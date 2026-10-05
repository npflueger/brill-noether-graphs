#!/usr/bin/env bash
# Build every Lean library of this repository and report greenness honestly.
#
# Why this exists.  "Green" should mean every library builds with no errors,
# no proved library contains a `sorry`, and the import layering between the
# libraries holds -- and that claim should rest on captured build logs, not on
# whichever targets someone happened to build that day.  The CI workflow in
# `.github/workflows/lean_action_ci.yml` builds a hand-maintained list of
# targets; this script instead reads the `[[lean_lib]]` entries of
# `lakefile.toml`, so a newly added library cannot be skipped.
#
# Two disciplines are baked in:
#
#   * greenness is read from a CAPTURED LOG, never from a pipeline exit code
#     -- `lake build ... | tail` reports tail's status, which is always 0;
#   * both streams are captured, because Lean and Lake can write diagnostics to
#     stderr.
#
# What it does:
#
#   1. builds each target into its own log and prints a table of errors,
#      warnings and infos per target (with the first errors, and the first
#      warnings, of any target that has them);
#   2. counts `sorry` in code (comments and string literals are ignored) per
#      top-level folder or root file.  The statement-only files --
#      `HighlightsStatements.lean`, `TwiceMarkedBananasStatements.lean` and
#      `Palomar/*/Challenge.lean` -- are deliberately stated with `sorry`
#      bodies and are listed separately; anywhere else a `sorry` is a failure;
#   3. runs `scripts/check_layering.py` (import arrows and root coverage).
#   4. checks module headers in project Lean sources.
#
# Usage:  bash scripts/check_build.sh [target ...]
#         (no arguments = every `[[lean_lib]]` of lakefile.toml)
#
#         LEAN_NUM_THREADS=2 bash scripts/check_build.sh   # throttle
#
# Lake has no job-count flag; `LEAN_NUM_THREADS` (default 4 here) throttles
# both the number of concurrent Lean workers and their internal parallelism.
# On a cold cache, run `lake exe cache get` first so Mathlib is downloaded
# rather than compiled.
#
# Exit status is 0 only if every target built with no errors, no proved
# library contains a `sorry`, and the layering check passed.
set -u
# In particular, a failed layering check must not be hidden by the final sed.
set -o pipefail

cd "$(dirname "$0")/.." || exit 2
LOGDIR="${TMPDIR:-/tmp}/bng-check-build.$$"
mkdir -p "$LOGDIR" || exit 2

: "${LEAN_NUM_THREADS:=4}"
export LEAN_NUM_THREADS

# The library names of lakefile.toml, one per line, in file order.
lakefile_libs() {
    python3 - <<'PY'
import re
text = open('lakefile.toml', encoding='utf-8').read()
try:
    import tomllib
    names = [lib['name'] for lib in tomllib.loads(text).get('lean_lib', [])]
except ImportError:  # Python < 3.11
    names = re.findall(r'^\[\[lean_lib\]\]\s*\n\s*name\s*=\s*"([^"]+)"', text, re.M)
print('\n'.join(names))
PY
}

TARGETS=()
if [ $# -gt 0 ]; then
    TARGETS=("$@")
else
    while IFS= read -r lib; do
        [ -n "$lib" ] && TARGETS+=("$lib")
    done < <(lakefile_libs)
fi
if [ ${#TARGETS[@]} -eq 0 ]; then
    echo "no targets: could not read any [[lean_lib]] from lakefile.toml" >&2
    exit 2
fi

fail=0
echo "LEAN_NUM_THREADS=$LEAN_NUM_THREADS; logs in $LOGDIR"
echo
printf '%-30s %8s %8s %8s %8s\n' target errors warnings infos result
printf '%s\n' "----------------------------------------------------------------------"

for t in "${TARGETS[@]}"; do
    log="$LOGDIR/$t.log"
    # Both streams; the exit code is recorded but never trusted on its own.
    lake build "$t" > "$log" 2>&1
    code=$?
    e=$(grep -c '^error:' "$log")
    w=$(grep -c '^warning:' "$log")
    i=$(grep -c '^info:' "$log")
    if [ "$e" -eq 0 ] && [ "$code" -eq 0 ]; then
        res=green
    else
        res=FAILED
        fail=1
    fi
    printf '%-30s %8s %8s %8s %8s\n' "$t" "$e" "$w" "$i" "$res"
    if [ "$res" = FAILED ]; then
        echo "    first errors:"
        grep '^error:' "$log" | head -5 | sed 's/^/      /'
        echo "    full log: $log"
    elif [ "$w" -gt 0 ]; then
        echo "    first warnings:"
        grep '^warning:' "$log" | head -5 | sed 's/^/      /'
        echo "    full log: $log"
    fi
done

echo
echo "sorries (in code; comments and strings ignored):"
python3 - <<'PY' || fail=1
import os, re, sys

def is_statement_hole(path):
    parts = path.split(os.sep)
    return (path in ('HighlightsStatements.lean', 'TwiceMarkedBananasStatements.lean')
            or (len(parts) == 3 and parts[0] == 'Palomar' and parts[2] == 'Challenge.lean'))

# In code: comment and string openers, character literals (so that `'"'`
# opens no string), newlines, and `sorry` as a whole token.
CODE = re.compile(r"""/-|--[^\n]*|"|'(?:\\.|[^\\'\n])'|\n|(?<![\w'.])sorry(?![\w'!?])""")
BLOCK = re.compile(r'/-|-/|\n')      # inside a (nestable) block comment
STRING = re.compile(r'\\.|"|\n', re.S)  # inside a string literal

def code_sorries(text):
    """Line numbers of `sorry` tokens outside comments and string literals."""
    out, i, line, depth, in_str = [], 0, 1, 0, False
    while True:
        m = (BLOCK if depth else STRING if in_str else CODE).search(text, i)
        if m is None:
            return out
        tok, i = m.group(0), m.end()
        line += tok.count('\n')
        if depth:
            depth += {'/-': 1, '-/': -1}.get(tok, 0)
        elif in_str:
            in_str = tok != '"'
        elif tok == '/-':
            depth = 1
        elif tok == '"':
            in_str = True
        elif tok == 'sorry':
            out.append(line)

proved, holes, where = {}, {}, []
for root, dirs, files in os.walk('.'):
    dirs[:] = sorted(d for d in dirs if not d.startswith('.'))
    for f in sorted(files):
        if not f.endswith('.lean'):
            continue
        path = os.path.normpath(os.path.join(root, f))
        lines = code_sorries(open(path, encoding='utf-8', errors='replace').read())
        if is_statement_hole(path):
            holes[path] = len(lines)
            continue
        key = path.split(os.sep)[0] + ('/' if os.sep in path else '')
        proved[key] = proved.get(key, 0) + len(lines)
        where += [f'{path}:{l}' for l in lines]

print('  proved libraries (any sorry is a failure):')
for key in sorted(proved):
    print(f'    {key:<40} {proved[key]:>5}')
print('  deliberate statement holes:')
for key in sorted(holes):
    print(f'    {key:<40} {holes[key]:>5}')
if where:
    print('  sorry in a proved library:')
    for w in where:
        print(f'    {w}')
    sys.exit(1)
PY

echo
echo "layering:"
python3 scripts/check_layering.py 2>&1 | sed 's/^/  /' || fail=1

echo
echo "module headers:"
python3 - <<'PY_MODULES' 2>&1 | sed 's/^/  /' || fail=1
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path.cwd()


def first_command(text):
    """Skip whitespace and nested leading comments before the module header."""
    depth = 0
    while text:
        text = text.lstrip()
        if depth:
            match = re.search(r"/-|-/", text)
            if match is None:
                return ""
            depth += 1 if match[0] == "/-" else -1
            text = text[match.end():]
        elif text.startswith("/-"):
            depth = 1
            text = text[2:]
        elif text.startswith("--"):
            text = text.partition("\n")[2]
        else:
            return text.splitlines()[0]
    return ""


def main():
    result = subprocess.run(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--", "*.lean"],
        cwd=ROOT, check=True, capture_output=True,
    )
    paths = sorted(set(p.decode() for p in result.stdout.split(b"\0") if p))
    invalid = [p for p in paths if first_command((ROOT / p).read_text()) != "module"]
    for path in invalid:
        print(f"missing module header: {path}")
    print(f"Module headers: {len(paths) - len(invalid)}/{len(paths)}")
    return bool(invalid)


if __name__ == "__main__":
    sys.exit(main())
PY_MODULES

echo
if [ "$fail" -eq 0 ]; then
    echo "ALL TARGETS GREEN"
else
    echo "SOME CHECKS FAILED -- see above (logs in $LOGDIR)"
fi
exit "$fail"
