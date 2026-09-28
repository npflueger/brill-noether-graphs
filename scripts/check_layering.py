#!/usr/bin/env python3
"""Layering and root-coverage guardrail for this repository.

Why this exists.  The libraries here form a stack: `Utilities` at the bottom,
imported by everything, and application libraries on top of it that must not
import each other except along the arrows listed below.  Nothing in Lake
enforces those arrows, and a stray import compiles fine: it only shows up
later, as a library that can no longer be built, audited or reused without
dragging in another one.  Likewise, `lake build X` builds only what the root
module `X.lean` reaches, so a module that no root imports is silently never
compiled.  This script checks both properties from the source tree alone,
without building anything.

Usage:  python3 scripts/check_layering.py
        (run from anywhere; it works relative to the repository root)

Exit status 0 prints "layering OK"; exit status 1 prints one line per
violation.  `scripts/check_build.sh` runs it as part of the full gate.

What is checked.

1. Import arrows, by the first component of each imported module.  Only the
   import header of each file is read (up to the first line that is neither
   an import, blank, nor a comment).  A library may always import itself.

   * Externals (always allowed): EXTERNALS below.
   * `Utilities/`: externals only.
   * `Bananas/`, `TwiceMarkedBananas.lean`: `Utilities`, `Bananas`.
   * `LowGenus/`, `TreewidthGonality/`, `Tricycle/`: `Utilities`.
   * Libraries that are planned but not yet present (the rules are harmless
     while they are absent): `DraismaVargas/`: `Utilities`, `LowGenus`;
     `DraismaVargasCount/`: those plus `DraismaVargas`; `GenusSixOddDescent/`:
     `Utilities`; `GenusSixExistence/`: `Utilities`, `LowGenus`,
     `DraismaVargas`, `DraismaVargasCount`, `GenusSixOddDescent`.
   * Statement-only files -- `HighlightsStatements.lean`,
     `TwiceMarkedBananasStatements.lean`, and everything under `Palomar/`
     except `Palomar/Solutions/` (in particular every `Palomar/*/Challenge.lean`)
     -- import externals only, so that they can be audited against Mathlib
     alone.
   * Reader-facing files -- `Highlights.lean`, any `*/Highlights.lean`, and
     `Palomar/Solutions/` -- may import any library of this repository.
   * `Research/` holds standalone audit scripts that belong to no library; they
     may import any library of this repository.
   * An import that is neither external nor a library of this repository, and a
     `.lean` file that no rule covers, are violations: a new top-level folder
     needs a rule here.

2. Root closure.  Each library root may reach, transitively, only modules of
   the libraries its own rule allows.  This matters for `*/Highlights.lean`:
   such a file may import any library, but if its library root imports it, the
   whole library acquires those dependencies.

3. Root coverage.  Each library root `X.lean` with a folder `X/` must
   transitively import every module under `X/`, apart from the explicit
   allowlist DELIBERATELY_UNREACHABLE below.
"""
import os
import re
import sys

try:
    import tomllib
except ImportError:  # Python < 3.11
    tomllib = None

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
os.chdir(ROOT)

EXTERNALS = {
    'Mathlib', 'Lean', 'Init', 'Std', 'Batteries', 'Aesop', 'Qq', 'Plausible',
    'ChipFiringWithLean', 'Demazure',
}

# Allowed first components for each library, keyed by its top-level folder
# (equivalently, its root file `X.lean`).  The library itself is always allowed.
LIBRARY_RULES = {
    'Utilities': set(),
    'Bananas': {'Utilities'},
    'TwiceMarkedBananas': {'Utilities', 'Bananas'},
    'LowGenus': {'Utilities'},
    'TreewidthGonality': {'Utilities'},
    'Tricycle': {'Utilities'},
    # Planned libraries; harmless while absent.
    'DraismaVargas': {'Utilities', 'LowGenus'},
    'DraismaVargasCount': {'Utilities', 'LowGenus', 'DraismaVargas'},
    'GenusSixOddDescent': {'Utilities'},
    'GenusSixExistence': {'Utilities', 'LowGenus', 'DraismaVargas',
                          'DraismaVargasCount', 'GenusSixOddDescent'},
}

STATEMENT_ONLY_FILES = {'HighlightsStatements.lean', 'TwiceMarkedBananasStatements.lean'}

# Modules under a library folder that its root does not reach.  This is the
# exact list at the time the check was introduced; every entry needs a reason,
# any other unreachable module is a violation, and an entry that becomes
# reachable or disappears must be removed (the script reports it as stale).
DELIBERATELY_UNREACHABLE = {
    # The fifteen generated cover modules named in the `LowGenus.lean`
    # docstring -- `GenusFiveRow03FixedCover`, `GenusFiveRow14FixedCover`, the
    # five-module row-04 chain and the eight-module row-06 chain -- kept as
    # independent generated checks alongside the readable proofs, and
    # `GenusFiveClosedCover`, the affine-cover semantics only they use.
    'LowGenus.GenusFiveClosedCover',
    'LowGenus.GenusFiveRow03FixedCover',
    'LowGenus.GenusFiveRow04CoverBase',
    'LowGenus.GenusFiveRow04CoverCells0',
    'LowGenus.GenusFiveRow04CoverCells1',
    'LowGenus.GenusFiveRow04FixedCover',
    'LowGenus.GenusFiveRow04Symmetry',
    'LowGenus.GenusFiveRow06CoverBase',
    'LowGenus.GenusFiveRow06CoverCells0',
    'LowGenus.GenusFiveRow06CoverCells1',
    'LowGenus.GenusFiveRow06CoverCells2',
    'LowGenus.GenusFiveRow06CoverCells3',
    'LowGenus.GenusFiveRow06CoverCells4',
    'LowGenus.GenusFiveRow06FixedCover',
    'LowGenus.GenusFiveRow06Symmetry',
    'LowGenus.GenusFiveRow14FixedCover',
}


def lean_libs():
    """The `[[lean_lib]]` entries of `lakefile.toml`, as (name, srcDir, roots)."""
    text = open('lakefile.toml', encoding='utf-8').read()
    if tomllib is not None:
        libs = tomllib.loads(text).get('lean_lib', [])
        return [(lib['name'], lib.get('srcDir', '.'), lib.get('roots', [lib['name']]))
                for lib in libs]
    # Minimal fallback: `name`, `srcDir` and `roots` inside `[[lean_lib]]` blocks.
    out = []
    for block in re.split(r'^\[\[', text, flags=re.M)[1:]:
        if not block.startswith('lean_lib]]'):
            continue
        name = re.search(r'^name\s*=\s*"([^"]+)"', block, re.M).group(1)
        src = re.search(r'^srcDir\s*=\s*"([^"]+)"', block, re.M)
        roots = re.search(r'^roots\s*=\s*\[([^\]]*)\]', block, re.M)
        out.append((name, src.group(1) if src else '.',
                    re.findall(r'"([^"]+)"', roots.group(1)) if roots else [name]))
    return out


def lean_files():
    """Every `.lean` file of the repository, outside `.lake` and hidden folders."""
    out = []
    for root, dirs, files in os.walk('.'):
        dirs[:] = sorted(d for d in dirs if not d.startswith('.'))
        for f in sorted(files):
            if f.endswith('.lean'):
                out.append(os.path.normpath(os.path.join(root, f)))
    return out


def imports_of(path):
    """Modules imported by the header of `path`."""
    out = []
    depth = 0  # nesting depth of an open `/- ... -/` comment
    for line in open(path, encoding='utf-8', errors='replace'):
        rest = line
        while True:
            if depth > 0:
                m = re.search(r'/-|-/', rest)
                if not m:
                    rest = ''
                    break
                depth += 1 if m.group(0) == '/-' else -1
                rest = rest[m.end():]
                continue
            rest = rest.strip()
            if rest.startswith('/-') and not rest.startswith(('/-!', '/--')):
                depth = 1
                rest = rest[2:]
                continue
            break
        if depth > 0 or rest == '' or rest.startswith('--'):
            continue
        tokens = rest.split('--', 1)[0].split()
        while tokens and tokens[0] in ('public', 'private', 'meta'):
            tokens = tokens[1:]
        if tokens and tokens[0] in ('module', 'prelude') and len(tokens) == 1:
            continue
        if not tokens or tokens[0] != 'import':
            break
        out.extend(t for t in tokens[1:] if t != 'all')
    return out


def top_key(path):
    """The top-level folder of `path`, or the stem of a top-level file."""
    first = path.split(os.sep)[0]
    return first[:-len('.lean')] if first.endswith('.lean') else first


def main():
    violations = []
    libs = lean_libs()

    # Module name <-> file, for every library of the lakefile; the first
    # component of each root names an in-repository library.
    in_repo = set(LIBRARY_RULES)
    for name, src, roots in libs:
        in_repo.update(r.split('.')[0] for r in roots)
    src_of = {r.split('.')[0]: src for _, src, roots in libs for r in roots}

    def module_path(module):
        src = src_of.get(module.split('.')[0], '.')
        return os.path.normpath(os.path.join(src, *module.split('.')) + '.lean')

    def module_name(path):
        for first, src in src_of.items():
            prefix = '' if src == '.' else os.path.normpath(src) + os.sep
            rel = path[len(prefix):] if path.startswith(prefix) else None
            if rel is not None and rel.split(os.sep)[0] in (first, first + '.lean'):
                return rel[:-len('.lean')].replace(os.sep, '.')
        return path[:-len('.lean')].replace(os.sep, '.')

    ANY = in_repo

    def allowed_for(path):
        """(label, allowed first components) for `path`, or None if no rule."""
        parts = path.split(os.sep)
        if path in STATEMENT_ONLY_FILES:
            return 'statement-only', set()
        if parts[0] == 'Palomar':
            if len(parts) > 1 and parts[1] == 'Solutions':
                return 'reader-facing', ANY
            return 'statement-only', set()
        if parts[-1] == 'Highlights.lean':
            return 'reader-facing', ANY
        if parts[0] == 'Research':
            return 'research', ANY
        key = top_key(path)
        if key in LIBRARY_RULES:
            return key, LIBRARY_RULES[key] | {key}
        return None

    files = lean_files()
    headers = {p: imports_of(p) for p in files}

    # 1. Import arrows.
    for path in files:
        rule = allowed_for(path)
        if rule is None:
            violations.append(f'no-rule: {path} is covered by no layering rule '
                              '(add one to scripts/check_layering.py)')
            continue
        label, allowed = rule
        for imp in headers[path]:
            first = imp.split('.')[0]
            if first in EXTERNALS or first in allowed:
                continue
            if first not in in_repo:
                violations.append(f'{label}: {path} imports {imp}, which is neither '
                                  'external nor a library of this repository')
            else:
                violations.append(f'{label}: {path} imports {imp}')

    # Transitive closure over in-repository modules that exist on disk, with
    # the import edges used to reach them.
    def closure_edges(module):
        seen, edges, stack = set(), [], [module]
        while stack:
            m = stack.pop()
            if m in seen:
                continue
            path = module_path(m)
            if not os.path.isfile(path):
                continue
            seen.add(m)
            for i in headers.get(path, imports_of(path)):
                if i.split('.')[0] in in_repo:
                    edges.append((path, i))
                    if i not in seen:
                        stack.append(i)
        return seen, edges

    def closure(module):
        return closure_edges(module)[0]

    for key, rule in sorted(LIBRARY_RULES.items()):
        root_file = key + '.lean'
        if not os.path.isfile(root_file):
            continue
        reach, edges = closure_edges(key)

        # 2. Root closure: report each import that leaves the allowed libraries
        # from a module that is itself inside them.
        allowed = rule | {key}
        for path, imp in sorted(set(edges)):
            if (imp.split('.')[0] not in allowed
                    and module_name(path).split('.')[0] in allowed):
                violations.append(f'root-closure: {root_file} reaches {imp} through '
                                  f'{path}, outside the libraries {sorted(allowed)} '
                                  'it may use')

        # 3. Root coverage.
        if not os.path.isdir(key):
            continue
        for path in files:
            if path.split(os.sep)[0] != key:
                continue
            m = module_name(path)
            if m not in reach and m not in DELIBERATELY_UNREACHABLE:
                violations.append(f'root-coverage: {path} is not reachable from '
                                  f'{root_file}')

    # An allowlist entry that is now reachable, or gone, is stale.
    for m in sorted(DELIBERATELY_UNREACHABLE):
        key = m.split('.')[0]
        if not os.path.isfile(module_path(m)):
            violations.append(f'stale-allowlist: {m} no longer exists')
        elif os.path.isfile(key + '.lean') and m in closure(key):
            violations.append(f'stale-allowlist: {m} is now reachable from '
                              f'{key}.lean')

    if violations:
        print('\n'.join(violations))
        return 1
    print('layering OK')
    return 0


if __name__ == '__main__':
    sys.exit(main())
