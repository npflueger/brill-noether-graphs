#!/usr/bin/env python3
"""Check that submitted Lean sources opt in to Lean's module system.

Checks tracked files and genuine untracked Lean sources; ignores Git-ignored scratch files and Lake build artifacts.
"""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent


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
