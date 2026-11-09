#!/usr/bin/env python3
"""CI backstop for metel-core#1799: the compiler must not identify the std `Copy` aspect by its spelling.

`Copy` is recognised through its declaration identity (`TypeDefinitionRegistry::is_copy_aspect`,
`copy_aspect_id`, `type_is_copy`, `infer_type_is_copy`), so an unrelated user aspect that shares the
spelling is not mistaken for it and aspect properties (RFC-0212) can later be read from the declaration.
The one place the spelling is written is `COPY_ASPECT` in `type_engine/mod.rs`.

This scans non-test frontend and interpreter source for the exact string literal `"Copy"`. Diagnostic
text is not matched, because it is never exactly that literal. A site that must compare by spelling is
exempted with a trailing or immediately preceding `// copy-by-name-allow: <reason>` comment. Code after
a `#[cfg(test)]` line, `tests.rs` files and `tests/` directories are skipped.

Usage:
  tools/check_no_copy_by_name.py          # print findings
  tools/check_no_copy_by_name.py --check  # CI gate: fail on any unexempted finding
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SCAN_DIRS = [
    REPO_ROOT / "metel-frontend" / "src",
    REPO_ROOT / "metel-interpreter" / "src",
]
DEFINITION = (
    REPO_ROOT / "metel-frontend/src/pipeline/type_checking/type_engine/mod.rs",
    "pub const COPY_ASPECT",
)
LITERAL = '"Copy"'
ALLOW = "copy-by-name-allow:"


def is_test_path(path: Path) -> bool:
    return path.name == "tests.rs" or "tests" in path.parts


def findings_in(text: str, path: Path) -> list[int]:
    found = []
    lines = text.splitlines()
    for number, line in enumerate(lines, start=1):
        if "#[cfg(test)]" in line:
            break
        if LITERAL not in line:
            continue
        if path == DEFINITION[0] and DEFINITION[1] in line:
            continue
        previous = lines[number - 2] if number >= 2 else ""
        if ALLOW in line or ALLOW in previous:
            continue
        found.append(number)
    return found


def scan() -> list[tuple[Path, int]]:
    out = []
    for root in SCAN_DIRS:
        for path in sorted(root.rglob("*.rs")):
            if is_test_path(path):
                continue
            for number in findings_in(path.read_text(encoding="utf-8"), path):
                out.append((path, number))
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true", help="exit 1 on any finding")
    args = parser.parse_args()
    findings = scan()
    for path, number in findings:
        print(f"{path.relative_to(REPO_ROOT)}:{number}: the `Copy` aspect is identified by spelling; "
              "use TypeDefinitionRegistry::is_copy_aspect / type_is_copy / copy_aspect_id")
    if findings:
        print(f"{len(findings)} finding(s)")
        return 1 if args.check else 0
    print("check_no_copy_by_name: ok (no Copy compared by spelling).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
