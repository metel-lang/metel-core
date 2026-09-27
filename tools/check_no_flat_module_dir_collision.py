#!/usr/bin/env python3
"""Flag a `foo.rs` sitting beside a same-named `foo/` directory.

Rust resolves `foo.rs` + `foo/{bar.rs, ...}` and `foo/mod.rs` +
`foo/{bar.rs, ...}` identically: both nest `foo`'s children in `foo/`. But the
first shape reads as confusing at a glance -- a file and a directory sharing a
name look like a collision even though they aren't one -- and this project has
twice ended up there by accident rather than by choice (`identity.rs`
alongside `identity/`, `inference.rs` alongside `inference/`, both fixed by
metel-core#1272 by moving the file to `foo/mod.rs`). This is a structural
backstop against a third one, in the same "policy checker in CI" slot as
clippy_allow_ratchet.py / check_no_semantic_name_lookup.py.

`mod.rs`, `lib.rs`, and `main.rs` are exempt: they are already a directory's
(or crate's) own entry point, so the question this check asks -- "should this
sit inside the directory it names?" -- doesn't apply to them.

Usage:
  tools/check_no_flat_module_dir_collision.py          # print findings
  tools/check_no_flat_module_dir_collision.py --check  # CI gate: fail on any finding
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# Library source only. A crate's `tests/` directory is a different shape:
# Cargo requires a flat `tests/foo.rs` as an integration-test binary's own
# crate root, and a same-named `tests/foo/` alongside it holds files pulled in
# via `#[path = "foo/bar.rs"]`, not Rust's automatic module-folder nesting --
# so `tests/unit.rs` + `tests/unit/` isn't this pattern, and converting it
# (to `tests/unit/main.rs`) is a separate, Cargo-discovery-affecting decision
# this check doesn't make on its own.
SCAN_DIRS = [
    REPO_ROOT / "metel-frontend" / "src",
    REPO_ROOT / "metel-interpreter" / "src",
]

EXEMPT_STEMS = {"mod", "lib", "main"}


def rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def scan() -> list[tuple[Path, Path]]:
    """Return a list of (file, dir) pairs for every `foo.rs` with a sibling
    `foo/` directory."""
    findings = []
    for scan_dir in SCAN_DIRS:
        if not scan_dir.exists():
            continue
        for path in scan_dir.rglob("*.rs"):
            if path.stem in EXEMPT_STEMS:
                continue
            sibling_dir = path.with_suffix("")
            if sibling_dir.is_dir():
                findings.append((path, sibling_dir))
    return sorted(set(findings), key=lambda pair: str(pair[0]))


def cmd_check(_args) -> int:
    findings = scan()
    if findings:
        print("check_no_flat_module_dir_collision: FAIL\n")
        for file, directory in findings:
            print(f"  {rel(file)}  <->  {rel(directory)}/")
        print(
            "\nMove the file to `<name>/mod.rs` instead: same module tree, no "
            "file/directory name collision. See metel-core#1272."
        )
        return 1
    print("check_no_flat_module_dir_collision: ok (no foo.rs beside foo/).")
    return 0


def cmd_list(_args) -> int:
    findings = scan()
    if not findings:
        print("No foo.rs-beside-foo/ pair found in the scanned directories.")
        return 0
    for file, directory in findings:
        print(f"{rel(file)}\t<->\t{rel(directory)}/")
    return 0


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--check", action="store_true", help="CI gate: fail on any finding")
    args = p.parse_args()
    return cmd_check(args) if args.check else cmd_list(args)


if __name__ == "__main__":
    sys.exit(main())
