#!/usr/bin/env python3
"""Run the executable reproductions of the active gap/limitation records against the interpreter.

A record's reproduction is a fenced Metel block whose info string carries the result it must
produce today:

    ```metel repro=T0002        the program is rejected with diagnostic T0002
    ```metel repro=ok           the program runs to completion

A limitation record says "this fails (or misbehaves) today". Prose cannot notice that it stopped
being true; this can. When a reproduction no longer gives its recorded result the limitation was
fixed, or changed shape, and the record is stale: resolve it, or update its reproduction. That is
how LIMIT-TYPE-INFERENCE-003 and LIMIT-COHERENCE-001 sat in the corpus, known and wrong, until an
audit ran their examples by hand (2026-11).

Only active records are run (`known`, `accepted`, `mitigated`, `planned`): a `resolved` or
`superseded` record may keep its old example as history. A reproduction is one self-contained
source file; a limitation that needs several modules has no executable reproduction.

A mismatch is a `warning:` and the exit status stays 0, because the record lives in metel-docs and
the fix that makes it stale lives here: a core pull request cannot resolve the record in the same
change (see the resolved-record ordering in docs/architecture/PROCESS.md). `--strict`, which
`/cut-release` runs, turns warnings into failures. A malformed `repro=` value is always an error.

    tools/check_record_repros.py [--metel target/release/metel] [--strict] [--suggest]

`--suggest` lists the Metel fences in active records that carry no `repro=` yet, with what the
interpreter does with each, to help annotate them.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RECORD_DIRS = ("docs/architecture/limitations", "docs/architecture/gaps")
ACTIVE = {"known", "accepted", "mitigated", "planned"}
FENCE_RE = re.compile(r"^```metel([^\n]*)\n(.*?)^```[ \t]*$", re.MULTILINE | re.DOTALL)
REPRO_RE = re.compile(r"\brepro=(\S*)")
EXPECT_RE = re.compile(r"^(?:ok|[A-Z]\d{4})$")
DIAG_RE = re.compile(r"\[([A-Z]\d{4})\]")
TIMEOUT_SECONDS = 20


@dataclass
class Repro:
    record: str
    path: Path
    source: str
    expect: str | None  # None: the fence has no repro= attribute


def frontmatter_field(text: str, key: str) -> str:
    m = re.search(rf"^{key}:\s*(.*?)\s*$", text, re.MULTILINE)
    return m.group(1).strip("\"'") if m else ""


def collect(root: Path = ROOT) -> tuple[list[Repro], list[str], int]:
    """(reproductions of active records, errors, number of active records)."""
    repros: list[Repro] = []
    errors: list[str] = []
    active = 0
    for rel in RECORD_DIRS:
        for path in sorted((root / rel).glob("*.md")) if (root / rel).is_dir() else []:
            text = path.read_text()
            if frontmatter_field(text, "disposition") not in ACTIVE:
                continue
            active += 1
            record = frontmatter_field(text, "id") or path.stem
            for m in FENCE_RE.finditer(text):
                attr = REPRO_RE.search(m.group(1))
                if attr and not EXPECT_RE.match(attr.group(1)):
                    errors.append(f"{record}: `repro={attr.group(1)}` must be `ok` or a diagnostic code like `T0002`")
                    continue
                repros.append(Repro(record, path, m.group(2), attr.group(1) if attr else None))
    return repros, errors, active


def run(metel: Path, source: str) -> str:
    """What the interpreter does with `source`: `ok`, a diagnostic code, or a short failure note."""
    with tempfile.TemporaryDirectory() as td:
        file = Path(td) / "repro.mtl"
        file.write_text(source)
        try:
            out = subprocess.run([str(metel), str(file)], capture_output=True, text=True, timeout=TIMEOUT_SECONDS)
        except subprocess.TimeoutExpired:
            return "timeout"
    if out.returncode == 0:
        return "ok"
    m = DIAG_RE.search(out.stderr + out.stdout)
    return m.group(1) if m else f"exit {out.returncode} with no diagnostic code"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--metel", type=Path, default=ROOT / "target" / "release" / "metel")
    ap.add_argument("--root", type=Path, default=ROOT)
    ap.add_argument("--strict", action="store_true", help="a stale reproduction fails (a release)")
    ap.add_argument("--suggest", action="store_true", help="show what un-annotated Metel fences do today")
    args = ap.parse_args()

    repros, errors, active = collect(args.root)
    if not args.metel.is_file():
        print(f"error: interpreter not found at {args.metel} (build it: cargo build --release -p metel)")
        return 2

    if args.suggest:
        for r in repros:
            if r.expect is None:
                print(f"{r.record}: {run(args.metel, r.source)}   ({r.path.relative_to(args.root)})")
        return 0

    stale: list[str] = []
    checked = 0
    for r in repros:
        if r.expect is None:
            continue
        checked += 1
        got = run(args.metel, r.source)
        if got != r.expect:
            stale.append(
                f"{r.record}: its reproduction is recorded as `repro={r.expect}` but now gives `{got}`; "
                "the limitation was fixed or changed shape: resolve the record, or update the reproduction"
            )
    with_repro = {r.record for r in repros if r.expect is not None}
    print(f"record reproductions: {checked} run for {len(with_repro)} of {active} active records; {len(stale)} stale")
    for e in errors:
        print(f"error: {e}")
    for s in stale:
        print(f"warning: {s}")
    if errors or (stale and args.strict):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
