#!/usr/bin/env python3
"""Ratchet Clippy suppressions so new `#[allow(clippy::...)]` directives can't
accumulate silently (metel-core#882).

The project carries a stock of `#[allow(clippy::...)]` from before this check
existed. Rather than block on a large cleanup PR, those are *baselined*:
`tools/clippy-allow-baseline.json` records, per (file, lint), how many bare
(unjustified) allows are grandfathered in, plus which files carry a module-level
`#![allow(clippy::...)]`. New code then has to either fix the warning, or justify
the suppression with a `// clippy-allow: <reason>` comment (which is never
counted), rather than adding a bare allow.

This is the same grandfathered-baseline shape `rfc.py`'s COVERAGE-BASELINE.json
uses, and it rides the "policy checker in CI" slot of the other tools/check_*.py scripts.

A suppression counts as **justified** when the token `clippy-allow:` appears in a
`//` comment either trailing the attribute line or on the line immediately above
it. Anything else is **bare**.

Usage:
  tools/clippy_allow_ratchet.py                 # or --list: print the inventory
  tools/clippy_allow_ratchet.py --check         # CI gate: fail on new bare allows
  tools/clippy_allow_ratchet.py --write-baseline  # regenerate the baseline file
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BASELINE_PATH = REPO_ROOT / "tools" / "clippy-allow-baseline.json"

# Library code only -- matches CI's `cargo clippy ... --lib` scoping; AGENTS.md
# holds test harnesses and measurement binaries to a looser bar.
SCAN_DIRS = [
    REPO_ROOT / "metel-frontend" / "src",
    REPO_ROOT / "metel-interpreter" / "src",
]

# `#[allow(clippy::a, clippy::b)]` / `#[expect(clippy::a)]`, and the inner
# `#![...]` (module-level) form. Captures the `!` and the parens' contents.
# One line at a time -- a suppression split across lines (rustfmt won't do this)
# is not matched, and would slip past the ratchet; add a fixup if one appears.
ALLOW_RE = re.compile(r"#(?P<bang>!?)\[(?:allow|expect)\((?P<body>[^)]*)\)\]")
CLIPPY_LINT_RE = re.compile(r"clippy::([a-z0-9_]+)")
JUSTIFY_TOKEN = "clippy-allow:"


def rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def scan():
    """Return (buckets, module_level) for the current tree.

    buckets: {relpath: {lint: bare_count}}          -- item-level bare allows
    module_level: {relpath: {"bare": [lints], "justified": [lints]}}
    """
    buckets: dict[str, dict[str, int]] = {}
    module_level: dict[str, dict[str, list[str]]] = {}

    for scan_dir in SCAN_DIRS:
        for rs in sorted(scan_dir.rglob("*.rs")):
            relpath = rel(rs)
            lines = rs.read_text().splitlines()
            for i, line in enumerate(lines):
                m = ALLOW_RE.search(line)
                if not m:
                    continue
                lints = CLIPPY_LINT_RE.findall(m.group("body"))
                if not lints:
                    continue  # a non-clippy allow, e.g. #[allow(dead_code)]

                justified = JUSTIFY_TOKEN in _comment_of(line[m.end():]) or (
                    JUSTIFY_TOKEN in _comment_block_above(lines, i)
                )

                if m.group("bang") == "!":
                    entry = module_level.setdefault(relpath, {"bare": [], "justified": []})
                    key = "justified" if justified else "bare"
                    for lint in lints:
                        if lint not in entry[key]:
                            entry[key].append(lint)
                    continue

                if justified:
                    continue  # justified item-level allows are never counted
                per_file = buckets.setdefault(relpath, {})
                for lint in lints:
                    per_file[lint] = per_file.get(lint, 0) + 1

    return buckets, module_level


def _comment_of(text: str) -> str:
    idx = text.find("//")
    return text[idx:] if idx != -1 else ""


def _comment_block_above(lines: list[str], i: int) -> str:
    """Text of the contiguous `//` comment block ending on the line above `i`.

    Walks up over consecutive comment lines (and any interleaved attributes, so a
    `#[inline]` between the justification and the `#[allow]` doesn't hide it),
    stopping at the first line that is neither.
    """
    out = []
    j = i - 1
    while j >= 0:
        stripped = lines[j].strip()
        if stripped.startswith("//"):
            out.append(stripped)
            j -= 1
        elif stripped.startswith("#["):
            j -= 1
        else:
            break
    return "\n".join(out)


def load_baseline() -> dict:
    if not BASELINE_PATH.exists():
        return {"buckets": {}, "module_level": {}}
    data = json.loads(BASELINE_PATH.read_text())
    data.setdefault("buckets", {})
    data.setdefault("module_level", {})
    return data


def cmd_write_baseline(_args) -> int:
    buckets, module_level = scan()
    ml_bare = {
        f: sorted(e["bare"]) for f, e in sorted(module_level.items()) if e["bare"]
    }
    payload = {
        "note": (
            "Grandfathered BARE #[allow(clippy::...)] counts per (file, lint), plus "
            "files carrying a module-level #![allow(clippy::...)]. A "
            "`// clippy-allow: <reason>` comment (trailing the attribute or on the "
            "line above) marks a suppression justified; justified suppressions are "
            "never counted here and never fail the check. New bare allows beyond "
            "these counts, and any new module-level #![allow(clippy::...)], fail "
            "tools/clippy_allow_ratchet.py --check in CI. Regenerate with "
            "tools/clippy_allow_ratchet.py --write-baseline after fixing a warning "
            "(to tighten the ratchet) or after deliberately grandfathering more."
        ),
        "buckets": {
            f: dict(sorted(lints.items()))
            for f, lints in sorted(buckets.items())
        },
        "module_level": ml_bare,
    }
    BASELINE_PATH.write_text(json.dumps(payload, indent=2) + "\n")
    total = sum(sum(v.values()) for v in buckets.values())
    print(f"wrote {rel(BASELINE_PATH)}: {total} bare allow(s) across "
          f"{len(payload['buckets'])} file(s); "
          f"{len(ml_bare)} file(s) with a module-level #![allow].")
    return 0


def cmd_list(_args) -> int:
    buckets, module_level = scan()
    by_lint: dict[str, list[tuple[str, int]]] = {}
    for f, lints in buckets.items():
        for lint, n in lints.items():
            by_lint.setdefault(lint, []).append((f, n))

    bare_total = 0
    print("Bare #[allow(clippy::...)] by lint (justified `// clippy-allow:` sites not shown):\n")
    for lint in sorted(by_lint):
        entries = sorted(by_lint[lint])
        sub = sum(n for _, n in entries)
        bare_total += sub
        print(f"  clippy::{lint}  ({sub})")
        for f, n in entries:
            print(f"      {n:>3}  {f}")
    print(f"\n  total bare: {bare_total}")

    if module_level:
        print("\nModule-level #![allow(clippy::...)]:")
        for f, e in sorted(module_level.items()):
            for lint in sorted(e["bare"]):
                print(f"      bare       clippy::{lint}  {f}")
            for lint in sorted(e["justified"]):
                print(f"      justified  clippy::{lint}  {f}")
    return 0


def cmd_check(_args) -> int:
    buckets, module_level = scan()
    base = load_baseline()
    base_buckets = base["buckets"]
    base_ml = base["module_level"]

    failures: list[str] = []
    improvements: list[str] = []

    for f, lints in sorted(buckets.items()):
        for lint, n in sorted(lints.items()):
            allowed = base_buckets.get(f, {}).get(lint, 0)
            if n > allowed:
                failures.append(
                    f"{f}: {n} bare #[allow(clippy::{lint})], baseline allows {allowed} "
                    f"(+{n - allowed}). Fix the warning, or add a "
                    f"`// clippy-allow: <reason>` comment above the attribute."
                )
            elif n < allowed:
                improvements.append(f"{f}: clippy::{lint} {allowed} -> {n}")

    for f, allowed in sorted(base_buckets.items()):
        for lint, allowed_n in sorted(allowed.items()):
            if buckets.get(f, {}).get(lint, 0) == 0 and allowed_n > 0:
                improvements.append(f"{f}: clippy::{lint} {allowed_n} -> 0")

    for f, e in sorted(module_level.items()):
        for lint in sorted(e["bare"]):
            if lint not in base_ml.get(f, []):
                failures.append(
                    f"{f}: new module-level #![allow(clippy::{lint})]. Module-level "
                    f"silencing is not grandfathered here -- scope it to the item, "
                    f"or add a `// clippy-allow: <reason>` comment."
                )

    for f, lints in sorted(base_ml.items()):
        remaining = set(module_level.get(f, {}).get("bare", []))
        for lint in sorted(set(lints) - remaining):
            improvements.append(f"{f}: module-level clippy::{lint} removed")

    if improvements:
        print("Suppressions reduced since the baseline "
              "(run --write-baseline to lock these in):")
        for line in improvements:
            print(f"  - {line}")
        print()

    if failures:
        print("clippy-allow ratchet: FAIL\n")
        for line in failures:
            print(f"  - {line}")
        print("\nSee AGENTS.md 'Clippy suppressions' and metel-core#882.")
        return 1

    print("clippy-allow ratchet: ok (no new bare or module-level clippy allows).")
    return 0


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--check", action="store_true", help="CI gate: fail on new bare allows")
    p.add_argument("--write-baseline", action="store_true", help="regenerate the baseline file")
    p.add_argument("--list", action="store_true", help="print the current inventory (default)")
    args = p.parse_args()

    if args.check and args.write_baseline:
        p.error("--check and --write-baseline are mutually exclusive")
    if args.write_baseline:
        return cmd_write_baseline(args)
    if args.check:
        return cmd_check(args)
    return cmd_list(args)


if __name__ == "__main__":
    sys.exit(main())
