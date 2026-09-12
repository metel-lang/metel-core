#!/usr/bin/env python3
"""CI backstop for ADR-0054 step 9 / metel-core#1054: the frozen IR's public
types and the durable `ResolutionMap` must not carry `String` or `Span` in a
map-key position -- a *structural* guarantee, not a lint, so a post-freeze
semantic name lookup does not typecheck. This script is the backstop against
new escape hatches the ADR calls for, not the primary defence: the primary
defence is that these types simply have no such field today.

Scans a curated list of files holding the frozen IR / resolution-map types
(SCAN_FILES below) for a `HashMap<..>` / `BTreeMap<..>` field whose key type
mentions `String` or `Span` anywhere (covers a bare key and a container of one,
e.g. `Vec<String>`). A field is exempted with an inline
`// resolution-freeze-allow: <reason>` comment, trailing the field or on the
line (or contiguous comment block) immediately above it -- the same convention
`clippy_allow_ratchet.py` uses for `clippy-allow:`. Every exemption must
justify itself in the comment, so a reviewer can ask whether it still holds.

Deliberately NOT scanned:
- `identity::position` (`PositionIndex` and friends) -- ADR-0054's own
  sanctioned exception, the only *position*-keyed structure allowed to exist
  (rebuilt fresh per snapshot, never a durable/frozen artifact).
- The evaluator's runtime registries (`RuntimeRegistry` and friends) -- a
  separate, adjacent concern with its own nuances (e.g. a method name is
  unique within one receiver type, a std::core builtin name within that one
  fixed module); not yet brought under this check. Extend SCAN_FILES to bring
  a file under it once its exemptions have been reviewed the same way.

Usage:
  tools/check_no_semantic_name_lookup.py          # print findings
  tools/check_no_semantic_name_lookup.py --check  # CI gate: fail on any unexempted finding
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# The frozen IR / durable resolution-map types. Add a file here once its
# String/Span-keyed fields have been reviewed and exempted (or removed).
SCAN_FILES = [
    REPO_ROOT / "metel-frontend" / "src" / "identity.rs",
    REPO_ROOT / "metel-frontend" / "src" / "typed_ast" / "mod.rs",
    REPO_ROOT / "metel-frontend" / "src" / "place.rs",
    REPO_ROOT / "metel-frontend" / "src" / "query.rs",
]

MAP_RE = re.compile(r"\b(?:HashMap|BTreeMap)\s*<")
KEY_TOKEN_RE = re.compile(r"\b(String|Span)\b")
JUSTIFY_TOKEN = "resolution-freeze-allow:"


def rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def _extract_key_type(text: str, open_idx: int) -> str | None:
    """`text[open_idx]` is the `<` right after `HashMap`/`BTreeMap`. Return the
    key type's source text (up to the top-level comma that separates it from
    the value type), or `None` if the generic never closes on this line (a
    map type split across lines -- not seen in the current scan targets; a
    field like that would need reformatting or this function extending)."""
    depth_angle = 1
    depth_paren = 0
    i = open_idx + 1
    start = i
    while i < len(text):
        c = text[i]
        if c == "<":
            depth_angle += 1
        elif c == ">":
            depth_angle -= 1
            if depth_angle == 0:
                return text[start:i]
        elif c == "(":
            depth_paren += 1
        elif c == ")":
            depth_paren -= 1
        elif c == "," and depth_angle == 1 and depth_paren == 0:
            return text[start:i]
        i += 1
    return None


def _comment_of(text: str) -> str:
    idx = text.find("//")
    return text[idx:] if idx != -1 else ""


def _comment_block_above(lines: list[str], i: int) -> str:
    """Text of the contiguous `//` comment block ending on the line above `i`,
    walking up over interleaved attributes too (mirrors
    clippy_allow_ratchet.py's helper of the same name)."""
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


def scan() -> list[tuple[str, int, str, str]]:
    """Return a list of (relpath, line_no (1-based), line_text, key_type) for
    every unexempted String/Span-keyed HashMap/BTreeMap field found."""
    findings = []
    for path in SCAN_FILES:
        if not path.exists():
            continue
        relpath = rel(path)
        lines = path.read_text().splitlines()
        for i, line in enumerate(lines):
            m = MAP_RE.search(line)
            if not m:
                continue
            key_type = _extract_key_type(line, m.end() - 1)
            if key_type is None or not KEY_TOKEN_RE.search(key_type):
                continue
            justified = JUSTIFY_TOKEN in _comment_of(line[m.end():]) or (
                JUSTIFY_TOKEN in _comment_block_above(lines, i)
            )
            if justified:
                continue
            findings.append((relpath, i + 1, line.strip(), key_type.strip()))
    return findings


def cmd_check(_args) -> int:
    findings = scan()
    if findings:
        print("check_no_semantic_name_lookup: FAIL\n")
        for relpath, lineno, text, key_type in findings:
            print(f"  {relpath}:{lineno}: key type `{key_type}` mentions String/Span")
            print(f"      {text}")
        print(
            "\nA field here is part of the frozen IR or the durable ResolutionMap "
            "(ADR-0054 step 9 / metel-core#1054): it must not resolve program "
            "meaning by a String/Span key. If this one genuinely can't collide "
            "(e.g. scoped to one module/type where the name is already unique), "
            "justify it with a `// resolution-freeze-allow: <reason>` comment "
            "trailing the field or on the line above."
        )
        return 1
    print("check_no_semantic_name_lookup: ok (no unexempted String/Span-keyed "
          "map in the frozen IR / ResolutionMap).")
    return 0


def cmd_list(_args) -> int:
    findings = scan()
    if not findings:
        print("No unexempted String/Span-keyed map found in the scanned files.")
        return 0
    for relpath, lineno, text, key_type in findings:
        print(f"{relpath}:{lineno}\tkey={key_type}\t{text}")
    return 0


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--check", action="store_true", help="CI gate: fail on any unexempted finding")
    args = p.parse_args()
    return cmd_check(args) if args.check else cmd_list(args)


if __name__ == "__main__":
    sys.exit(main())
