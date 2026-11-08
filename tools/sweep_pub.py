#!/usr/bin/env python3
"""One-shot sweep for RFC-0218 (metel-core#1849): the visibility keyword `public` becomes `pub`.

Not a blind regex (docs/rfcs/PROCESS.md, exit criterion of 2026-07-31). The rewrite works by token context:

- In Metel source (`.mtl` files and the contents of ```metel fences in Markdown) it rewrites the word `public` only
  in code. String literals (including `${...}` interpolation) and char literals are left alone, and so is any
  identifier that merely contains the word (`public_api`, `is_public`). Comments (`//` and `/* */`) are left alone
  except for inline code spans that name the keyword (`` `public` ``, `` `public fun` ``), which would go stale.
- In Markdown prose it rewrites an inline code span that is exactly `` `public` `` or that starts with `public`
  followed by a declaration keyword (`` `public fun` ``, `` `public struct Foo` ``). English prose, other fences
  (```rust, ```toml, ...) and untagged fences are never touched; untagged fences are reported.
- Line endings are preserved byte for byte (at least one docs file is CRLF).

Scope (RFC-0218 section 2). Swept: the stdlib and the fixture corpus, the spec, tutorials, live RFCs, architecture
reports and the blog. Left alone, and excluded by default: release notes, `5-superseded` and `6-refused` RFCs,
ADRs (`architecture/decisions/`), and prose that describes the rename itself (review the diff for those).
Released-version snapshots live outside the repositories this script is pointed at.

Rust test sources embed Metel snippets in string literals; they are not rewritten. `--report-rust` lists the
candidate lines so the grammar change (metel-core#1850) can fix them by hand.

Usage:
  tools/sweep_pub.py PATH...                  dry run: report what would change
  tools/sweep_pub.py --apply PATH...          rewrite the files
  tools/sweep_pub.py --check PATH...          CI gate: exit 1 if any swept scope still has `public`
  tools/sweep_pub.py --report-rust PATH...    list Rust lines that embed `public <decl keyword>`
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

NEW = "pub"
DECL_KEYWORDS = (
    "fun", "struct", "enum", "aspect", "type", "record", "extend", "let", "var", "use",
    "copy", "linear", "declared", "const", "comptime", "mod", "impl",
)
_DECL = "|".join(DECL_KEYWORDS)

WORD_RE = re.compile(r"(?<![A-Za-z0-9_])public(?![A-Za-z0-9_])")
CHAR_LIT_RE = re.compile(r"'(?:\\(?:u\{[0-9a-fA-F]{1,6}\}|[ntr\\'])|[^'\\\n])'")
FENCE_OPEN_RE = re.compile(r"^(?P<indent>[ \t]*)(?P<fence>`{3,}|~{3,})[ \t]*(?P<lang>[^\s`]*)")
INLINE_SPAN_RE = re.compile(r"`public(?P<rest>(?: (?:" + _DECL + r")\b[^`]*)?)`")
RUST_CANDIDATE_RE = re.compile(r"\bpublic (?:" + _DECL + r")\b")

DEFAULT_EXCLUDES = (
    "release-notes/",
    "rfcs/5-superseded/",
    "rfcs/6-refused/",
    "architecture/decisions/",
    "/target/",
    "node_modules/",
    "/.git/",
    "/.claude/",
)
METEL_FENCE_TAGS = {"metel", "mtl"}


# ----------------------------------------------------------------------------
# Metel lexing: which byte ranges are code
# ----------------------------------------------------------------------------

def _skip_interpolation(src: str, i: int) -> int:
    """`i` is just after `${`; return the index just after the matching `}`."""
    depth = 1
    n = len(src)
    while i < n and depth:
        ch = src[i]
        if ch == '"':  # nested string inside an interpolation: no escapes (grammar: nested_string)
            i += 1
            while i < n and src[i] != '"':
                i += 1
            i += 1
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
        i += 1
    return i


def _skip_string(src: str, i: int) -> int:
    """`i` is at the opening quote; return the index just after the closing quote."""
    n = len(src)
    j = i + 1
    while j < n:
        ch = src[j]
        if ch == "\\":
            j += 2
        elif ch == '"':
            return j + 1
        elif src.startswith("${", j):
            j = _skip_interpolation(src, j + 2)
        else:
            j += 1
    return n


def segments(src: str):
    """Yield (kind, start, end) with kind "code" or "comment"; strings and char literals are yielded as neither."""
    n = len(src)
    i = 0
    start = 0
    while i < n:
        if src.startswith("//", i):
            if start < i:
                yield ("code", start, i)
            nl = src.find("\n", i)
            end = n if nl == -1 else nl
            yield ("comment", i, end)
            i = start = end
        elif src.startswith("/*", i):
            if start < i:
                yield ("code", start, i)
            close = src.find("*/", i + 2)
            end = n if close == -1 else close + 2
            yield ("comment", i, end)
            i = start = end
        elif src[i] == '"':
            if start < i:
                yield ("code", start, i)
            i = _skip_string(src, i)
            start = i
        elif src[i] == "'":
            m = CHAR_LIT_RE.match(src, i)
            if m:
                if start < i:
                    yield ("code", start, i)
                i = m.end()
                start = i
            else:  # an anchor such as 'a, not a char literal
                i += 1
        else:
            i += 1
    if start < n:
        yield ("code", start, n)


def code_spans(src: str):
    """Yield (start, end) of every stretch of `src` that is code, not a comment, string or char literal."""
    for kind, a, b in segments(src):
        if kind == "code":
            yield (a, b)


def sweep_metel(src: str) -> tuple[str, int]:
    """Rewrite the keyword in Metel source. Returns (new source, number of rewrites)."""
    out = []
    last = 0
    count = 0
    for kind, a, b in segments(src):
        seg = src[a:b]
        if kind == "code":
            new, k = WORD_RE.subn(NEW, seg)
        else:
            new, k = INLINE_SPAN_RE.subn(lambda mm: "`" + NEW + mm.group("rest") + "`", seg)
        if k:
            out.append(src[last:a])
            out.append(new)
            last = b
            count += k
    out.append(src[last:])
    return "".join(out), count


# ----------------------------------------------------------------------------
# Markdown: tagged fences and inline spans
# ----------------------------------------------------------------------------

def sweep_markdown(text: str, inline: bool = True) -> tuple[str, int, int, int]:
    """Returns (new text, fence rewrites, inline rewrites, untagged-fence candidates)."""
    lines = text.splitlines(keepends=True)
    out: list[str] = []
    fence_hits = inline_hits = untagged = 0
    i = 0
    while i < len(lines):
        m = FENCE_OPEN_RE.match(lines[i])
        if not m:
            line = lines[i]
            if inline:
                line, k = INLINE_SPAN_RE.subn(lambda mm: "`" + NEW + mm.group("rest") + "`", line)
                inline_hits += k
            out.append(line)
            i += 1
            continue
        fence = m.group("fence")
        lang = m.group("lang").lower()
        out.append(lines[i])
        i += 1
        body_start = i
        while i < len(lines):
            s = lines[i].strip()
            if s and set(s) == {fence[0]} and len(s) >= len(fence):
                break
            i += 1
        body = "".join(lines[body_start:i])
        if lang in METEL_FENCE_TAGS:
            body, k = sweep_metel(body)
            fence_hits += k
        elif lang == "":
            untagged += len(WORD_RE.findall(body))
        out.append(body)
        if i < len(lines):
            out.append(lines[i])
            i += 1
    return "".join(out), fence_hits, inline_hits, untagged


# ----------------------------------------------------------------------------
# Files
# ----------------------------------------------------------------------------

def iter_files(paths, suffixes, excludes):
    for raw in paths:
        p = Path(raw)
        candidates = [p] if p.is_file() else sorted(q for q in p.rglob("*") if q.is_file())
        for q in candidates:
            if q.suffix not in suffixes:
                continue
            posix = "/" + q.as_posix().lstrip("/")
            if any(e in posix for e in excludes):
                continue
            yield q


def read(path: Path) -> str:
    with open(path, encoding="utf-8", newline="") as f:  # newline="" keeps CRLF intact
        return f.read()


def write(path: Path, text: str) -> None:
    with open(path, "w", encoding="utf-8", newline="") as f:
        f.write(text)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("paths", nargs="+")
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument("--apply", action="store_true", help="rewrite the files")
    mode.add_argument("--check", action="store_true", help="exit 1 if any swept scope still has `public`")
    mode.add_argument("--report-rust", action="store_true", help="list Rust lines embedding `public <decl>`")
    ap.add_argument("--no-inline", action="store_true", help="do not rewrite inline code spans in Markdown")
    ap.add_argument("--exclude", action="append", default=[], help="skip paths containing this substring")
    ap.add_argument("--no-default-excludes", action="store_true")
    args = ap.parse_args(argv)

    excludes = list(args.exclude)
    if not args.no_default_excludes:
        excludes += DEFAULT_EXCLUDES

    if args.report_rust:
        total = 0
        for f in iter_files(args.paths, {".rs"}, excludes):
            for ln, line in enumerate(read(f).splitlines(), 1):
                if RUST_CANDIDATE_RE.search(line):
                    print(f"{f}:{ln}: {line.strip()}")
                    total += 1
        print(f"{total} Rust line(s) embed `public <declaration keyword>`; fix by hand (not rewritten).")
        return 0

    files = rewrites = inline = untagged = changed = 0
    for f in iter_files(args.paths, {".mtl", ".md", ".mdx"}, excludes):
        files += 1
        text = read(f)
        if f.suffix == ".mtl":
            new, k = sweep_metel(text)
            fk, ik, ut = k, 0, 0
        else:
            new, fk, ik, ut = sweep_markdown(text, inline=not args.no_inline)
        rewrites += fk
        inline += ik
        untagged += ut
        if new != text:
            changed += 1
            print(f"{f}: {fk} in code, {ik} inline" + (f", {ut} in untagged fences (not rewritten)" if ut else ""))
            if args.apply:
                write(f, new)
        elif ut:
            print(f"{f}: {ut} in untagged fences (not rewritten)")
    print(f"{files} file(s) scanned, {changed} {'rewritten' if args.apply else 'to rewrite'}: "
          f"{rewrites} keyword(s) in code, {inline} inline span(s), {untagged} left in untagged fences")
    if args.check and changed:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
