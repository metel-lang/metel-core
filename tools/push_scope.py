#!/usr/bin/env python3
"""Does a push touch only documentation? (`.githooks/pre-push`)

The pre-push hook runs clippy and the whole test suite, about ten minutes. A push that changes only the
documentation pin, ROADMAP.md, the process documents or `docs/` cannot change what those check, so the hook
skips them (CI still runs everything on the pull request).

Reads git's pre-push lines on stdin (`<local ref> <local sha> <remote ref> <remote sha>`) and prints
`docs-only` or `code`. Anything it cannot establish (no lines, no merge base, a git failure) is `code`: the
full checks run. A branch delete pushes no commits and counts as docs-only.

Usage: git pre-push hook:  printf '%s\\n' "$refs" | tools/push_scope.py
"""

import subprocess
import sys

ZERO = "0" * 40
# The `docs` gitlink is the documentation pin; the root process documents carry no checked code (README.md
# does: its examples run in CI, so it is not listed).
DOCS_PATHS = {
    "docs",
    "ROADMAP.md",
    "AGENTS.md",
    "CLAUDE.md",
    "PROCESSES.md",
    "RELEASING.md",
}


def is_docs_path(path: str) -> bool:
    return path in DOCS_PATHS or path.startswith("docs/")


def git(*args: str) -> str | None:
    result = subprocess.run(["git", *args], capture_output=True, text=True)
    return result.stdout if result.returncode == 0 else None


def base_for(remote_sha: str, local_sha: str) -> str | None:
    """The commit the push is measured against: the remote's tip, or for a new branch its merge base with develop."""
    if remote_sha != ZERO:
        return remote_sha
    for upstream in ("origin/develop", "develop"):
        out = git("merge-base", upstream, local_sha)
        if out and out.strip():
            return out.strip()
    return None


def push_is_docs_only(lines: list[str]) -> bool:
    seen = False
    for line in lines:
        parts = line.split()
        if len(parts) != 4:
            continue
        _local_ref, local_sha, _remote_ref, remote_sha = parts
        if local_sha == ZERO:
            continue  # a delete: nothing to test
        seen = True
        base = base_for(remote_sha, local_sha)
        if base is None:
            return False
        changed = git("diff", "--name-only", "--no-renames", base, local_sha)
        if changed is None:
            return False
        if not all(is_docs_path(p) for p in changed.split("\n") if p):
            return False
    # Only deletes (or nothing) pushed: nothing to test either, but an empty stdin is not evidence.
    return seen or bool(lines)


def main() -> int:
    docs_only = push_is_docs_only(sys.stdin.read().splitlines())
    print("docs-only" if docs_only else "code")
    return 0


if __name__ == "__main__":
    sys.exit(main())
