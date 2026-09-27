#!/usr/bin/env bash
# Report which unreleased feature/fix commits are not yet reflected in the changelog.
#
# The changelog lives in the `docs/` submodule, so a feature commit in this repo can never
# contain its own changelog entry — the entry is a separate commit in `metel-docs`. That
# split is exactly why "update the changelog when the feature lands" silently stopped
# happening. This turns the changelog step of the per-PR and release gates from a memory
# exercise into a diff you can read.
#
# Heuristic, deliberately: it compares commit timestamps across the two repositories rather
# than trying to match issue numbers, because changelog entries are written in prose and
# do not cite issue numbers. It reports; it does not enforce. A commit listed as UNLOGGED
# may well be covered by a later changelog edit that also covered something else — read the
# section and decide.
#
# Usage: tools/changelog-status.sh [since-ref]
#   since-ref defaults to the most recent v* tag.

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

changelog="docs/release-notes/changelog.md"
if [[ ! -f "$changelog" ]]; then
    echo "error: $changelog not found — is the docs submodule checked out?" >&2
    exit 1
fi

since="${1:-$(git describe --tags --abbrev=0 --match 'v*' 2>/dev/null || true)}"
if [[ -z "$since" ]]; then
    echo "error: no v* tag found; pass a ref explicitly" >&2
    exit 1
fi

echo "Unreleased range: ${since}..HEAD"

section="$(grep -m1 '^## ' "$changelog" || true)"
echo "Changelog top section: ${section:-<none>}"

# When was the changelog last actually edited, in the submodule's own history?
last_entry_epoch="$(git -C docs log -1 --format=%ct -- release-notes/changelog.md 2>/dev/null || echo 0)"
if [[ -z "$last_entry_epoch" || "$last_entry_epoch" == "0" ]]; then
    echo "Changelog last edited: never (in submodule history)"
else
    echo "Changelog last edited: $(date -d "@$last_entry_epoch" '+%Y-%m-%d %H:%M')"
fi
echo

# Feature and fix commits that changed real code, newest first.
mapfile -t commits < <(
    git log --no-merges --format='%ct%x09%h%x09%s' "${since}..HEAD" -- metel-interpreter/src metel-interpreter/stdlib \
        | grep -E $'\t(feat|fix)(\\(|:)' || true
)

if [[ ${#commits[@]} -eq 0 ]]; then
    echo "No feature or fix commits in range."
    exit 0
fi

unlogged=0
for line in "${commits[@]}"; do
    IFS=$'\t' read -r epoch sha subject <<<"$line"
    if (( epoch > last_entry_epoch )); then
        printf 'UNLOGGED  %s  %s\n' "$sha" "$subject"
        unlogged=$((unlogged + 1))
    else
        printf 'ok        %s  %s\n' "$sha" "$subject"
    fi
done

echo
if (( unlogged > 0 )); then
    echo "$unlogged commit(s) land after the changelog was last edited."
    echo "Add their entries to $changelog, commit in the submodule, then bump the pointer here."
    exit 1
fi
echo "All ${#commits[@]} feature/fix commit(s) predate the last changelog edit."
