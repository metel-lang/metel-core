#!/usr/bin/env bash
# Self-test for tools/bump-docs.sh (metel-core#1511): real git repositories in a temp directory,
# no network, no `gh`. Run: tools/test_bump_docs.sh
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# identity for the commits the script itself makes
export GIT_AUTHOR_NAME=test GIT_AUTHOR_EMAIL=t@example.com GIT_COMMITTER_NAME=test GIT_COMMITTER_EMAIL=t@example.com

fail() { echo "FAIL: $*" >&2; exit 1; }
git_quiet() { git -c user.email=t@example.com -c user.name=test "$@"; }

# metel-docs stand-in with two commits on main
git init -q --bare "$tmp/docs-origin.git"
git init -q "$tmp/docs-work"
(
    cd "$tmp/docs-work"
    echo one > a.md; git add -A; git_quiet commit -q -m one
    echo two > a.md; git add -A; git_quiet commit -q -m two
    git branch -M main
    git push -q "$tmp/docs-origin.git" main
)
c1="$(git -C "$tmp/docs-work" rev-parse HEAD~1)"
c2="$(git -C "$tmp/docs-work" rev-parse HEAD)"

# metel-core stand-in pinned to the first docs commit
git init -q --bare "$tmp/core-origin.git"
git init -q "$tmp/core"
(
    cd "$tmp/core"
    printf '[submodule "docs"]\n\tpath = docs\n\turl = %s\n' "$tmp/docs-origin.git" > .gitmodules
    mkdir tools; cp "$here/bump-docs.sh" tools/
    git add -A
    git update-index --add --cacheinfo "160000,$c1,docs"
    git_quiet commit -q -m initial
    git remote add origin "$tmp/core-origin.git"
    git push -q origin HEAD:develop
)

cd "$tmp/core"
script=tools/bump-docs.sh

# 1. unknown argument is a usage error
set +e; "$script" --nope >/dev/null 2>&1; code=$?; set -e
[[ $code -eq 2 ]] || fail "unknown argument should exit 2, got $code"

# 2. dry run changes nothing
out="$("$script" --dry-run --skip-checks)"
grep -q "${c1:0:7} -> ${c2:0:7}" <<<"$out" || fail "dry run should name the move: $out"
[[ "$(git branch --list 'chore/bump-docs-*')" == "" ]] || fail "dry run created a branch"

# 3. a real run: branch, gitlink moved, commit, pushed, no PR
out="$("$script" --no-pr --skip-checks --issue 1511)"
branch="chore/bump-docs-${c2:0:7}"
[[ "$(git rev-parse --abbrev-ref HEAD)" == "$branch" ]] || fail "should be on $branch"
[[ "$(git ls-tree HEAD docs | awk '{print $3}')" == "$c2" ]] || fail "gitlink not moved to the target"
[[ "$(git log -1 --format=%s)" == "chore(#1511): bump docs gitlink to ${c2:0:7}" ]] || fail "bad commit title: $(git log -1 --format=%s)"
git ls-remote --exit-code --heads origin "$branch" >/dev/null || fail "branch was not pushed"
[[ "$(git diff --name-only HEAD~1 HEAD)" == "docs" ]] || fail "the commit should change only the docs gitlink"

# 4. running again on a fresh base: the branch exists
git switch -q --detach origin/develop
set +e; "$script" --no-pr --skip-checks >/dev/null 2>&1; code=$?; set -e
[[ $code -eq 1 ]] || fail "an existing branch should be refused, got exit $code"

# 5. a dirty tree is refused
git_quiet branch -q -D "$branch"
git push -q origin ":$branch"
echo dirty > tools/untracked-edit.txt
git add tools/untracked-edit.txt
set +e; "$script" --no-pr --skip-checks >/dev/null 2>&1; code=$?; set -e
git rm -q -f tools/untracked-edit.txt
[[ $code -eq 1 ]] || fail "a dirty tree should be refused, got exit $code"

# 6. once origin/develop pins the target there is nothing to do
git push -q origin "$(git rev-parse HEAD):refs/heads/develop" 2>/dev/null || true
git switch -q -c landed origin/develop
git update-index --cacheinfo "160000,$c2,docs"
git_quiet commit -q -m "land the bump"
git push -q origin landed:develop
out="$("$script" --no-pr --skip-checks)"
grep -q "already points at ${c2:0:7}" <<<"$out" || fail "should report up to date: $out"

echo "bump-docs: all checks passed"
