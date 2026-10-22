#!/usr/bin/env bash
# Move this repo's `docs` gitlink to metel-docs `main` (or another commit) on its own branch and
# open the pull request, so a docs-only change reaches core's pin without writing the PR by hand
# (metel-core#1511).
#
# Why a script and not a bot: a pull request opened with the default GITHUB_TOKEN does not trigger
# CI, so its required checks would never run. A bot would need a credential that can push branches
# and open PRs here; the repository has none, and this keeps a person in the loop. Run it when core
# work needs new docs content (a claim id, a spec rule a fixture cites, a tool change). The release
# pins the exact commit separately (`/cut-release`, gate item 4).
#
# What it does:
#   1. resolves the target commit (metel-docs `main` by default) without needing the submodule checked out;
#   2. stops if the pin already points there;
#   3. creates `chore/bump-docs-<short sha>` from `origin/develop`;
#   4. moves the gitlink with `git update-index --cacheinfo` (never `git commit -- docs`, and no
#      bare stash), commits, pushes, and opens the PR with the docs commits listed;
#   5. unless --skip-checks, first runs the docs-dependent checks CI runs, on the new commit.
# It never merges.
#
# Usage: tools/bump-docs.sh [--sha <docs-commit>] [--issue <N>] [--base <branch>] [--skip-checks] [--no-pr] [--dry-run]
#   --sha          bump to this commit instead of metel-docs main
#   --issue        reference an issue in the commit title: chore(#N): ...
#   --base         branch to start from and target (default: develop)
#   --skip-checks  do not run rfc.py check and the architecture check
#   --no-pr        commit and push the branch, do not open the PR
#   --dry-run      print what would happen; change nothing

set -euo pipefail

sha="" issue="" base="develop" skip_checks=0 no_pr=0 dry_run=0
while [[ $# -gt 0 ]]; do
    case "$1" in
        --sha) sha="${2:?--sha needs a commit}"; shift 2 ;;
        --issue) issue="${2:?--issue needs a number}"; shift 2 ;;
        --base) base="${2:?--base needs a branch}"; shift 2 ;;
        --skip-checks) skip_checks=1; shift ;;
        --no-pr) no_pr=1; shift ;;
        --dry-run) dry_run=1; shift ;;
        -h|--help) sed -n '2,/^set -euo/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//'; exit 0 ;;
        *) echo "error: unknown argument: $1 (see --help)" >&2; exit 2 ;;
    esac
done

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

say() { printf '%s\n' "$*"; }
run() { if [[ $dry_run -eq 1 ]]; then say "[dry-run] $*"; else "$@"; fi; }

docs_url="$(git config -f .gitmodules --get submodule.docs.url)" \
    || { echo "error: no submodule.docs.url in .gitmodules" >&2; exit 1; }

# --- the pinned commit (what origin/<base> records, not the local working tree) ---------------
git fetch -q origin "$base"
pinned="$(git ls-tree "origin/$base" docs | awk '{print $3}')"
[[ -n "$pinned" ]] || { echo "error: origin/$base has no docs gitlink" >&2; exit 1; }

# --- the target commit --------------------------------------------------------------------------
if [[ -z "$sha" ]]; then
    sha="$(git ls-remote "$docs_url" refs/heads/main | awk '{print $1}')"
    [[ -n "$sha" ]] || { echo "error: could not read refs/heads/main from $docs_url" >&2; exit 1; }
fi
if [[ ${#sha} -lt 40 ]]; then
    # a short sha needs the objects; use the submodule checkout if there is one
    full="$(git -C docs rev-parse --verify "$sha^{commit}" 2>/dev/null || true)"
    [[ -n "$full" ]] || { echo "error: give a full 40-character --sha (cannot expand '$sha' without the docs checkout)" >&2; exit 1; }
    sha="$full"
fi

short="${sha:0:7}"
if [[ "$sha" == "$pinned" ]]; then
    say "docs gitlink on origin/$base already points at $short; nothing to bump."
    exit 0
fi

# --- a clean tree to branch from ----------------------------------------------------------------
if [[ -n "$(git status --porcelain --untracked-files=no -- . ':!docs')" ]]; then
    echo "error: the working tree has uncommitted changes; commit or move them first" >&2
    exit 1
fi

branch="chore/bump-docs-$short"
if git show-ref --verify --quiet "refs/heads/$branch" || git ls-remote --exit-code --heads origin "$branch" >/dev/null 2>&1; then
    echo "error: branch $branch already exists; delete it or pick another --sha" >&2
    exit 1
fi

# --- what the bump brings in --------------------------------------------------------------------
log=""
if git -C docs cat-file -e "$pinned^{commit}" 2>/dev/null; then
    git -C docs fetch -q origin 2>/dev/null || true
    if git -C docs cat-file -e "$sha^{commit}" 2>/dev/null; then
        log="$(git -C docs log --oneline --no-decorate "$pinned..$sha" | head -30)"
    fi
fi

say "docs gitlink: ${pinned:0:7} -> $short   (base: origin/$base, branch: $branch)"
[[ -n "$log" ]] && { say "metel-docs commits:"; printf '%s\n' "$log" | sed 's/^/  /'; }

if [[ $dry_run -eq 1 ]]; then
    say "[dry-run] would branch, move the gitlink, commit, push$([[ $no_pr -eq 1 ]] || printf ', open a PR')."
    exit 0
fi

git switch -q -c "$branch" "origin/$base"

# --- move the gitlink ---------------------------------------------------------------------------
git update-index --cacheinfo "160000,$sha,docs"
if [[ -d docs/.git || -f docs/.git ]]; then
    git -C docs fetch -q origin 2>/dev/null || true
    git -C docs checkout -q "$sha" 2>/dev/null || say "note: could not check the docs working tree out at $short; run: git -C docs checkout $short"
fi

# --- the checks that read docs ------------------------------------------------------------------
checks="not run (--skip-checks)"
if [[ $skip_checks -eq 0 ]]; then
    if [[ -f docs/rfcs/tools/rfc.py ]] && [[ "$(git -C docs rev-parse HEAD 2>/dev/null)" == "$sha" ]]; then
        python3 docs/rfcs/tools/rfc.py check >/dev/null
        python3 docs/architecture/tools/generate_architecture_evidence.py --core . --check
        checks="rfc.py check and the architecture evidence check pass on the new commit"
    else
        checks="not run (docs working tree is not at $short)"
    fi
fi

title="chore: bump docs gitlink to ${short}"
[[ -n "$issue" ]] && title="chore(#$issue): bump docs gitlink to ${short}"
body_log="${log:-(the docs history is not available locally; see the compare view)}"
git commit -q -m "$title" -m "metel-docs ${pinned:0:7}..${short}"
git push -q -u origin "$branch"
say "pushed $branch"

if [[ $no_pr -eq 0 ]]; then
    pr_body="Moves the \`docs\` gitlink from \`${pinned:0:7}\` to \`${short}\` (metel-docs).

\`\`\`
${body_log}
\`\`\`

Checks run before opening: ${checks}.

Opened by \`tools/bump-docs.sh\` (metel-core#1511)."
    gh pr create --base "$base" --head "$branch" --title "$title" --body "$pr_body"
fi
