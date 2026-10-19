# /cut-release

Cut a release: run the release gate, fast-forward `main` to `develop`, tag, and publish.

**Arguments:** `$ARGUMENTS` — the version, e.g. `v0.12.0`. The version is chosen here, by the
rule in gate item 2, not when the work was planned (`ROADMAP.md`). If the release was
built from a theme milestone, rename that milestone to `$ARGUMENTS` first (renaming keeps its
issues); after the cut, promote the next theme the same way.

**Nothing is pushed until every gate item passes.** The gate is defined in AGENTS.md
§ Release Workflow — this command runs it, it does not redefine it. If the two disagree,
AGENTS.md wins.

A release is cut when a **version milestone completes**, not on a calendar. This is the
periodic half of the two gates: it sweeps repository-wide state that no single pull
request owns. It does **not** re-run the per-PR gate — those checks already passed on
every branch that landed — and it assumes `/milestone-integration-test` has already
exercised the milestone's features in combination (Step 1b); this command gates on that
session's report, it does not perform it.

---

## Step 0 — Freeze `develop`

Merge nothing into `develop` between the gate passing and the tag being pushed. `main`
must land on `develop`'s **tip**, not on a commit inside a longer line of work — that is
how `v0.11.0` ended up tagged 116 commits into `sprint/27` with 72 more still to come,
bracketing a range nobody had decided on.

Announce the freeze, then:

```bash
git checkout develop && git pull --recurse-submodules
git log --oneline $(git describe --tags --abbrev=0 origin/main)..develop
```

That range is what this release ships. Read it — it is the input to every gate item below.

## Step 1 — Milestone is actually complete

```bash
gh issue list --milestone  --state open
```

Every remaining open issue is either genuinely done and needs closing, or is deferred and
must be **re-milestoned to a later version** — not left silently attached to this one.
A deferred **bug** goes back to the `Backlog` milestone, never to a theme.

Then check bugs repo-wide, not just in this milestone:

```bash
gh issue list --label severity:soundness --state open
gh issue list --label regression --state open
```

An open `severity:soundness` bug blocks the release wherever it is milestoned. An open
`regression` introduced since the last tag blocks it unless the user explicitly defers it.
Confirm closed issues had their acceptance criteria satisfied; a closed box is not proof.

## Step 1b — Integration session

```bash
ls docs/release-notes/integration/$ARGUMENTS.md
```

`/milestone-integration-test $ARGUMENTS` has been run, and its report exists, is dated
**on or after the Step 0 freeze**, and its `**Result:**` line reads `PASS`. Every finding
it lists is a closed fix or a deferred issue re-milestoned off `$ARGUMENTS` (the Step 1
rule, applied to the session's findings). A stale report — `<short-sha>` older than
`develop`'s tip — does not count; re-run the session on the frozen tree.

If the report is missing, stop and run `/milestone-integration-test $ARGUMENTS` first.

## Step 2 — Release gate

**1. Changelog finalized** — `docs/release-notes/changelog.md`'s in-progress
section is complete and accurate against the commit range from Step 0. Reword for
clarity, then replace the "in progress on `develop` — not yet released" line with the
release date. Cross-check with:

```bash
tools/changelog-status.sh
```

**2. Version number chosen** — per `docs/internal/versioning.md`'s major/minor/patch rule:
a spec change requires at least a minor bump; a patch must not touch language-visible
behaviour at all. Bump `metel-interpreter/Cargo.toml`'s `version` to match, in the same
commit as the changelog finalization.

**3. RFC state** —

```bash
python3 docs/rfcs/tools/rfc.py check
```

Reports clean. Any RFC this release implements end-to-end moves to `4-implemented`
(`rfc.py transition <id> --to implemented`) rather than being left at `3-integrated` with
stale "Not yet implemented" spec callouts.

Also bump the spec's fixture-viewer ref to the tag being cut (metel-core#944): in the
`metel-docs` working tree, set `SPEC_FIXTURE_REF` in `rfcs/tools/rfc.py` to `$ARGUMENTS`,
run `python3 docs/rfcs/tools/rfc.py index --write-spec-origins`, and commit both on
`metel-docs main` — so every Formal-rules block's fixture `href` and inlined source
snapshot point at this release's tag, not `main`. This is the once-per-release move that
keeps `--check-drift` quiet between releases.

**4. Docs submodule in lockstep** — bump the `docs` pointer to `metel-docs main`'s tip as
part of the release commit. This is the only time `main`'s pointer moves. Since
`metel-docs` is trunk-based, its `main` should already hold everything the changelog and
spec entries were written against; if it doesn't, something bypassed the pair rule.

**5. Spec correctness** — spot-check `docs/reference/spec.md` and its linked
sections against the behaviour actually being released, not an aspirational version of it.

**6. Internal docs** — `docs/architecture/architecture.md`,
`metel-frontend/docs/typechecker.md`, and `metel-interpreter/docs/evaluator.md` reflect
the pipeline, inference, construction, runtime, and builtin behaviour as it now is. Read
them against the release's diff, not from memory.

**7. Decision records** — every non-obvious architectural decision, reversal, or
workaround this release introduced has an ADR in
`docs/architecture/decisions/`. A
reversal especially: why a past decision stopped holding is the part that gets lost.

**8. Full suite green on the release commit** — the per-PR gate ran per branch, but not
on this exact tree:

```bash
cd metel-interpreter && cargo test --release
cargo clippy --release --lib -- -W clippy::pedantic
```

Confirm by reading the `test result:` lines and a 0-warning clippy tail.

**9. Doc examples green** — `tools/check_doc_examples.py` reports clean:

```bash
cargo build --release -p metel
python3 tools/check_doc_examples.py --binary target/release/metel \
    README.md docs/getting-started/tutorials docs/reference/spec
```

Confirm by reading the CI job `doc-examples`'s result on the release commit rather than
re-running it locally, unless the submodule pointer just moved and CI hasn't caught up.

## Step 3 — Fix findings, then re-run

Every failing item gets fixed on its own issue branch through the normal per-PR flow —
a release does not license committing straight to `develop`. Then re-run the gate.

## Step 4 — Fast-forward and tag

```bash
git checkout main
git merge --ff-only develop
git push origin main
git tag -a $ARGUMENTS -m "$ARGUMENTS: <theme>"
git push origin $ARGUMENTS
```

There is no release merge commit. Because every issue branch fast-forwarded into
`develop`, `main` is by construction a prefix of it, and what a release contained is read
off the tags bracketing the range.

The tag is created on `main` after the fast-forward, never before, and its name must match
the version in the changelog and in `Cargo.toml`.

## Step 5 — Publish

Pushing the tag in Step 4 already triggers both of the following automatically
(`.github/workflows/release.yml`, metel-core#614 and #643) — nothing to do here but
verify they actually ran and succeeded:

1. A GitHub Release is created from the tag, with the body sourced directly from the
   changelog section just finalized — not regenerated separately. The changelog is the
   single source of truth for release notes. A release binary (`metel`, Linux x86_64)
   is attached alongside it.
2. `metel-website`'s `docs` pointer is bumped to this repo's own pinned `metel-docs`
   commit, its versioned docs snapshot cut, and the website built and deployed to
   staging (see `RELEASING.md`). Production promotion is still a deliberate manual
   step — review the staging URL and run `promote.yml`.

Lift the freeze on `develop` once both are confirmed green.

## Step 6 — Report

```
## $ARGUMENTS — released

**Range:** <prev-tag>..$ARGUMENTS (<N> commits)
**Gate:** integration session PASS + all 9 release-gate items passed.

### Shipped
- #N: <title>
…

### RFCs reaching implemented
- RFC-NNNN: <title>
…

### Deferred out of this milestone
- #N: <title> → re-milestoned to <version>
…
```

## Notes

- Do not tag before `main` is pushed and verified — check the remote rather than trusting
  the push output, which has reported "Everything up-to-date" against a stale ref before.
- A patch release that turns out to contain a spec change is not a patch release; go back
  to gate item 2.
- If gaps surfaced that need design rather than a fix, prompt the user to run `/new-rfc`.
