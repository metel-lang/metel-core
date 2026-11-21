# /stage-gate

Gate a completed stage of a staged release, before the next stage is called done.

**Arguments:** `$ARGUMENTS` — the release and the stage: `v0.17.0 "Linear types"`. The stage may be given by
its title (`[v0.17.0] Linear types`) or its name (`Linear types`). The release must be staged
(`ROADMAP.md`, "How milestones work"): the stage says `Part of: <release>` and the release lists it
under `Stages:`.

A staged release used to run every gate once, at the end, so a fault in the first stage surfaced after the
last. This command runs the gates **when each stage completes**, on the stage together with the stages
already gated. Order of the whole process: `/gap-analysis` at the start of a stage → implement its
issues → **`/stage-gate`** → … → `/milestone-integration-test` over the whole release → `/cut-release`.
It does not replace the last two: the pairs that span two stages are first exercised together in the
integration session, and `/cut-release` still sweeps repository-wide state.

Its output is a committed report, `docs/release-notes/integration/<release>/stage-<slug>.md` in
`metel-docs`, and the stage milestone closed. `/cut-release` refuses to tag unless every stage has both.
A stage stays open until it passes, and the release does not move past it. A finding is a fix or a
deferral, one issue each, through the normal per-PR flow; this is a session, not an issue branch.

---

## Step 0 — The stage is ready to be gated

```bash
VERSION=<release>; STAGE="<stage name>"
python3 tools/release_stages.py check "$VERSION"     # the release and its stages agree
python3 tools/release_stages.py list "$VERSION"
python3 tools/release_stages.py open "$VERSION" | sed -n "/== \[$VERSION\] $STAGE/,/^==/p"
```

`check` must be clean. A stage that is not listed, or whose title lacks its tag, is fixed first (a link
problem is the release's, not the stage's). The stage's own issues must all be closed, with the same rule
as `/cut-release` Step 1: each remaining open issue is genuinely done and gets closed, or is deferred and
re-milestoned off the stage (a deferred bug goes to `Backlog`). A closed box is not proof: confirm each
closed issue's acceptance criteria were met.

Then read the stage's description and check its **exit test** clause by clause. Name the evidence for
each (a fixture, a merged PR, an RFC at the required state). A design stage's exit test is usually RFC
state; an implementation stage's is behaviour a fixture shows. An exit clause with no evidence blocks.

## Step 1 — Bugs

```bash
gh issue list --label severity:soundness --state open
gh issue list --label regression --state open
```

An open `severity:soundness` bug blocks the stage wherever it is milestoned. An open `regression`
introduced since the last tag blocks it unless the user explicitly defers it.

## Step 2 — RFC state

```bash
python3 docs/rfcs/tools/rfc.py check
```

Clean. Every RFC the stage owns is at the state its exit test names. An RFC the stage implements
end-to-end moves to `4-implemented` now (`rfc.py transition <id> --to implemented`), not at the cut, so
its spec callouts are current while the work is fresh. `/cut-release` re-runs the check with `--strict`.

## Step 3 — The feature matrix, cumulative

Register what the stage delivers in `tools/feature-matrix/registry.toml`, as `/milestone-integration-test`
Step 1 does, with `introduced = "<release>"` and `stage = "<stage name>"`. A scoped gate needs **every**
feature of the release to name its stage, and errors on one that does not.

The scope is this stage and every stage already gated, so a later stage's unfinished features cannot block
this one and an earlier stage's features still meet this stage's:

```bash
stage_args=()
while IFS= read -r s; do stage_args+=(--stage "$s"); done < <(python3 tools/release_stages.py scope "$VERSION" "$STAGE")
python3 tools/feature_matrix.py "$VERSION" "${stage_args[@]}" --blockers
```

It must print `Gate: PASS`. A blocking cell is closed the way `/milestone-integration-test` Step 3 closes
it: a fixture tagged with the spec rules of both features, an `n/a` with a reason, or a deferral with an
issue. Fixtures and the bugs they find go through the per-PR flow, one issue per finding. A design-only
stage with no registry features passes this step with a note, and says so in the report.

## Step 4 — Full-tree verification on `develop`

On the tip of `develop`, after the stage's last pull request has merged:

```bash
cd metel-interpreter && cargo test --release
cargo clippy --release --lib -- -W clippy::pedantic
cargo build --release -p metel
./target/release/move-check-count metel-interpreter/tests/integration/sources
python3 ../tools/check_doc_examples.py --binary target/release/metel \
    ../README.md ../docs/getting-started/tutorials ../docs/reference/spec
```

Zero failures, zero clippy warnings, doc examples clean, and `move-check-count` no worse than its
baseline (`/milestone-integration-test` Step 4). This is the point of gating a stage: `develop` is checked
at every stage boundary, not first at the end.

## Step 5 — Report, close, hand over

Write `docs/release-notes/integration/<release>/stage-<slug>.md` in `metel-docs`, on a branch off `main`,
and merge it. The slug is the stage name lower-cased, with runs of other characters as `-`
(`tools/release_stages.py check "$VERSION" --gated` prints the exact path it looks for).

```markdown
# Stage gate — <release>, <stage name>

**Run:** <date> · against `develop` at `<short-sha>`.
**Result:** <PASS | BLOCKED — see findings>.
**Stages in scope:** <this stage>, <the stages already gated>.

## Exit test

- <clause> — <evidence>
- …

## Features exercised

- <capability> (RFC-NNNN, #issue), or "none: design-only stage".

## Matrix

The `--blockers` summary from Step 3 and its `Gate:` line; the `n/a` and deferred cells with their reasons.

## Findings

- **#N** — <one line>. <fixed on #M | deferred to vX.Y.Z or Backlog>.
- (none)

## Verification

Step 4 results on `<sha>`.
```

Only when the result is `PASS`, after the report is merged and the docs gitlink bumped
(`git -C docs checkout main && git -C docs pull`, then a commit that bumps `docs`), close the stage:

```bash
number=$(gh api repos/metel-lang/metel-core/milestones --paginate --jq ".[] | select(.title == \"[$VERSION] $STAGE\") | .number")
gh api -X PATCH "repos/metel-lang/metel-core/milestones/$number" -f state=closed
python3 tools/release_stages.py list "$VERSION"
```

Report to the user:

```
## <release> — stage "<stage>" gated

**Result:** PASS · stages gated: <n> of <total> · open: <names>
**Report:** docs/release-notes/integration/<release>/stage-<slug>.md
**Findings:** #N (fixed), #M (deferred → …), …
**Next:** <the next stage to finish | /milestone-integration-test <release>>
```

---

## Notes

- A stage is gated against the `develop` it ran on. Later work can break it; that is what the cumulative
  scope of the following stage gates, and the whole-release integration session, are for. They re-verify,
  so a stage gate that predates a regression does not hide it.
- A stage that is blocked and will not be fixed in this release slips instead (`ROADMAP.md`): its `Part of:`
  line, its `Stages:` entry and the title tag are removed, and its registry features move to the release
  they will ship in. A stage that already passed its gate cannot slip; its work is on `develop`.
- Gate stages in the order they finish, one at a time. If two finish together, the second gate's scope
  includes the first.
