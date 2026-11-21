# /milestone-integration-test

Exercise a completed milestone's features **in combination**, before `/cut-release`.

**Arguments:** `$ARGUMENTS` — the version, e.g. `v0.13.0` (the numbered release milestone; a
release built from a theme is renamed to its version before this session, see `ROADMAP.md`).
For a staged release the features under test are those of the numbered milestone and of every
stage it lists (`tools/release_stages.py list $ARGUMENTS`). Each stage has already passed `/stage-gate`
over itself and the stages before it, so this session is the whole-release run: no `--stage` scope, so
it is the one that sees the pairs spanning two stages. Start from the stage reports in
`docs/release-notes/integration/$ARGUMENTS/` and do not redo what they cover; fixtures they added count.
Every feature of a staged release carries its stage in the registry (`stage = "<name>"`).

The per-PR gate (AGENTS.md § Verification tiers) proves each diff in isolation.
`/cut-release`'s Step 2 sweeps repository-wide hygiene. Neither exercises what happens
when two features from the same milestone meet — a `move`-capture closure over a
partially-moved struct, a type alias for a move-only function type, a struct pattern that
binds a field whose type is a written callback. This command is that missing gate: it is
run once per milestone, after `/gap-analysis` reports the milestone executed and every
issue closed, and **before** `/cut-release`.

Its output is a committed report, `docs/release-notes/integration/$ARGUMENTS.md` in
`metel-docs`. `/cut-release` refuses to tag without it.

This is a **session**, not an issue branch. Fixtures it adds and bugs it finds go through
the normal per-PR flow — **one issue per finding**, never a single omnibus commit.

---

## Step 1 — Reconcile the feature registry

```bash
git checkout develop && git pull --recurse-submodules
git log --oneline $(git describe --tags --abbrev=0 origin/main)..develop
python3 docs/rfcs/tools/rfc.py check
```

The committed registry in `tools/feature-matrix/registry.toml` is the persistent inventory.
Reconcile it against implemented RFCs and the changelog for `$ARGUMENTS`, including
language-visible fixes and integrated RFC slices. Each capability has a stable ID, source,
introduction release, subsystem tags and owned spec rule IDs. Name capabilities by behavior,
not RFC number.

Do not infer an introduction release from an RFC title or creation date. If neither the
RFC's release metadata nor the changelog establishes it, leave it `unresolved` and report
it. The script reports features without owned spec rules.

## Step 2 — Compute rule coverage and the release gate

```bash
python3 tools/feature_matrix.py "$ARGUMENTS"
```

The script reads the registry, hand-set dispositions in `tools/feature-matrix/states.toml`,
and fixture `spec = [...]` tags. It checks registered rule IDs against the public spec and
computes the milestone baseline plus new-feature rows against the full registry. Use
`--blockers` to print blocking Tier A cells with their fixture evidence, or `--details` to
print every new-feature pair.

For a pair A × B, a fixture contributes only when its `spec` tags cite at least one rule
owned by A and one owned by B. The rule-coverage score is the distinct owned rules cited by
all joint fixtures divided by the distinct owned rules of both features. It measures
citation breadth; review fixture behavior as well. The score accumulates across fixtures and
falls automatically if a fixture is removed or loses relevant tags.

Cell state is computed from the score unless the state file records a disposition:

- **covered** — 100% of the pair's owned rules have joint-fixture evidence.
- **partial** — some, but not all, owned rules have joint-fixture evidence.
- **open** — no joint-fixture evidence, or no owned rules are available to score.
- **n/a** — one-line reason in `states.toml`.
- **deferred** — reason and GitHub issue URL in `states.toml`.

Tier A means a shared subsystem; Tier B means an explicitly configured adjacent-subsystem
pair; Tier C is everything else. The gate (thresholds in the registry's `[gate]` table, ADR-0069) passes only when none of these holds:

- **open-tier-a** — a Tier A cell in a new feature's row is `open` (not covered by a fixture, `n/a`,
  `deferred` or bulk-deferred).
- **joint-fixtures** — a Tier A pair among the release's own features has fewer than two joint fixtures.
- **tier-b-evidence** — a Tier B pair among the release's own features is `open`.
- **feature-floor** — a new feature has evidence in fewer than half of its Tier A pairs (an `n/a` pair
  does not count against it; a bulk deferral is not evidence).
- **expired-bulk** — a `[[bulk]]` deferral of an earlier minor release still has open cells.

A `partial` score is reported and never blocks. A bulk deferral excuses only open-tier-a, and only for the
release it names. Tier C remains visible as debt. Deferred Tier A cells must point to an issue. A `[[bulk]]` entry
in `states.toml` defers every still-open cell of a tier for a release to one tracking issue; fixture evidence
always wins over it. A fixture cites only the rules it exercises: the gate counts citations and cannot check them,
so review them (a mis-tag is a finding).

The milestone-only baseline is reported separately for comparison with #2080. Old-by-old
cells do not block this release.

## Step 3 — Fill the high-risk gaps

For each high-risk gap, write a fixture that puts **both** features in one program and
asserts a concrete result:

- A positive fixture (`evaluator/…`) when the combination should work — assert the
  runtime value, and set `move_check = true` if either feature is move-related.
- A negative fixture (`typechecking/…`) when the combination should be rejected — assert
  the exact error code and a message substring.
- `spec = ["…"]` tags citing every rule block the fixture exercises, for both features.

If a fixture reveals a **bug** — wrong value, missing rejection, a panic, an internal
error — stop writing fixtures, file an issue (`gh issue create --label bug,severity:<soundness|incorrect|diagnostic>`; add
`regression` if it worked in an earlier tag; milestone `$ARGUMENTS` for a soundness bug or a
regression, otherwise `Backlog`; see `ROADMAP.md` § Bugs),
and note it in the report. Do not fix it inline; it goes through `/start-issue` like any
other. A fixture that documents the bug is committed `skip = "metel-core#N"` so the
corpus records the gap.

Land the fixtures on one issue branch per logical group (`test(#956): v0.13.0
cross-feature fixtures — closures × narrowing`), Tier 3, PR to `develop`.

## Step 4 — Full-tree verification

On the combined `develop` tree, after the fixture branches merged:

```bash
cd metel-interpreter && cargo test --release
cargo clippy --release --lib -- -W clippy::pedantic
cargo build --release -p metel
./target/release/move-check-count metel-interpreter/tests/integration/sources
python3 ../tools/check_doc_examples.py --binary target/release/metel \
    ../README.md ../docs/getting-started/tutorials ../docs/reference/spec
```

- `test result:` lines: zero failures.
- `move-check-count`: `skipped_generic_bodies_user_total` has not risen above its
  baseline (18); `user_move_violations` is 0 or every one is a `skip`-tagged
  documented-bug fixture.
- Doc examples: clean.

## Step 5 — Write the report

`docs/release-notes/integration/$ARGUMENTS.md` in `metel-docs`, committed on a branch
off `main` and merged before `/cut-release` bumps the `docs` gitlink:

```markdown
# Integration testing — $ARGUMENTS

**Session run:** <date> · against `develop` at `<short-sha>` (post-freeze).
**Result:** <PASS — clear to release | BLOCKED — see findings>.

## Features exercised

- <capability> (RFC-NNNN, #issue)
- …

## Interaction matrix

Paste the summary from `python3 tools/feature_matrix.py $ARGUMENTS`, including the
milestone-only baseline, rule-coverage totals and full-registry gate verdict. Include the
blocking rows from `python3 tools/feature_matrix.py $ARGUMENTS --blockers`, with fixture
paths, and any `n/a`/deferred Tier A cells with their reason or issue link.

Also commit the metrics snapshot next to the report and paste the table, with the per-feature rows, into
the report:

```bash
python3 tools/feature_matrix.py "$ARGUMENTS" --json > docs/release-notes/integration/$ARGUMENTS.metrics.json
python3 tools/feature_matrix.py "$ARGUMENTS" --table --per-feature
```

The snapshot is what a later release diffs against; the compact table (without `--per-feature`) is published
with the release in `changelog.md` (`/cut-release` Step 2).

The registry and state file preserve the feature rows and manual dispositions. The script
recomputes fixture evidence each run, so deleted or retagged fixtures automatically reduce
scores and can reopen cells.

## Fixtures added

- `path` — <features>, <what it asserts>
- …

## Findings

- **#N** — <one line>. <fixed on #M | deferred to Backlog>.
- (none) if nothing surfaced.

## Sign-off

All high-risk pairs have a fixture. Full release suite green on `<sha>`. Findings
above are each resolved or deferred. Clear for `/cut-release $ARGUMENTS`.
```

## Step 6 — Bump the gitlink and report back

```bash
git -C docs checkout main && git -C docs pull
git add docs && git commit -m "chore(#<n>): bump docs gitlink — $ARGUMENTS integration report"
```

Then report to the user:

```
## $ARGUMENTS — integration session complete

**Matrix:** <N> pairs · <F> fixtures pre-existing · <G> gaps filled · <B> bugs found.
**Report:** docs/release-notes/integration/$ARGUMENTS.md
**Findings:** #N (fixed), #M (deferred → vX.Y.Z), …
**Verdict:** <clear for /cut-release | blocked on #N>
```

---

## Notes

- The matrix is the deliverable even when every cell is "fixture exists" or "n/a" —
  a milestone that genuinely has no cross-feature risk still produces the report saying
  so, dated, so `/cut-release` has its gate artifact.
- Re-run the session, not just the suite, if new work lands on `develop` after the
  report is written — the freeze in `/cut-release` Step 0 exists so this does not happen,
  but if it does, the report's `<short-sha>` no longer matches and it is stale.
- A finding that needs design rather than a fix: prompt the user to run `/new-rfc`, and
  defer the release-blocking question to them.
- This does not replace `/gap-analysis` (milestone *entry*) or `/cut-release` (release
  *hygiene*). Order: `/gap-analysis` → implement issues → `/milestone-integration-test`
  → `/cut-release`.
