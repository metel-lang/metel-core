# /milestone-integration-test

Exercise a completed milestone's features **in combination**, before `/cut-release`.

**Arguments:** `$ARGUMENTS` — the version, e.g. `v0.13.0` (the numbered release milestone; a
release built from a theme is renamed to its version before this session, see `ROADMAP.md`).

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

## Step 1 — Enumerate the milestone's language-visible surface

```bash
git checkout develop && git pull --recurse-submodules
git log --oneline $(git describe --tags --abbrev=0 origin/main)..develop
python3 docs/rfcs/tools/rfc.py check
```

List every **feature** the milestone shipped that a program can observe:

- Every RFC that reached `4-implemented` this milestone
  (`grep -l '^target: '$ARGUMENTS docs/rfcs/4-implemented/*.md`, cross-checked against
  each RFC's `impl_status`).
- Every entry in `docs/release-notes/changelog.md`'s in-progress `## $ARGUMENTS` section
  that changes syntax, type-checking, move-checking, or runtime behaviour — including the
  "Fixes:" block, since a fix changes observable behaviour too.
- Any `3-integrated` RFC targeting this milestone that shipped in slices (its slice
  issues are closed) — the slice is a feature even though the RFC file has not moved.

Each becomes one row/column label in Step 2. Name them by capability, not RFC number,
so the matrix reads (`written fn types move-only`, not `RFC-0166`).

## Step 2 — Build the interaction matrix

Form the N×N grid of Step 1's features. The diagonal is single-feature (already covered
per-PR — skip). For every off-diagonal **unordered pair**, decide one of:

- **Fixture exists** — a corpus fixture under
  `metel-interpreter/tests/integration/sources/` already exercises both features in the
  same program. Record its path.
- **No interaction possible** — the two features cannot appear in one program in a way
  that could interact (e.g. a pure-syntax parse rule and a runtime builtin). Record a
  one-line justification.
- **Gap** — neither. This pair needs a new fixture.

A pair is **high-risk** (must be filled, not just noted) when both features touch the
same subsystem:

| Subsystem | Features that touch it |
|---|---|
| move / ownership | narrowing, widening, `--move-check`, written fn types move-only, closure capture lists, closure mutation axis |
| type inference / unification | row narrowing, row bounds, type aliases, first-class generic functions, function-type multiplicity widening |
| closures | every closure-cluster RFC, pipe notation, written fn types |
| pattern matching | struct patterns, row-bounded `..`, parenthesized scrutinee |

Any gap where a row and a column are both in the same subsystem row above is high-risk.

## Step 3 — Fill the high-risk gaps

For each high-risk gap, write a fixture that puts **both** features in one program and
asserts a concrete result:

- A positive fixture (`evaluator/…`) when the combination should work — assert the
  runtime value, and set `move_check = true` if either feature is move-related.
- A negative fixture (`typechecking/…`) when the combination should be rejected — assert
  the exact error code and a message substring.
- `spec = ["…"]` tags citing every rule block the fixture exercises, for both features.

If a fixture reveals a **bug** — wrong value, missing rejection, a panic, an internal
error — stop writing fixtures, file an issue (`gh issue create`, milestone `$ARGUMENTS`),
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

| | A | B | C |
|---|---|---|---|
| **A** | — | fixture / n-a / GAP→#N | … |
| **B** | | — | … |
| **C** | | | — |

Legend: fixture `path`, `n/a: <reason>`, `GAP→#N` (filled, fixture `path`),
`BUG→#N` (documented, `skip`-tagged fixture `path`).

## Fixtures added

- `path` — <features>, <what it asserts>
- …

## Findings

- **#N** — <one line>. <fixed on #M | deferred, re-milestoned to vX.Y.Z>.
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
