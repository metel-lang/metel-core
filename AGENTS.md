# Metel — Agent Guide

## Project

Metel is a statically typed, expression-oriented language. This repository contains the
shared frontend and the shipped tree-walk interpreter:

- `metel-frontend`: parser, module loading, name resolution, typechecking, typed AST,
  elaboration, and move checking.
- `metel-interpreter`: evaluator, CLI, runtime integration, and test harness.

The interpreter is a first-class product and the semantic reference for the planned
compiler. Do not treat it as disposable compiler scaffolding.

## Repository map

| Path | Purpose |
|---|---|
| `metel-frontend/src/` | Shared language frontend |
| `metel-frontend/docs/typechecker.md` | Typechecker implementation notes |
| `metel-interpreter/src/` | Evaluator and CLI |
| `metel-interpreter/docs/evaluator.md` | Evaluator implementation notes |
| `metel-interpreter/tests/integration/sources/` | End-to-end fixture corpus |
| `docs/` | Public `metel-docs` submodule: spec, RFCs, tutorials, changelog, ADRs |
| `docs/reference/spec/` | Normative language specification |
| `docs/rfcs/` | RFC corpus and lifecycle tooling |
| `docs/architecture/decisions/` | Architecture decision records |

Private strategy and research reports live in the separate
`metel-docs-internal` repository. They are not a submodule of this implementation
repository and are not required reading for ordinary issues. Consult them only when a
task explicitly concerns strategy or research.

Initialize the public docs before a task that needs them:

```bash
git submodule update --init docs
```

## Sources of truth

- Language behavior: `docs/reference/spec/`.
- RFC lifecycle and design history: `docs/rfcs/PROCESS.md` and the RFC file.
- Implementation work and release assignment: GitHub issues and milestones.
- Current code architecture: the crate docs named above and the code itself.
- Versioning/release rules: `RELEASING.md`; release history:
  `docs/release-notes/changelog.md`.

If these disagree, stop and resolve the inconsistency before implementing against it.

## Task workflow

### Start narrowly

1. Read the issue and its explicit blockers.
2. Read only the spec/RFC sections governing the behavior being changed.
3. Reproduce the bug or establish the missing behavior before editing.
4. Locate the relevant symbols with search; read bounded sections before opening an
   entire large module.
5. State the intended change and focused regression test.

Do not re-audit the whole language or dependency graph for a localized issue. Expand
scope only when the repro or code provides evidence that the cause crosses a boundary.
If there is no causal hypothesis after 15 minutes of exploration, stop and report what
is missing instead of continuing an open-ended search.

### Implement

- Preserve the pipeline and typechecker invariants below.
- Reuse an existing mechanism when the adjacent code already expresses the rule.
- Add a focused regression fixture that fails without the change.
- A second concern discovered during the task gets its own issue; do not widen the PR.
- Keep docs and changelog changes paired with language-visible behavior.

### Verification tiers

Use the cheapest tier that can falsify the current edit. Full release verification is a
merge gate, not an inner-loop command.

**Tier 1 — iteration, after each meaningful edit**

```bash
cargo check -p metel-frontend                 # frontend-only change
cargo check -p metel                          # evaluator/CLI change
cargo test --test integration <exact-filter> -- --exact
```

Use the exact new regression test or the smallest relevant unit-test module. Do not run
the full release suite repeatedly while the diff is still changing.

**Tier 2 — handoff/review, once the focused test is stable**

```bash
cargo test --workspace
cargo fmt --check --all
```

For a delegated change, the delegate runs Tier 1 and reports the commands. The reviewing
agent runs Tier 2 after reading the diff. Do not make both agents independently run the
full release gate.

**Tier 3 — pre-merge, exactly once on the final tree**

```bash
cargo test --release --workspace
cargo clippy --release --workspace --lib -- -D warnings -D clippy::pedantic
cargo fmt --check --all
```

Read the `test result:` and Clippy tails. If Tier 3 exposes a defect, fix it, rerun the
focused regression first, then rerun only the failed gate and finally one complete Tier
3 pass. CI runs the same release-level gate.

**Milestone gate — once per release, not per PR.** Tier 3 proves each diff in isolation.
Before a milestone is declared finished, `/milestone-integration-test <version>` exercises
its features *in combination* — the cross-feature cases no single PR's fixtures cover —
and commits `docs/release-notes/integration/<version>.md`. `/cut-release` gates on that
report (its Step 1b). Run order for a release: `/gap-analysis` → implement the issues →
`/milestone-integration-test` → `/cut-release`.

### Clippy suppressions

Fix the warning by default. A `#[allow(clippy::...)]` is acceptable only when the lint
is a false positive, or the fix would be worse than the warning — and then it carries a
`// clippy-allow: <one-line reason>` comment, either trailing the attribute or in the
comment block directly above it. Module-level `#![allow(clippy::...)]` is not accepted
for new code — scope the allow to the item.

`tools/clippy_allow_ratchet.py --check` runs in CI and fails a PR that adds a *bare*
(unjustified) allow beyond the grandfathered counts in `tools/clippy-allow-baseline.json`,
or any new module-level `#![allow]`. A justified `// clippy-allow:` suppression is never
counted and needs no baseline change. When you fix a warning and remove an allow, run
`tools/clippy_allow_ratchet.py --write-baseline` to lock in the improvement;
`--list` (no args) prints the current inventory for gradual burndown (metel-core#882).

Cargo's workspace cache is `/target/` and is intentionally ignored. Do not delete it to
obtain a clean worktree. Disposable worktrees should use `sccache` when available rather
than sharing one writable target directory concurrently.

## GitHub and branch workflow

GitHub Issues are the task source of truth. Milestones are releases; dependencies are
written as `Blocked by #N` / `Blocks #N` in issue bodies.

Normal implementation flow:

1. Branch from current `develop`, never `main`.
2. Use `<type>/<issue>-<slug>` (`feat`, `fix`, `refactor`, `test`, `docs`, `chore`).
3. One issue, branch, and pull request.
4. Rebase onto `origin/develop`; never merge `develop` into the branch.
5. Run Tier 3, open the PR to `develop`, and merge by local fast-forward.
6. `main` moves only when a release milestone completes.

GitHub's hosted merge buttons do not provide the required true fast-forward. After
review:

```bash
git fetch origin develop <branch>
git switch develop
git merge --ff-only origin/<branch>
git push origin develop
```

**Local git hooks (metel-core#1268), one-time per clone:**

```bash
git config core.hooksPath .githooks
```

`commit-msg` rejects Claude/Anthropic attribution; `pre-commit` runs `cargo fmt --check`
plus the two instant text-scan tools (`clippy_allow_ratchet.py --check`,
`check_no_semantic_name_lookup.py`); `pre-push` runs clippy, `cargo test --workspace`, and
refuses to push a merge commit reaching `develop`. Not a substitute for Tier 3 or CI —
branch protection ("Require linear history" on `develop`) is the actual backstop; these
hooks just catch the same classes of mistake earlier, for whoever has them enabled.

"Commit and push directly" means push the completed work to `develop`; it does not
authorize writing to `main`. Only an instruction that explicitly names `main` and
acknowledges its release-only role can override this convention.

Commit format for tracked work:

```text
<type>(#<number>): <description>
```

Use `Closes #N` in the PR body or commit body only when all acceptance criteria are met.
Do not add Claude/Codex attribution trailers.

Detailed mechanics are on demand rather than duplicated here:

- `.claude/commands/start-issue.md`
- `.claude/commands/ship-issue.md`
- `.claude/commands/cut-release.md`
- `.claude/skills/codex-delegate/SKILL.md`

## Documentation and RFC workflow

Public docs changes are committed to the `metel-docs` repository first, then the `docs`
gitlink is updated in the core issue branch. The core release pins an exact public-docs
commit.

RFC stages are directories under `docs/rfcs/`:

```text
0-draft → 1-under-review → 2-accepted → 3-integrated → 4-implemented
                                                ↘ 5-superseded / 6-refused
```

Use the lifecycle tool; do not move RFC files manually:

```bash
python3 docs/rfcs/tools/rfc.py check
python3 docs/rfcs/tools/rfc.py transition <id> --to <stage> ...
```

Implementation of an RFC begins only after `3-integrated`. From that point the RFC has
one umbrella `impl_tracking` issue and an `impl_status`. When implementation finishes,
transition it to `4-implemented` in the same work.

The specification contains current rules, not design rationale or issue history. Put
rationale in RFCs/ADRs and issue state on GitHub. Add or update the changelog when a
language-visible change lands, not at the end of the release.

## Architecture invariants

The product pipeline is:

```text
.mtl root
  → module loader
  → name resolver
  → path normalizer
  → coherence
  → typechecker
  → move checker (when enabled)
  → elaborator
  → evaluator
```

Do not create a shortcut entry point that silently skips stages.

- `pipeline::parsing::module_loader::load_root` produces a topologically ordered module graph.
- `pipeline::name_resolution::name_resolver::resolve` owns import scopes, visibility, and re-exports.
- `pipeline::path_normalization::normalize` rewrites qualified paths before typechecking.
- `pipeline::type_checking::check_graph` consumes normalized modules and resolved names.
- Cross-module public APIs require explicit annotations.
- A boundary change requires architecture-doc review and usually an ADR.

## Type-system invariants

The typechecker has two passes:

- Inference emits constraints and solves substitutions. It does not build typed AST.
- Construction reads solved results and builds typed AST. It does not infer or mutate
  substitutions.

If a task appears to require blurring this boundary, stop and surface the architectural
choice. Prefer recording more resolved facts in the inference result for construction to
consume rather than repeating the semantic decision in both passes.

Sensitive rules:

- `Substitution::compose` is ordered; verify direction at every changed call.
- `Never` is a bottom type; typechecking alone cannot prove runtime behavior.
- `Perhaps` and `Result` are distinct `Type` variants; normalize through established
  conversions where named types are handled uniformly.
- Apply substitutions before `infer_type_to_type`; unresolved variables are errors.
- `crate::data::types::Type` contains no type variables. Abstract parameters are
  `InferType::Var(TypeVar)`.
- Generic instantiation follows `instantiate_scheme_for_call`: fresh variables,
  initial substitution, unification, composed substitution, then extraction.
- Imported schemes must reach both inference and construction.
- `construct_block` must receive the expected tail type when one exists.

For typechecker changes, use `.claude/commands/review-typechecker.md` after the focused
regression passes. Add an ADR when multiple reasonable architectural choices exist, a
prior decision is reversed, or a workaround would surprise a future contributor.

## Review discipline

Read the actual diff before trusting a green suite. In particular check:

- fallback arms that silently copy, ignore, or erase a new variant;
- workarounds added only to make a fixture pass;
- a helper that is never called from the fixture's `main`;
- inference/construction behavior that changed on only one side;
- specification examples that no longer compile.

For a substantial type-system or architecture change, obtain an adversarial review whose
job is to produce runnable counterexamples, not a summary. Reproduce findings before
fixing them and keep review separate from implementation.

## Stop conditions

Stop and ask when:

- the spec is ambiguous in a way that changes behavior;
- a required RFC is below `3-integrated`;
- a dependency is closed but its code does not provide the assumed contract;
- multiple architectural choices have materially different consequences;
- the task would require destructive cleanup, unrelated edits, or broader authority;
- a substitution/pass-boundary change breaks an existing test.

Never use destructive git commands to obtain a clean tree, rewrite shared history, create
merge commits, silently change RFC lifecycle state, or implement behavior absent from the
spec.
