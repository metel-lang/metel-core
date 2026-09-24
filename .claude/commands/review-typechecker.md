# /review-typechecker

Review a change to any file under `src/pipeline/type_checking/` (including its nested
`typeinference/` submodule) before committing.
Work through every checklist item. Report pass/fail for each section. Do not skip items.

---

## 1. Test suite

```bash
cargo test --test integration <exact-regression-filter> -- --exact
cargo test --workspace
```

- [ ] The focused regression passes before the full workspace suite is run
- [ ] The workspace tests pass — zero failures, zero ignored regressions
- [ ] If a previously-passing test now fails: **STOP**. A shared invariant is broken. Diagnose before proceeding.

This is the handoff tier. Do not run release tests or release Clippy here; those run
once in `/ship-issue` after the review checklist and diff are final.

---

## 2. Pass boundary

The typechecker has two strictly separated passes:

- **Pass 1 (inference)** — `infer_*` functions. Pushes constraints, populates `ctx.subst`. No TypedAST construction.
- **Pass 2 (construct)** — `construct_*` functions. Reads `ctx.subst`, builds TypedAST. No inference, no constraint pushing.

Check the changed code:

- [ ] No `construct_*` calls inside `infer_*` functions
- [ ] No `infer_*` calls inside `construct_*` functions (exception: `infer_type_to_type` is a pure converter, not inference)
- [ ] No `ctx.subst` mutations inside `construct_*`

If any box is unchecked: STOP and ask. The pass boundary must not be blurred.

---

## 3. Substitution composition

`Substitution::compose` is **ordered**: `a.compose(b)` = apply `b` to `a`'s values, then merge. This is `a ∘ b` (b first). Reversing arguments changes semantics silently.

For each new `compose` call:

- [ ] Confirm which substitution represents "earlier" constraints and which represents "later"
- [ ] Confirm the order matches the intended composition direction
- [ ] Grep for any call site where `local_subst = local_subst.compose(&s)` was changed to `local_subst = s.compose(&local_subst)` or vice versa — the difference is non-obvious

---

## 4. Generic instantiation pattern

The canonical pattern is `instantiate_scheme_for_call`. Any new site that instantiates a generic type (struct literal, enum variant, function call) must follow it:

1. For each formal type param in `EnumInfo`/`StructInfo`, create a **fresh** `InferType::Var(ctx.gen.fresh())`
2. Build `init_subst` binding each formal `TypeVar` → its fresh var
3. Apply `init_subst` to all field/param types to get instantiated types
4. Unify instantiated types against actual types, composing into `local_subst`
5. For each fresh var: apply `local_subst` — if still `Var`, fall back to annotation hint; if still unresolved, return E0002

- [ ] Any new generic instantiation site follows all five steps
- [ ] No site reuses the same fresh vars across multiple call/literal sites (each site must create its own)
- [ ] `ctx.gen.fresh()` is called (not a reused `TypeVar`)

---

## 5. Type normalisation

`Type::Perhaps(T)` and `Type::Result(T, E)` are distinct `Type` variants — they do **not** match `Type::Named`. Code that needs to handle all named types uniformly must route through `type_to_infer()` first.

- [ ] Any new pattern match on `Type` that handles `Named` also handles `Perhaps` and `Result` (or routes through `type_to_infer`)
- [ ] Any new hint extraction from `expected_ty` uses `type_to_infer(ty)` and then matches `InferType::Named(name, args)`

---

## 6. `infer_type_to_type` call sites

`infer_type_to_type` requires all `InferType::Var` cases to be resolved first. Calling it on an unresolved var silently produces a wrong type or panics.

- [ ] Every new `infer_type_to_type` call has a `Span` available at the call site
- [ ] Every new `infer_type_to_type` call is preceded by substitution application that resolves any vars
- [ ] No call passes a raw `InferType::Var` unless the caller handles the resulting error

---

## 7. `expected_ty` threading

`construct_block` takes `expected_tail_ty: Option<&Type>`. This must carry the function return type (or annotation type) so that fieldless generic variants at block tails can resolve their type args.

- [ ] Any new `construct_block` call site passes the correct `expected_tail_ty`:
  - Function body → function return type
  - `if`/`loop` expression branch → the expression's own `expected_ty`
  - Statement position (no value needed) → `None`
- [ ] `construct_expr` for `If` propagates `expected_ty` into both `then_branch` and the `else_branch` `construct_block` calls
- [ ] No new call site passes `None` where a concrete type is available

---

## 8. `Never` and test coverage

`Never` unifies with any type. A test that annotates `: Int` and receives a `Never`-typed expression will pass the typechecker silently. Typechecking tests **cannot** verify that a loop/return/break produces the correct runtime type.

- [ ] If the change affects how `break`, `return`, or diverging expressions are typed: confirm there is a corresponding evaluator test (or open a tracking issue if the evaluator is not yet available)
- [ ] Positive typechecking tests for diverging expressions are acceptable as regression guards, but their passing is not proof of correctness

---

## 9. Code quality

- [ ] **Comments**: no new comment describes *what* the code does — only the non-obvious *why* (a hidden constraint, a subtle invariant, a workaround). Remove any comment that just restates the function or variable name.
- [ ] **Nesting depth**: no new function body exceeds 3 levels of indentation in its happy path. If a match arm contains another match or a for loop with an if inside, extract a helper.
- [ ] **File size**: `inference.rs` and `construction.rs` have not grown significantly past their current sizes without a corresponding split or extraction. Flag if either file exceeds ~1100 lines.
- [ ] **Concern separation**: new helpers belong to exactly one pass (infer or construct). A helper that takes both `InferContext` and `ConstructCtx` parameters is a sign of blurred concerns.

---

## 10. Test coverage

- [ ] Every new happy-path behavior has at least one passing typechecking test (a `.mtl` fixture under `tests/integration/sources/typechecking/`, or a unit test under `tests/unit/`)
- [ ] Every new error path (new `ErrorCode` emission or new rejection branch) has at least one negative test that asserts the error is produced
- [ ] If a test was added: confirm it actually exercises the changed code path, not a pre-existing path that happens to pass

---

## 11. Implementation notes

- [ ] If the change adds or removes a known limitation, update the **Known Limitations** section of `metel-interpreter/docs/typechecker.md`
- [ ] If the change introduces a new invariant, pattern, or non-obvious constraint (e.g. a new required ordering, a new fallback strategy), add it to the relevant section of the typechecker doc
- [ ] If an existing entry now describes something that no longer exists (removed function, resolved limitation), remove or update it

---

## 12. Summary

State the result for each section (pass / fail / n/a) and list any blockers. If any section fails, do not commit — resolve the issue first.
