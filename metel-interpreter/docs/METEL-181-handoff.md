# METEL-181 — std::core unification: status

**Branch:** `sprint/22-stdcore` (isolated worktree; `sprint/22` is untouched and green).
**Suite at HEAD:** 402 integration + 46 lib tests, green. CLI verified.

## Status: COMPLETE

All three remaining points are implemented and committed on this branch:

### 1. The full core surface lives in `stdlib/core.mtl`
- `Option`/`Result` enums, the `Display`/`From<S>`/`Iterable<T>` aspects,
  `struct List<T>` + its seven native methods, the 13 primitive Display impls,
  the full numeric `From` cross-product, and `Char ↔ u32` — all declared in
  the embedded std::core source, bound to Rust hosts via the closed `NativeKey`
  enum (27 keys).
- `build_registry` derives every module's builtin registry by running
  `register_program_decls` over `stdlib::core_program()`; native methods on
  generic structs are registered as polymorphic schemes over the struct's type
  params; the prelude derives free-function and `List::new`/`List::from`
  joined-key schemes from the same source.
- Deleted: the resolver's std::core pub_surface injection, the hand-built
  registry entries, the `from_int!`/`from_float!` runtime cross-product, the
  GlobalExports std::core seed. `StdPrelude` renamed to `CorePrelude`
  (fully derived; kept for the single-program path, which loads no modules).
- Still hand-registered (intentional): Range/RangeInclusive Iterable impls
  (runtime ranges are intrinsic) and the String/array `len` pattern methods
  (receiver shapes, not named types).

### 2. EmbeddedStdlibProvider is the default
- `load_root` reads embedded `std::` modules through the provider;
  `validate_std_namespace` rejects user-supplied `std::` paths.

### 3. Overload dispatch by SymbolId (METEL-180 end state)
- Each overloaded definition gets a unique SymbolId (range `0x4000_0000+`,
  `symbols::OVERLOAD_SYM_START`). Construction stamps the selected candidate
  into `TypedExpr::Call::callee_id`; the evaluator registers overloaded
  definitions in a SymbolId-keyed registry and dispatches through it.
- `overload::mangle`/`type_mangle` and all name rewriting are deleted.
  Overloads never enter the name-keyed scheme env or the export surface.
- Struct/type/enum registry rekeying stays OUT (follow-up: METEL-185).

## Key invariants (for future work)
- TypeVar ranges: registry/module gens ~0+, CorePrelude 10_000+,
  `construct_generic_body` 1_000_000+, exported schemes 2_000_000+
  (`refresh_scheme_for_export`); `Substitution::bind` drops identity bindings.
- `stdlib/core.mtl` + `NativeKey` are the single source of truth for the core
  surface; the typechecker registry, the prelude, and the runtime all derive
  from `stdlib::core_program()`.
- Fixtures: 75 (primitive aspect impls), 82 (embedded Display/From impls),
  76 (overload SymbolId dispatch),
  `module_semantics/generic_native_scheme_no_typevar_collision`.
