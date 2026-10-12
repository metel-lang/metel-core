# Typechecker Implementation Notes

> Status: v0.8.1 — elaboration support added (METEL-152): `check_graph` now threads `names.symbols` through `check_impl` → `construct_program` → `ConstructCtx` so that `construct_impl_decl` can populate `TypedImplBlock::aspect_id`.
>
> Status: v0.10.0 (in progress) — `Bound{polarity, aspect, assoc_bindings}` replaces bare `TypeExpr` in `GenericParam.bounds`/`WhereClause.constraints` (issue #233); `ImplBlock` gained `polarity`/`generics`/`where_clause`/`assoc_type_defs`; `AspectDecl` gained `assoc_types`; `TypeExpr::Projection` added for `T::AssocType`. See "Polymorphic Function Bodies" below for how impl-block-own-generics and generic type-argument recovery from runtime values (issue #267, ADR-0043) fit into construction-at-call-time.

---

## Pipeline Position

### Single-module (legacy `check`)

```
untyped AST  ──►  check()  ──►  TypedProgram
                    │
                    ├─ Pre-pass: register builtins, enums, hoist names
                    ├─ Pass 1:   infer — emit constraints, solve
                    └─ Pass 2:   construct — consume resolved facts, build TypedAST
```

### Multi-module (v0.6.0 `check_graph`)

```
NormalizedModuleGraph + ResolvedNames
       │
       ▼  (for each module in topological order)
  ┌─────────────────────────────────────────────────────┐
  │ build_import_schemes — pull pub schemes from         │
  │   GlobalExports for this module's imports            │
  │                                                      │
  │ check_impl(program, imported_schemes, base_registry) │
  │   ├─ Pre-pass: seed imports, register builtins, hoist│
  │   ├─ Pass 1:   infer (same as single-module)         │
  │   └─ Pass 2:   construct (scheme_env includes imports)│
  │                                                      │
  │ filter_pub_schemes — extract pub names → GlobalExports│
  └─────────────────────────────────────────────────────┘
       │
       ▼
  TypedModuleGraph (one TypedModule per input module)
```

Entry points:
- `pipeline::type_checking::check(program) -> Result<TypedProgram>` — single-module legacy path
- `pipeline::type_checking::check_graph(graph, names, std_prelude) -> Result<TypedModuleGraph>` — multi-module path (v0.6.0)

---

## Module Structure

| File | Responsibility |
|---|---|
| `mod.rs` | `check()` / `check_graph()` entry points; `CorePrelude`, `GlobalExports`, `check_impl` |
| `registry.rs` | `build_registry` (drives `populate_schemes_from_embedded_core` + `register_program_decls`), `build_concrete_*_env`; registers aspect declaring modules for elaboration |
| `overload/mod.rs` | `build_overload_table`, `core_overload_table()`, `select`, `no_match_error`; SymbolId allocation for overload sets |
| `inference/mod.rs` | Pass 1 orchestration, signature validation, block/statement traversal, and expression helpers |
| `inference/declarations.rs` | Declaration, function, impl, and default-method inference and generalization |
| `inference/expressions.rs` | The exhaustive expression constraint-emission dispatch |
| `inference/patterns.rs` | Match and pattern constraint emission, record-row pattern access, and built-in pattern method typing |
| `inference/lowering.rs` | Pre-inference lowering for `impl Aspect` parameters and associated-type projections |
| `handoff/mod.rs` | `ResolvedInferenceFacts`, immutable solved decisions passed from inference to construction |
| `handoff/abstract_signature/` | Binder-local freezing of generic signatures, retained facts and staged typed bodies (ADR-0063) |
| `construction/mod.rs` | Pass 2 context, block/statement construction, literals, coercions, and places |
| `construction/declarations.rs` | Declaration, function, impl, and default-method typed-AST construction |
| `construction/expressions.rs` | The exhaustive expression typed-AST dispatch |
| `construction/patterns.rs` | Pattern binding, match construction, exhaustiveness, and control-flow result merging |
| `construction/calls.rs` | Calls, generic instantiation, method dispatch, and bound validation |
| `conversions.rs` | `type_expr_to_infer`, `infer_type_to_type`, `resolved_to_type`, `type_to_infer` |

The inference engine lives in `pipeline/type_checking/type_engine/` (type vars, unification, substitution, constraints, schemes). The typechecker modules in `pipeline/type_checking/` walk the AST and drive that engine.

---

## Theory Background

### Type Variables and InferType

During inference, types may be partially unknown. **Concrete types** (`Type` enum) are fully resolved: `Int`, `String`, `fun(Int) -> String`. **Inference types** (`InferType` enum) may contain type variables — placeholders that get unified with concrete types as more information becomes available:

```
?t0, ?t1, ?t2   — type variables (generated fresh for each unknown)
fun(?t0) -> ?t1 — an InferType containing type variables
```

Type variables satisfy an **occurs check**: `?t0` cannot be unified with `Array(?t0)`, which would create an infinite type.

### Unification

Unification makes two types equal by binding type variables:

```
unify(Int, Int)                        → ok, already equal
unify(?t0, Int)                        → ok, bind ?t0 = Int
unify(?t0, ?t1)                        → ok, bind ?t0 = ?t1
unify(Int, String)                     → error, incompatible
unify(fun(?t0) -> ?t0, fun(Int) -> Int) → ok, bind ?t0 = Int
unify(?t0, Array(?t0))                 → error, occurs check
```

### Substitution and Constraints

A **substitution** is a map from type variables to types (`?t0 → Int`, `?t1 → String`). Applying a substitution replaces all variables in a type with their bindings.

Rather than unifying types immediately as the AST is walked, the inference system collects **constraints** (equality relations between `InferType`s, each tagged with a source span) and solves them in batch. Batch solving handles complex interdependencies and produces better error messages.

### Let-Polymorphism and Type Schemes

A **type scheme** is a type with universally quantified variables: `∀α. α → α` (the identity function — works with any type). In code:

```rust
pub struct TypeScheme {
    pub quantified_vars: Vec<TypeVar>,
    pub ty: InferType,
}
```

When `let id = fun(x) { x }` is inferred:
1. Infer the body — parameter `x` gets fresh variable `?t0`, function type is `fun(?t0) -> ?t0`
2. **Generalize**: identify free type variables not shared with the outer environment; `?t0` is free → scheme `∀?t0. fun(?t0) -> ?t0`
3. Bind `id` to this scheme in `poly_env`

When `id` is **used**, the scheme is **instantiated** with fresh type variables — each call site gets an independent copy:

```
id(42)      → instantiate to fun(?t1) -> ?t1, unify ?t1 = Int  → id(42) : Int
id("hello") → instantiate to fun(?t2) -> ?t2, unify ?t2 = String → id("hello") : String
```

### The Generalization Boundary: Why `env_fvs` Matters

Generalization must only quantify type variables that are *truly local* to the function. If a variable is shared with the outer scope, quantifying it is unsound.

```metel
fun f(x) {
    let g = fun(y) { x };   // g's type: fun(?t1) -> ?t0 where ?t0 is x's type
}
```

`?t1` is local to `g` — safe to quantify. `?t0` is shared with `f`'s scope — quantifying it would let different calls to `g` return different types, but `x` has one concrete type per call to `f`. The typechecker snapshots the environment's free variables (`env_fvs`) before entering the function body and only quantifies variables absent from that set:

```
fun_ty   = fun(?t1) -> ?t0
env_fvs  = {?t0}                          ← x's type is already in scope
scheme   = ∀?t1. fun(?t1) -> ?t0          ← ?t0 left free, not quantified
```

The snapshot is taken before pushing the function's parameter scope — the right moment, capturing what the surrounding context has already committed.

### Never Type

`InferType::Never` (the bottom type `!`) unifies with any type. Diverging expressions — `return`, `break`, `continue`, and infinite `loop` with no reachable `break` — produce `Never`. This lets the constraint solver treat dead branches as compatible with any expected type.

### Rank-1 Limitation

The HM algorithm infers types at rank 1: `∀` only at the outermost level. Higher-rank polymorphism (e.g. a function that accepts a polymorphic function as an argument) requires decidability-breaking extensions and is not supported. The practical consequence: function arguments are unified as monotypes; passing a polymorphic function as an argument works only if the call site knows the concrete instantiation.

---

## Pre-Pass

Four pre-inference steps run before Pass 1:

1. `build_registry` (via `TypeDefinitionRegistry`) — registers types, aspects, and impls. It first calls `populate_schemes_from_embedded_core` to derive schemes for all `std::core` declarations (including `print`/`println`/`assert` with their aspect bounds, and `String::len` as a derived method entry), then calls `register_program_decls` for the user module. The old hand-maintained `register_builtins` step no longer exists — every stdlib item is derived from the embedded `core.mtl` source (ADR-0039).
2. `projections::check` — walks type-bearing annotations and bounds against the completed registry. It reports unresolved type and aspect names (and malformed record projections) before inference can turn them into stand-in types and emit a misleading unification error. Its scope carries generic parameters, valid `Self` positions, and block-local nominal declarations.
3. `build_overload_table` — groups same-name `fun` declarations into overload sets; assigns each definition a process-unique `SymbolId` from the `OVERLOAD_SYM_START` range. Overloaded names are not registered in the scheme env and are resolved by exact-match candidate selection in Pass 1 (ADR-0038).
4. `hoist_fun_decls` — walks top-level non-overloaded `FunDecl`s and pre-registers each with a fresh type variable in both `ctx.mono_env` and `ctx.poly_env`. Enables forward references, mutual recursion, and shadowing of `std::core` names. Native decls are hoisted with bounds derived from their annotated parameter types.

`hoist_fun_decls` is also called at block entry in `infer_block`, so nested functions support forward references within their block.

Struct and enum declarations follow **lexical scope rules** matching Rust's model:

- `build_registry` registers only top-level `struct`/`enum` declarations. These are globally visible for the entire compilation unit.
- Struct/enum declarations inside function bodies (or any nested block) are registered at block entry by `infer_block` using `TypeDefinitionRegistry::push_struct_scope` / `register_struct_fields` / `pop_struct_scope`. On scope exit, all names registered in that scope are removed from the registry.
- `construct_block` in Pass 2 mirrors this: it pushes a new struct scope, builds concrete field types from the substitution, and pops on exit.
- A locally-declared struct is **not visible outside its enclosing block**. Two functions may declare structs with the same name without collision.

---

## Pass 1 — Type Inference

**Modules:** `type_engine/mod.rs` (engine) + `inference/mod.rs` (AST walkers)

### Environment Structure

```
InferContext {
    mono_env: Vec<HashMap<String, (InferType, bool)>>  // scope stack, innermost last
    poly_env: Vec<HashMap<String, TypeScheme>>           // scope stack, mirrors mono_env
    constraints: Vec<Constraint>                        // accumulated equality constraints
    var_gen: TypeVarGenerator                           // globally unique TypeVar allocator
    registry: TypeDefinitionRegistry                    // pre-built struct/enum/method/aspect-impl registries
    current_return_type / current_break_type            // context for return/break inference
    current_type_params: HashMap<String, TypeVar>       // active generic param map (see below)
}
```

**`current_type_params` invariant:** set to the enclosing generic function's `name → TypeVar` map for the duration of `infer_fun_decl` / `infer_impl_method` body inference, and restored to the caller's map afterward via `swap_type_params`. Empty at top level and inside non-generic functions. All type annotations inside a function body (`let`, `var`, `for`-init, closure params) must resolve through `ann_to_infer(ann, ctx)` rather than the bare `type_expr_to_infer(ann)` so that param names resolve to their TypeVars instead of `Type::Named`.

**Row decomposition facts:** function and impl-method body scopes install typed
`where` equations and open-parameter decompositions, together with their negative
row bounds. A named open-parameter tail is recorded as a remainder derivation
from the parameter's value type, so it remains available at calls even when the
body only destructures it. Intermediate rows are quantified with the scheme;
construction backfills chains independently of quantifier order. Following a
decomposition must retain its final opaque tail;
presence-only bounds do not enumerate that tail. Unification treats `{ ..R }`
as `R` before variable binding, avoiding a false occurs check on this identity.
Every source of a shared row tail remains a separate derivation, so two
parameters cannot silently infer incompatible rows for the same `R`. Scheme
instantiation reserves IDs beyond the scheme's own variables before allocating
its fresh copies; imported registry IDs must not overlap the renaming range.

`poly_env` takes precedence over `mono_env` in `ctx.lookup()`. Poly entries are automatically instantiated with fresh type variables on each lookup (let-polymorphism).

### Constraint Emission

Each `infer_expr` call returns an `InferType` and may push zero or more `Constraint`s into `ctx.constraints`. Constraints are not solved inline — they accumulate and are solved in batch.

### Inline Solve-and-Generalize (Functions)

`infer_fun_decl` solves accumulated constraints immediately after inferring the function body, generalizes the function type, and re-binds it as a `TypeScheme` in `poly_env`. This is essential for:
- Let-polymorphism: the function's type scheme can be instantiated fresh at each call site
- Mutual recursion: the pre-hoisted mono binding is unified with the inferred type before generalization

The same constraints remain in `ctx.constraints` after the inline solve; the final `ctx.solve()` at the top level re-solves the same list (idempotent).

### Eager Partial Solves

A few inference cases call `ctx.solve()` eagerly to determine structural type information before emitting further constraints:

- `Expr::ForIn`: resolves the iterable type to decide Array vs Range
- `Expr::FieldAccess`, `Expr::MethodCall`, `Expr::TupleAccess`: resolves the receiver type to look up fields/methods

These partial solves are read-only (they produce a `Substitution` value but don't modify `ctx.constraints`). They are a pragmatic workaround for the fact that field/method lookup requires knowing the concrete type name — a fundamental limitation of constraint-only inference.

### Incremental Constraint Solving (v0.8.2)

`InferContext::solve()` now caches the solved substitution for the already-seen
prefix of `ctx.constraints` and only processes newly appended constraints on the
next call. This is valid because inference only ever appends constraints; it
does not rewrite or remove earlier ones.

This matters because generic-heavy inference triggers many eager partial solves.
Re-solving the full constraint list on every call was the dominant cost in the
`0.8.2` benchmark baseline. The cache keeps the behavior the same while making
repeated solves proportional to the number of new constraints rather than the
entire accumulated list.

The invariant is:

- constraints are append-only during a typecheck run
- cached substitutions may be reused only for the already-solved prefix
- `default_literal_vars(...)` remains a caller-side post-processing step and is
  not stored in the cache

### Mutability Enforcement

Binding mutability is tracked as a boolean flag in `mono_env`: `HashMap<String, (InferType, bool)>`. `bind_mono(name, ty, is_mutable)` stores the flag. `lookup_for_write(name, span)` retrieves the binding and returns `T0006` if `is_mutable` is false.

Three write sites call `lookup_for_write` during Pass 1:

1. **Direct assignment** (`Expr::Assign { target: Ident(x), .. }`) — checked directly.
2. **`&var x`** (`UnaryOp::RefMut` where the operand is `Ident`) — checked before returning `MutPointer(T)`.
3. **Field assignment** (`Expr::FieldAssign`) — the object is inferred first to resolve its type. If the object type is `MutPointer(T)` (auto-deref field assign), the binding check is skipped entirely. Otherwise, `root_binding_for_write` walks the object chain (`FieldAccess → Index → Ident`) to find the root binding and calls `lookup_for_write` on it. Chains ending in `UnaryOp::Deref` also return `None` from `root_binding_for_write` and are exempt.

Method `self` parameters: `self` in an `&var self` method is bound with `is_mutable = true` regardless of the `Param::mutable` flag (which the parser always sets to `false` for receivers). This is handled at `infer_impl_method` and `infer_default_aspect_method` with `p.mutable || matches!(p.receiver, Some(ReceiverKind::RefMut))`.

### Type Ascription (`:` Operator)

`e : T` is a pure inference hint. Inference:
1. Infers the inner expression type `inner_ty`.
2. Converts the annotation `T` to an `InferType` via `type_expr_to_infer`.
3. Adds a constraint `inner_ty ~ ascribed_ty`.
4. Returns `inner_ty` (not the annotated type directly).

The constraint propagates the annotation into the solver without changing control flow. In Pass 2, the ascription node is **erased**: `construct_expr` resolves the annotation to a concrete `Type` and constructs the inner expression with that type as the expected-type hint. No `TypedExpr::Ascribe` variant exists — ascription has zero runtime cost.

---

## Pass 2 — Construction

**Modules:** `construction/mod.rs` and its sibling `construction/` submodules

Pass 2 re-walks the untyped AST with:
- `subst: &Substitution` — the final solved substitution from Pass 1
- `scheme_env: &SchemeEnv` — generalized type schemes for user-defined functions
- `ResolvedInferenceFacts` — immutable concrete decisions made by Pass 1
- `ConstructCtx` — a stripped-down context with concrete `Type` values (no inference)

Construction uses the solved substitution to instantiate schemes and turn annotations
into concrete types, but does not receive mutable inference state. Decisions that Pass 1
must communicate are converted to `Type` while creating `ResolvedInferenceFacts`; for
example, an inferred closure return type is resolved once at this boundary and then
copied into the typed closure. Polymorphic closures intentionally have no single
concrete return fact: they are omitted and reconstructed per call site by the existing
generic-body path. This is the current interpreter compatibility path, not the intended
compiler boundary: frontend monomorphization must eventually replace
`FunBody::Generic` and `GenericClosure` bodies with concrete typed specializations
before evaluation or code generation. No constraints are emitted and the final
substitution is never mutated.

### Responsibility and retained overlap

Inference owns constraint generation, eager structural lookup needed to continue
inference, closure return-type decisions, and explicit capture-list completeness.
The pure AST free-use walker is shared with construction: generic bodies defer
construction, but a missing capture must be rejected before any call, not become
an `I0010` during reconstruction. Only bindings below the inference environment's
module scope require capture items; module-level declarations do not.
Construction owns typed-AST shape,
concrete call instantiation, coercion nodes, runtime method-dispatch metadata, pattern
bindings, and exhaustiveness diagnostics. Lowering is a pre-pass and does not infer or
construct typed nodes.

Some traversal overlap remains deliberately. Method calls are inspected during
inference to constrain receivers and arguments, then resolved against concrete types
during construction so the typed AST can carry dispatch metadata and inserted
coercions. Generic call schemes are likewise instantiated in both passes for different
outputs: constraints in Pass 1 and a monomorphic typed call in Pass 2. Removing this
overlap safely requires frontend monomorphization and a typed intermediate
representation that records complete call resolution, not exposing mutable inference
internals to construction. Bound
satisfaction itself remains centralized in the registry/type-inference queries rather
than being independently reimplemented by each traversal.

### Polymorphic Call Sites

When a call site resolves to a polymorphic callee (present in `scheme_env` but not in `ConstructCtx.env`), `construct_call` calls `instantiate_scheme_for_call`, which:
1. Instantiates the scheme with fresh type variables
2. Unifies the instantiated param types against the concrete argument types
3. Returns the concrete `Fun` type for the specific call

### Polymorphic Function Bodies

ADR-0063 introduces a parallel definition-time handoff under #273. Inference
records expression types, ordinary instantiated call contracts, selected nominal
field identities and the active aspect arguments; the final substitution
is applied before construction freezes legitimate generic variables into
`AbstractParameterId { binder, index }`. Explicit positions follow source order,
not solver allocation order. Source spans join temporary tables only; retained
references use frozen binding identities.

Generic free functions currently retain abstract signatures and parameter facts,
plus a staged body preparation for bindings and projected assignment to named
fields, tuple slots, and explicit dereferences.
Annotated local bindings retain their solved declared types. An exact match
with the initializer needs no coercion operation; differing types remain pending
until their read-copy, reborrow or erasure facts can be retained explicitly.
Assignment targets carry their solved type and field-selection evidence;
indexed and compound assignments
remain pending. The body also retains record/nominal construction, nominal
residual projections, closures with typed capture-entry states and explicit capture modes,
control flow, ordinary calls, borrows and field/tuple projections. Call contracts preserve
parameter passing modes and callable axes; places retain a `BindingId` root and
the shared ownership projection algebra. Temporary borrows materialize storage
and remain distinct from borrowing an existing place. Nominal fields carry the
identity selected by inference; structural and row-granted fields retain their
typed evidence. A name-keyed generic call contract alone cannot establish the
contract of a shadowing local callable. Aspect methods selected through a
declared generic bound retain their instantiated contract, receiver mode and
resolved aspect identity. The solved method-generic arguments remain in that
contract, so an enclosing declared bound such as `U: Copy` is available to
ownership analysis without reconstruction.
For a blanket implementation (`extend<T> T: Aspect`), the target is frozen as
that definition's abstract parameter rather than a synthetic nominal name, so
the body can be checked directly and its move diagnostics retain the receiver.
Record-pattern match arms retain their selection. An open record bound carries
its declared fields plus an opaque self tail, allowing a trailing `..` with no
remainder binding to discard fields without representing the row as closed.
For a nominal `record`, the retained declaration identity instantiates the
declared field template; its fields retain their `FieldId` selections rather
than being re-found by label in the ownership pass.
Missing selection/coercion facts or unresolved associated arguments produce
`Pending`, never invented types or an ownership verdict. Move checking consumes
supported retained free-function and impl-method bodies directly and records
their spans in
`checked_abstract_generic_bodies`. It keys the shared flow lattice by resolved
binding identity, renders source names only in diagnostics, and queries explicit
parameter/field-wise `Copy` grants without constructing sample types. Incomplete
operation or nominal-entailment coverage rolls back that attempted analysis before
the existing reconstruction path runs. This staged migration preserves the current
incomplete-analysis policy. The artifact is not used for runtime evaluation.

Structural row remainders inherit field-wise `Copy` through retained subtraction
equations, including chains and zero-removal equalities. Excluded labels must all
have been removed before that grant covers the remainder. This proof is directional:
it never grants `Copy` to the source from a bound on its remainder.
For a closed source, the retained equation determines the remainder's actual
fields; their types decide ownership, including mixed and empty remainders.
In the opposite direction, a row equation proves Copy of its source when its
known heads and retained remainder are Copy. Alternative decompositions are
positive proof routes, not an ordering-dependent choice of one shape.

Array reads retain their array/element types, auto-dereference depth and an
already-typed `u64` index operation. The consumer evaluates indices even inside
longer projection chains and uses the shared opaque-index place projection to
reject non-`Copy` element moves. Indexed writes, including field and tuple writes
through an indexed base, retain a separate ordered list of target-input operations.
The abstract consumer follows the interpreter: consume the RHS first, then
evaluate target inputs once, then reinitialize the place. A diverging RHS skips
the target entirely. Storage conversions, including closure environments erased
by a raw function type, remain pending without a retained contract. Index
coercions and empty-array validation remain pending. Temporary-array indexing is
retained when the selected element has a declared or structural Copy proof: the
base construction is consumed once before observing the index. Non-Copy temporary
element accesses and other temporary projections remain pending.

Numeric casts retain a distinct operation with solved primitive source and result
types. Their operands are observed once, including call effects inside explicit
array-index casts. Generic and nonnumeric casts remain pending rather than erasing
`From` dispatch or non-Copy source ownership.

Unguarded matches retain definition-resolved literal, wildcard, whole-binding
and enum-variant and named-struct patterns with declaration/field identities and
solved binding types. Tuple patterns retain their recursive element shape and
consume through individual tuple projections, preserving partial moves.
Bare variant resolution stays in inference. The consumer observes the scrutinee
once, applies pattern moves to the saved place and scopes bindings per arm, then
joins only continuing arms. Enum exhaustiveness uses the retained variant set;
primitive matches require a catch-all (or both boolean literals). Guards,
borrowed payload extraction and structural/positional patterns remain pending.
Nominal types without applicable ownership impl candidates retain negative
`Copy`/`Drop` coherence facts by declaration identity, allowing ordinary generic
struct moves and in-place enum payload extraction without reconstruction.
Unrestricted positive impls separately retain resolved target/aspect identity
and universal target coverage, allowing unconditional nominal `Copy` and `Drop`
queries. Conditional candidates with distinct ordinary target parameters and inline
or ordinary `where` aspect-only bounds retain polarity and conditions in target-argument
order. Applicability is proved or disproved from identity-resolved definition grants,
including negative bounds. A disproved conjunct defeats unknown siblings; a missing
grant does not prove absence. Applicable negative candidates override positive ones;
unknown overrides block positive grants. Destructor absence requires all positive
candidates to be disproved or an applicable negative override. Concrete specializations,
repeated/nested target arguments, associated bindings, row equations, field-wise conditions
and kind restrictions remain pending. Every candidate uses
the resolved aspect identity, including imported aliases; a same-named marker
cannot grant builtin ownership permission. Record blankets block only record
kinds. For a nominal `record` whose field-wise `Copy` applicability remains
unproved, a consuming operation is retained as a move rather than granted a
copy; this is conservative and does not infer `Copy` or destructor absence.
Absence of a declared bound never proves absence of a conditional destructor.
As in the concrete checker, unreachable duplicate
arms are conservatively analyzed rather than pruned.

Impl-method variants have separate structural lexical body binders, allocated
under their shared method-group symbol with a group-local definition ordinal.
Their parameters and locals are owned by those binders. Abstract construction
uses the retained binder rather than the flattened runtime method symbol, so
conditional variants cannot alias each other's generic parameters or locals.
Definition retention is independent of caller polymorphism: a declared generic
used only inside the method body still retains its binder and bounds.
Record-target aspect methods are inferred at definition time through a separate
definition-local `Self` parameter; this does not replace their call-site schemes
or runtime dispatch. The receiver's nominal identity is distinct from its field
row, even for a pure-tail target. Field-wise `Copy` evidence is not a nominal
`Copy` grant, and a method-owned parameter may shadow an impl row name.
Shadowed impl names are alpha-renamed only in definition-local enclosing facts;
the source method and runtime/call schemes are not rewritten. Selected structural
call contracts retain the candidate's declaring aspect identity and receiver
mode. Registration-ordered provenance is merged alongside candidates, because
module-local inference variable numbers cannot identify a declaration globally.

Expanded inherited defaults have definition-local fact snapshots: their copied
source spans must not let a later impl overwrite an earlier impl's selected
types or contracts. The snapshot is frozen immediately after that definition's
inference, before construction. Lexical identities are
allocated under the resolved source aspect-method identity, the resolved nominal
target or record-target group,
the canonical implementation module and a pair-local impl ordinal. Locals are
reallocated under that owner; source-global references keep their original
resolution. The module is part of the key because disjoint impl variants can
reside in different modules whose ordinal counters both start at zero.

Numeric compound assignments retain the assignment operator and read the target
after the RHS and target inputs have been evaluated. The target read checks moves
without re-evaluating indices. Nonnumeric compound operators remain pending until
their ownership-relevant operator contracts are retained.

Value-producing loops retain their solved result type and consume exact-type break
values. Nested loops establish their own result contracts, including Unit for
statement loops, and closures do not inherit an enclosing loop's contract. Break
coercions remain pending. A diverging break operand does not create a loop exit;
likewise, a diverging assignment index prevents later target inputs and restoration.

Record destructuring retains resolved binding identities, explicit discards and
typed owned remainders for closed rows and known open-row heads. Destructuring
has a pattern-specific shape retained from inference, separate from the source
receiver's type. Structural method inference installs the target's field-row
decomposition without asserting equality between nominal `Self` and its row.
Brand-erasing destructuring remains pending when ownership lacks destructor-
absence evidence for a possibly nominal receiver; field-wise `Copy` is not such
evidence.
A named remainder consumes the source once; without one, named and explicitly discarded fields are
consumed separately. Temporary constructions consume their inputs once, and place
scrutinees evaluate nested indices once before projecting the selected fields.
Unknown tails remain part of the remainder type. Parameter-backed open rows can
be decomposed when a typed row grant and an exact retained subtraction equation
identify their known heads and tail. Missing field types or remainder equations
remain pending, as do unresolved remainder ownership entailments. A known non-Copy
head disproves structural Copy without requiring a tail sample; explicit Copy
grants still take precedence. Nominal and reference patterns also remain staged.

Built-in operators retain their solved operand and result types. The direct
consumer visits operand effects without reconstructing a concrete body; operators
requiring abstract dispatch or additional legality facts remain pending. Array
`for-in` retains its element binding and iteration mode: unsized-array elements
are borrowed, while sized arrays follow the existing owned-element rules. Each
loop pass starts with a fresh element binding and preserves loop-carried moves.
Non-array iteration dispatch remains pending.

C-style `for` retains an initializer operation, condition, step and body. The
initializer owns a loop-local scope and runs once. Continue paths unwind body
locals and join fallthrough before the step; breaks and returns bypass it.
Restoring the step's lexical scope does not restore pre-body moves: saved
continue-edge moves preserve reinitializations performed by the body.
Diverging initializers or conditions do not enter the body. Exact-type
ascriptions preserve the underlying operation and place; ascriptions requiring
coercions or a different closure ownership contract remain pending.

Move-check reports distinguish preparation fallbacks from ownership-consumer
fallbacks and retain their source span and reason. Failed speculative analysis
rolls back partial results before recording the fallback. `move-check-count`
uses frozen resolver identities and prints deduplicated abstract successes and
fallback records; these measurements do not replace the unchecked-body report
or enable the final completeness guard.

Free functions and impl methods retain a declaration-specific definition scheme
with source names, including parameters appearing only in row-grant field types.
Associated facts are rebuilt against that definition's retained quantifiers.
Body-only associated projections retain separate definition parameters and their
declared member bounds, resolved in the aspect's declaring module. Static and
unit-variant paths retain their definition-time selections. Generic native
prelude schemes acquire nominal identity in `std::core` before instantiation.
Method definitions also retain inherited positive body grants. This does not
strengthen the separate call-site scheme. Supported methods use distinct frozen
body binders under their shared method-group symbol. A selected conditional call
retains its own receiver mode, rather than the last registered receiver mode.
Nominal impl receivers acquire the target declaration's resolved identity during
inference, including inherited defaults. Consuming receivers therefore retain
ownership facts without a later lookup by type spelling.
Named method calls likewise select signatures, candidate spans and receiver
modes by the receiver's known declaration identity, not the caller's imports.
Borrowed receiver declarations limit access to
`self` even though inference retains its bare target type. Structural targets,
default methods, and full method selection coverage remain staged.

The direct consumer retains closure environment ownership separately from the
callable signature. Direct local aliases and nested captures preserve this
contract: owned and cloned captures contribute to `Copy`, while reference
captures limit access without making the closure move-only. Implicit captures
carry a separate entry snapshot per closure and require a definition-time `Copy`
proof. Capture bodies are checked in a separate flow state. Aggregate, borrowed,
reassigned and coerced closure contracts, many-call non-Copy owned capture legality, other derived
entailments, nominal projections, and remaining method or
nested-definition artifacts are still staged. A loop with no break targeting it
retains a definition-time divergence fact so its abstract result is `Never` even
when inference's unused break-result variable remains unresolved.

Functions with quantified type variables in their scheme are stored as `FunBody::Generic(untyped_block)` rather than `FunBody::Typed(typed_block)`. At each call site the evaluator re-runs the construction pass on the untyped block at the concrete call-site types, producing a `TypedBlock` that is evaluated normally. This is the monomorphization mechanism.

`let`-bound unannotated closures generalised to polymorphic schemes are stored as `TypedExpr::GenericClosure { params, body: Block, .. }` and evaluated to `ClosureBody::Untyped(block)`. The evaluator re-runs construction per call, mirroring the function case.

**An `ImplBlock` that declares its own generics (v0.10.0, issue #233 — `impl<T:
Bound> Aspect for Type<T>`, or the `where` form) defers its methods to
`FunBody::Generic` the same way**, in `construct_impl_method`: `is_generic_target`
is now `impl_has_generics || struct_generic_names_for(target_name)...`, so an impl
whose target isn't even a nominal struct/enum (RFC-0061's structural blanket impls,
e.g. `impl<T: Display> Display for T[]`) is also covered without needing a real
`target_name` to key a registry lookup on. `construct_default_aspect_methods` is
skipped entirely for these impls — it constructs default method bodies eagerly
against a concrete `self` type today, which isn't sound against a conditional or
structural target without knowing the instantiation. Real bound-satisfaction
checking at each instantiation is issue #241/#245's job, not this mechanism's;
this only makes the syntax construct without crashing.

**Generic type arguments aren't recoverable from a runtime `Value` on their own
(issue #267, ADR-0043).** `construct_generic_body` (called from
`evaluator/call.rs` when a `ClosureBody::Untyped` is invoked) unifies the
receiver/argument types derived from live `Value`s against the scheme's declared
types to build the substitution used to construct the body. `Value::Struct`/
`Value::Enum` carry no type-argument info of their own, so naively this
unification always failed on an arity mismatch for any generic struct/enum
receiver, silently defaulting the type parameter to `Unit`.
`pipeline::type_checking::infer_named_type_args` fixes this by unifying each field's
*declared* type template (from the registry, `FieldEntry.ty`) against that
field's *actual* type (computed by the evaluator recursing over the live value)
and reading the type's own quantified type variables back out of the resulting
substitution — recovering, from field values alone, what the value's own type
tag never recorded. See ADR-0043 for the full reasoning and the rejected
alternative (tagging `Value` itself).

### Closure Body Expected Type

Owned capture source types are recorded before entering the closure body, using
the current narrowed type rather than its original declaration. Both typed and
let-polymorphic closure nodes carry these entry facts. Ownership analysis consumes
explicit owned captures from that snapshot, not from body reads after possible
restoration, and also checks unused or shadowed captures. See
[ADR-0062](../../docs/architecture/decisions/adr-0062-owned-capture-entry-types.md).

`Expr::Closure` construction passes `return_type.as_ref().map(|_| &ret_ty)` as the `expected_tail_ty` for `construct_block`. This is necessary so that enum variant literals with unmentioned type params (e.g. `Result::Ok { value }` in a `fun() -> Result<T,E>`) can resolve the unbound type argument from the annotation hint rather than failing with T0002. Closures without an explicit return annotation pass `None`.

### Exhaustive Match Checking

`check_match_exhaustiveness` runs at the end of `construct_match` once the scrutinee type is known concretely.

- An unguarded `_`, bare binding pattern, or irrefutable tuple `(a, b, ...)` is a catch-all — exhaustive.
- **Guarded arms do not count**: a guard may fail at runtime.
- `Bool`: must cover `true` and `false` (both unguarded).
- `Perhaps(_)`: must cover `Perhaps::Some` and `Perhaps::Nope`.
- `Result(_, _)`: must cover `Result::Ok` and `Result::Err`.
- Named enum: must cover every variant.
- `Never`: vacuously exhaustive.
- All other types (Int, Float, Str, …): value-infinite; only a catch-all satisfies exhaustiveness.

Error: `E0008 Non-exhaustive match`.

---

## Type Registries

All type and impl data is stored in a single `TypeDefinitionRegistry` (owned by `InferContext`, shared with `ConstructCtx` via reference). This replaced the previous design where four separate maps were passed to `ConstructCtx` individually (#133).

| Field | Type | Content |
|---|---|---|
| `struct_env` | `HashMap<String, Vec<(String, InferType, Span)>>` | struct name → field list (name, type, declaration span) |
| `struct_type_params` | `HashMap<String, Vec<TypeVar>>` | generic struct name → ordered type-param TypeVars (absent for non-generic structs) |
| `method_env` | `HashMap<String, HashMap<String, InferType>>` | type name → method name → fun type |
| `enum_env` | `HashMap<String, EnumInfo>` | enum name → variant list + type params |
| `aspect_env` | `HashMap<String, Vec<String>>` | aspect name → required method names |
| `impl_aspect_env` | `HashMap<(target, aspect), Vec<Vec<Type>>>` | aspect impl type-arg lists |

`TypeDefinitionRegistry` is constructed in one pre-pass and injected into `InferContext::new`, consistent with [ADR-0001](decisions/adr-0001-typeregistry-structure-and-location.md).

### Elaboration output: `TypedImplBlock::aspect_id`

`TypedImplBlock` carries `aspect_id: Option<SymbolId>` (v0.8.1, METEL-152). It is populated at the end of `construct_impl_decl` by:

1. Looking up the aspect's declaring module via `ctx.registry.aspect_declaring_module(aspect_name)`.
2. Looking up the `SymbolId` for `(declaring_module, aspect_name)` in `ctx.symbols` (the name resolver's intern table, threaded from `check_graph`).

`ctx.symbols` is `None` on the single-module pipeline (`check` / `check_with_ctx`), so `aspect_id` is `None` in that path. The elaborator (`elaborate`) consumes `aspect_id` and stores it in `RuntimeAspectImpl::aspect_id` for SymbolId-keyed dispatch.

---

## Coherence, Conditional Impls, Associated Types, and Structural Bounds (v0.10.0)

Five RFCs (0036, 0037, 0060's remaining scope, 0072, 0082, 0061) landed together this
sprint and share one pipeline shape: a bound-satisfaction question asked repeatedly
across the typechecker, resolved the same way everywhere it's asked.

### Coherence pass (`src/coherence.rs`)

Runs as its own stage between path normalization and typechecking (introduced in
#238, extended here). For every `impl`/`extend` block across the module graph it
checks, in order:

1. **Orphan rule (`T0014`)** — an impl is rejected unless the aspect or the target
   type is local to the declaring module. Structural type constructors (`T[]`,
   tuples, `fun` types) are treated as owned by `std::core`, never locally owned by
   a user module on their own (`outermost_id` returns `None` for them) — so a user
   module may only implement a *locally-declared* aspect for a structural target.
2. **Overlap detection (`T0015`)** — a pairwise scan across every impl of a given
   aspect (not exact-key grouping, since a blanket impl and a concrete impl for the
   same aspect never share a canonical key shape but can still conflict). Two impls
   are allowed to coexist when they're *provably disjoint*: one requires `T: Bound`
   and the other requires `T: !Bound` at the same target position (RFC-0036 §3.1
   syntactic negation). This positional bound extraction
   (`scoped_type_param_bounds`) and the `TypeParam(i)` canonicalization it depends
   on (`canonicalize_impl_target`) apply identically to `Named` targets and to
   structural targets (`T[]`'s element position, a tuple's element positions, a
   `fun` type's parameter/return positions) — RFC-0061 §2 requires structural
   targets to follow the same rules "without special cases," and the two functions
   are written to share one code path rather than special-casing shape.
3. **Polarity** — a negative impl (`extend Type: !Aspect;`) takes priority over a
   *blanket* positive impl for an overlapping instantiation (not a coherence
   conflict), but conflicts with a *concrete* positive impl for the exact same type
   (RFC-0081 §2.2) — decided by whether the positive side's canonical target still
   contains a `TypeParam`, not by polarity alone.

### Conditional-impl bound checking at use sites

`conditional_impl_bounds`/`array_impl_bounds` (and their negative-bound twins)
store each conditional impl's per-position bound requirements, keyed by aspect and
target. `type_satisfies_aspect` (`pipeline/type_checking/type_engine/mod.rs`) is the
single recursive query every use site funnels through: method calls, struct/enum
literal construction, and generic function-call bound checking
(`check_type_satisfies_bounds` in `pipeline/type_checking/construction/mod.rs`) all
ask this same function rather than each
re-implementing bound satisfaction. For `Type::Array`, it recurses into the
element type through the same function — so `T[]: Display` is satisfied
recursively for `T[][]` without any special nested-array case.

### Associated types (RFC-0082)

An aspect's `type Name;` (or `type Name: Bound;`) declarations and an impl's
`type Name = Concrete;` definitions are stored alongside the aspect/impl
registries. `T::AssocType` projections are resolved to the concrete type at both
call sites and inside impl method bodies (not left as an opaque placeholder past
construction). Equality constraints (`Aspect<AssocType = Concrete>`) and impl
completeness (every declared associated type must be defined, `T0017` otherwise)
are checked at the same points ordinary bound satisfaction is.

### Opaque return types (RFC-0037)

`fun f() -> impl Aspect` carries a `TypeScheme.opaque_returns` entry rather than
exposing the concrete return type to callers. The concrete type is checked against
the declared bound at definition time (once, at the function's own construction);
callers only ever see the aspect's interface, enforced by rejecting any use of the
result that isn't sanctioned by the bound.

### Structural targets

`Type::Array`/`Type::Tuple`/`Type::Fun` never resolve to a `SymbolId` the way a
named type does, so they're handled as explicit match arms wherever bound
satisfaction or diagnostics are produced, rather than falling through a generic
`Type::Named` path. `check_type_satisfies_bounds` emits a distinct `T0012` hint per
shape: arrays name the element type that's missing the bound; tuples and
functions report the concrete type since neither has a real impl to point at yet
(RFC-0061 §6/§7).

---

### Empty row narrowing

Both passes retain empty rows after moving every non-`Copy` field: an anonymous
record becomes `Record([])`, while a nominal value becomes a same-brand
`Residual { fields: [] }`. This is independent of the optional move checker.
`Name.{}` in type position names that empty residual; full-width normalization
still preserves a nominal declaration that genuinely has no fields.

Field reassignment widens from empty using the original binding row, not the
narrowed read row. The move checker's legal narrowed-value exemption must first
exclude a whole-binding move; otherwise empty rows bypass ownership checking
vacuously. See ADR-0059 and metel-core#1398.

Registered move-analysis placeholders remain abstract for narrowing, including
when nested in field types. This matches inference's hold-unresolved rule and
allows the move checker to diagnose generic ownership errors rather than skip
an unconstructable witness body. Known concrete fields still narrow normally.

Initially residual nominal bindings seed their missing fields into the same
typechecker flow state as local partial moves, with the full non-generic brand as
the underlying binding type. Assignments can then restore fields after parameter
passing, rebinding and capture. These are type-level absences, not ownership
diagnostic move sites. Generic residuals retain their concrete surviving field
types rather than inventing erased type arguments. See ADR-0061.

---

### Symbolic rows in ownership analysis

Destructuring declarations observe a place initializer, then let the pattern
account for its consumption (whole-row for a rest binding, field-wise otherwise).
Temporary initializers still consume their inputs during evaluation; treating
tuple or array literals as mere observations would leave owned elements usable.

Ownership reconstruction uses `Type::SymbolicRow` for an unknown row tail and
`Type::OpenRecord` for its known head. These are resolved witnesses, not inference
variables or runtime type forms. Conversions, spreads and rest patterns retain
the tail's identity and declared field-wise/negative facts. Only an actual closed
bound proves an empty tail; unknown tails are not vacuously `Copy`.

Remainder equations retain known fields in both directions. Specialization replays
those equations before defaulting unresolved scalar variables to `Never`.
Regression tests require no generic-body skip warning and pair successful `Copy`
forwarding with a genuine move violation when that bound is absent. See
[ADR-0060](../../docs/architecture/decisions/adr-0060-symbolic-row-ownership-witnesses.md).

Abstract field selections through equal row parameters gather grants from the
entire retained equality class. An untyped `{ label, .. }` grant proves the
label exists while the solved field-expression type supplies its type; typed row
grants must also agree with that expression type. Open nominal-projection
parameters contribute their selected head fields to the definition artifact
only, keeping the structural proof out of the call-site scheme.

Callable boundaries retain an explicit abstract callable-view operation. The
operand keeps its capture types and creation effects; the result carries the
written function type, including its use multiplicity. Capture-derived `Copy`
is therefore not recovered after a written slot erases the environment. Only
equal callable signatures and the existing first-order `Copy`-to-`Move`
conversion are accepted; other value coercions remain explicit fallbacks.

Declared value boundaries retain solved source/target pairs in each definition
snapshot. Multiple pairs may share a span (for example an ascription at a return
tail). Abstract read-copy requires a matching retained boundary, peels the
reference chain, and checks the referent's definition-time `Copy` proof before
observing the source. A mutable-to-shared reference view instead consumes the
source reference at an ordinary declared boundary; call-site reborrowing is a
separate operation.

Abstract sized-array-to-view coercions retain their solved boundary pair and a
distinct view operation. Creating a view observes a source place rather than
moving its owner; a temporary still consumes its construction inputs once.
Views are unconditionally `Copy`, as in the ordinary checker, while owning
sized arrays require `Copy` elements. View copying grants no permission to
move a non-`Copy` element out through an index. Empty literal coercions retain
their zero-length bottom element without inventing a bound for the target.
Call arguments use the retained selected function contract for the same view
operation. Array method dispatch retains its receiver kind and callable contract;
receiver views observe the sized owner, including through an existing reference.
Explicit type arguments constrain fresh callee parameters during definition
inference, so empty arguments retain the caller's declared parameter identity.
Explicit forwarding checks the caller's positive and negative grants, including
the existing `Copy`/`Drop` exclusion; it does not attach callee requirements to
the caller's binder. This retained abstract contract does not replace runtime
reconstruction, whose remaining unsupported forms can still report `I0010`.

## Known Limitations

### `as` Cast — Via `From<S>` Aspect (v0.4)

`as` is now desugared to a `From<S>` aspect check. Built-in impls cover `Int ↔ Float`. User-defined types may implement `From<S>` to enable `as` casts. Casting between types with no `From` impl is a typecheck error.

---

## Extension Points

### v0.4 — Aspects (shipped)

All four v0.4 extension points are done:

1. ~~Add `impl_env` / extend `TypeDefinitionRegistry` with aspect-impl storage~~ — **done**: `TypeDefinitionRegistry` carries `aspect_env: HashMap<String, Vec<String>>` (aspect name → required method names) and `impl_aspect_env: HashMap<(target, aspect), Vec<Vec<Type>>>` (impl type-arg lists).
2. ~~Replace the provisional `as` cast with a `From<S>` aspect check~~ — **done**: `construct_cast` calls `has_from_impl(target, source)` and errors with `cannot cast` if no impl is registered.
3. ~~Replace the provisional `?` error type match with a `From<E>` coercion lookup~~ — **done**: `construction.rs` emits a `PropagateError` node carrying the `from_key` when `E1 ≠ E2`; the evaluator calls the impl at runtime.
4. ~~Upgrade `for-in` from Array/Range only to an `Iterable<T>` aspect check~~ — **done**: inference pass checks `iterable_elem_type` and falls back to Array/Range for built-in types.
