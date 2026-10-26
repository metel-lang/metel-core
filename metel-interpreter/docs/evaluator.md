# Evaluator Implementation Notes

> Status: v0.8.3 — SymbolId dispatch for overloads (METEL-180/181): `RuntimeRegistry` gains `symbol_values: HashMap<SymbolId, Value>` for overloaded functions; `TypedExpr::Call::callee_id: Some(id)` bypasses lexical-env lookup. `register_core_natives_from_embedded` derives all std::core native bindings from the embedded `core.mtl` AST rather than hand-registration. `List<T>` native methods and primitive `Display` / `From` impls are live at runtime via `NativeKey` dispatch.  
> The evaluator is intentionally the simplest correct implementation. It will be rewritten before production use. Do not over-engineer it; open new issues for correctness gaps instead of adding complexity here.
>
> Status: v0.10.0 (in progress) — `type_of::value_to_type` recovers a generic struct/enum argument's own type parameters from its field values instead of reporting them as always-erased (issue #267, ADR-0043); see "Function Call Dispatch" below.

---

## Pipeline Position

```
TypedProgram           ──►  evaluate()       ──►  side effects / RuntimePanic  (legacy, single-module test path)
ElaboratedModuleGraph  ──►  evaluate_graph() ──►  side effects / RuntimePanic  (v0.8.1, main pipeline)
```

Entry points:
- `evaluator::evaluate(program: TypedProgram) -> Result<(), MetelError>` — single-module legacy path; used by the evaluator test harness only, not called from the main pipeline.
- `evaluator::evaluate_graph(graph: ElaboratedModuleGraph) -> Result<(), MetelError>` — multi-module path (v0.6.0, updated v0.8.1): processes each `TypedModule` in topological order in its own isolated `Environment`, seeding imported names from already-evaluated dependency environments and sharing a process-wide `RuntimeRegistry` for `std::core` ownership plus type/aspect dispatch. The `ElaboratedModuleGraph` newtype is a proof that the elaboration pass has already run.

The evaluator operates on the typed AST produced by the typechecker. It does not re-check types — if the evaluator panics on a type mismatch, that is a typechecker bug, not an evaluator limitation.

Source: `src/evaluator/` — split into `mod.rs` (core), `builtins.rs`, `call.rs`, `display.rs`, `lvalue.rs`, `pattern.rs`

---

## Runtime Values

```rust
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    Unit,
    Tuple(Vec<Value>),
    Array(Rc<RefCell<Vec<Value>>>),
    Struct { name: String, fields: HashMap<String, Value> },
    Enum   { name: String, variant: String, fields: HashMap<String, Value> },
    Callable(RuntimeCallable),
    Pointer(Rc<RefCell<Value>>),        // shared immutable reference — &expr (RFC-0043)
    MutPointer(Rc<RefCell<Value>>),     // shared mutable reference — &mut expr (RFC-0043)
}
```

`RuntimeCallable` distinguishes host-backed intrinsic callables from user
closures without making either one a special namespace concept:

```rust
pub enum RuntimeCallable {
    Closure(Rc<ClosureValue>),
    Intrinsic { label: String, fun: fn(Vec<Value>, &Span) -> Result<Value, MetelError> },
}
```

### Array representation

`Value::Array` uses `Rc<RefCell<Vec<Value>>>` internally, but the evaluator enforces **value semantics** at every binding site. When `env.define()` or `env.set()` stores an array, it calls `deep_clone_value()` to produce a fully independent copy. This means:

- Assigning an array variable to another name gives an independent copy — mutations to one do not affect the other.
- Passing an array to a function gives the function its own copy; `array_push` inside the function does not mutate the caller's array.
- `array_push` applied to the binding itself mutates through the `Rc<RefCell>` as expected.

**`Option` and `Result`** are represented as `Value::Enum` — the same general enum representation used for all user-defined enum types. `Option::Some { value: v }` produces `Value::Enum { name: "Option", variant: "Some", fields: { "value": v } }`, `None` produces `Value::Enum { name: "Option", variant: "None", fields: {} }`, and so on. Pattern matching and the `?` operator use the general enum path, not dedicated variants. (Dedicated `Value::Option` and `Value::Result` variants were removed in #205.)

### Range representation

`a..b` evaluates to `Value::Struct { name: "Range", fields: { start: Int, end: Int } }`. This is an ad-hoc struct, not a typed `Range` struct — it exists so `for-in` can inspect the fields without a dedicated type. Same pattern for `a..=b` → `"RangeInclusive"`.

---

## Signal-Based Control Flow

All evaluation functions return `Result<Signal, MetelError>`:

```rust
pub enum Signal {
    Value(Value),
    Return(Value),
    Break(Value),        // carries the break-expression value
    Continue,
    PropagateErr(Value), // the ? operator
}
```

`Signal::Value` is the normal case. The others implement non-local control flow by propagating up the call stack until handled:

| Signal | Consumed by |
|---|---|
| `Return(v)` | `call_function` — converts to `Signal::Value(v)` at the function boundary |
| `Break(v)` | `Expr::Loop` handler — exits the loop, returns `Signal::Value(v)` |
| `Continue` | `While`, `For`, `ForIn` loop bodies — skips to next iteration |
| `PropagateErr(e)` | `Expr::PropagateError` handler — or `call_function`, which wraps `e` in `Value::Enum { name: "Result", variant: "Err", fields: { "error": e } }` |

`Signal::into_value()` is a convenience that panics on non-Value signals. It is used at call sites where the typechecker guarantees the expression cannot diverge (e.g., function arguments, struct field expressions). If it panics, that indicates a typechecker bug.

---

## Environment and Runtime Registry

```rust
pub struct Environment {
    scopes: Vec<HashMap<String, Rc<RefCell<Value>>>>,
}
```

Each binding is stored as an `Rc<RefCell<Value>>`. This has two consequences:

1. **Mutation is visible through the scope chain.** `env.set(name, val)` finds the binding's `Rc` in any enclosing scope and mutates through it. This correctly implements `mut` re-assignment without requiring the caller to traverse scopes differently for reads vs writes.

2. **Mutation through the scope chain does not apply to closure captures.** Since
   v0.13.0 a closure does **not** snapshot the enclosing `Environment` — it builds a
   capture aggregate from its explicit capture list (see Closure Capture). `[x]` moves or
   copies the value in; `[&x]` / `[&var x]` capture a reference deliberately. A closure
   and its definition scope no longer implicitly share a `RefCell` for a bare capture —
   sharing is opt-in via `&`/`&var` in the list. The intended semantics RFC-0006 called
   for are now settled and implemented (RFC-0050 / RFC-0153 / RFC-0157; ADR-0052).

Lexical `Environment` storage is intentionally separate from runtime metadata. Module-owned runtime values, type-owned methods, and aspect impl methods live in a shared `RuntimeRegistry`, not as synthetic bindings inside the lexical scope stack. Type-owned method entries now also carry receiver and lightweight signature metadata so static-style callables and receiver methods are structurally distinct at runtime. Closures capture only lexical environment state; they do not capture runtime dispatch tables.

---

## Evaluation Entry Point

`evaluate()` runs three passes over the top-level declarations:

**Pass 1a — Define placeholders:**
Every top-level `Fun` is bound to `Value::Unit` in the root environment. This ensures the names exist before any closure is created, so closures formed in Pass 1b can capture them via shared `Rc`s.

**Pass 1b — Create closures:**
Every top-level `Fun` clones the full current environment and creates a `Value::Callable(RuntimeCallable::Closure(...))`. The clone captures the `Rc`s from Pass 1a, not copies of `Value::Unit`. `env.set()` then mutates those `Rc`s in place.

Top-level `Impl` methods are registered into the shared `RuntimeRegistry` during this pass. Inherent impls with no receiver are stored as type-owned associated values for `Type::method(...)` path resolution; inherent impls with a receiver are stored as receiver methods under the owning type. Aspect impls are stored as explicit aspect records attached to the owning type, and each runtime method entry carries receiver/signature metadata.

Because all function closures from Pass 1b share the same set of `Rc`s, after Pass 1b completes every closure's captured environment already contains references to every other function closure — including those defined after it. This "ties the knot" for mutual recursion without a fixpoint pass or separate reference-resolution step.

**Pass 2 — Evaluate bindings:**
Top-level `let`/`mut` bindings and statements are evaluated in order. `Fun` and `Impl` declarations are skipped (already handled in 1a/1b).

**Call `main()`:**
`main`'s body is executed directly in the root environment so that top-level `let`/`mut` bindings from Pass 2 are visible. `Signal::Return` from `main` is treated as a normal exit.

### Self-recursion inside blocks

`eval_decl` for `Fun` uses the same define-placeholder / clone / set pattern as the top-level pass so that functions defined inside a block can call themselves recursively.

---

## Closure Capture

> *Rewritten in v0.13.0 for the closure cluster (RFC-0050 / RFC-0134 / RFC-0152 /
> RFC-0153 / RFC-0157). Implementation shape is ADR-0052; this section is the runtime
> summary.*

A closure literal carries an explicit **capture list** — `[x, &y, &var z, w.clone()]`
before the pipes — required the moment a non-`Copy` binding is captured by value or any
binding is captured by reference (RFC-0050). At definition (`TypedExpr::Closure`) the
evaluator builds a **capture aggregate**: one field per list entry, its kind fixed by the
specifier — `[x]` moved (or copied, if `Copy`), `[x.clone()]` an independent copy, `[&x]`
a shared reference, `[&var x]` an exclusive reference. This is the same field-storage
machinery as a struct value, not a separate environment type, and the surrounding
`Environment` is **not** snapshotted.

There is **no per-call environment clone**. A call pushes only a fresh parameter scope;
the aggregate is read in place. A closure that declares `var` (a *mutating* closure)
mutates the aggregate in place and the writes **persist on the closure value across
calls** (RFC-0153 §1a write-back). A `mutating` call takes a `&var self`-shaped exclusive
borrow of the callee place; re-entering the *same* closure value while a call on it is in
progress is a runtime error, `R0015`, guarded by an in-call flag on the value (the
interim mechanism until RFC-0122 borrow checking; the aliased-`[&var x]` case is deferred
there).

A `Copy` closure (all captures `Copy`, no list) is bit-copied aggregate-and-all when the
value is copied — `let var d := c;` gives `d` an independent aggregate; the copies
diverge. A non-`Copy` closure has exactly one owner.

The closure-cluster checks (capture-list requirement, `var` requirement for a mutating
body, `once` requirement for a consuming body, the `var`-closure-through-shared-`&`
rejection, the in-call flag) are **always on** in v0.13.0, independent of `--move-check`
(ADR-0052 §1).

---

## Pattern Matching

`match_pattern(pattern, value, out)` returns `bool` and writes bindings into `out: &mut HashMap<String, Value>`. It does not mutate the environment directly — the caller pushes a scope and inserts the bindings after a successful match.

Guarded arms: the guard is evaluated in a temporary scope containing the pattern bindings. If the guard returns `false`, the scope is popped and the next arm is tried. Pattern bindings accumulated so far are discarded (the `out` map is not reused between arms).

The evaluator will panic with `"match: no arm matched scrutinee"` if no arm matches at runtime. The typechecker's exhaustiveness check (E0008) is the static guarantee that this panic is unreachable for well-typed programs.

---

## Call Stack Trace

Every user-defined function call pushes a `FrameInfo { fn_name, call_site }` onto a thread-local `CALL_STACK` before evaluating the body. On any runtime error, `attach_stack()` captures a snapshot of the stack and attaches it to the `MetelError`. The stack is displayed innermost-first in the error message:

```
[R0001] runtime error: division by zero
  at file.mln:10:5
  in bar at file.mln:7:9    ← innermost (called from line 7)
  in foo at file.mln:4:5    ← outermost
```

Anonymous closures appear as `<closure>`. The call stack is cleared at the start of each `evaluate()` call. `main()` itself is not pushed (it is executed directly, not via `call_function`).

---

## Assignment and Typed Places

Assignment targets are represented as `TypedPlace` (introduced in METEL-106, v0.7.0) rather than raw `AssignTarget` from the untyped AST. This ensures every sub-expression in an assignment target — including index expressions — is fully type-checked before the evaluator runs, so `arr[i + 1] = v` works correctly without re-entering the untyped evaluator.

```
TypedPlace::Ident(name)              — bare variable
TypedPlace::Deref { object }         — *expr (pointer write-through)
TypedPlace::Field { object, field }  — place.field  (pure field chain, root must be Ident)
TypedPlace::Index { object, index }  — place[typed_expr]
```

`lvalue.rs` provides:
- `eval_typed_place_value` — evaluates a place to get its current `Value` (used to retrieve the array `Rc` for index mutation)
- `extract_typed_place_field_path` — walks a `Field` chain down to a root identifier and a list of field names

Index mutation works by calling `eval_typed_place_value` on the receiver to get `Value::Array(rc)`, evaluating the index expression with `eval_expr`, then mutating through the shared `Rc<RefCell<Vec<Value>>>`. This preserves shared-reference semantics: if two bindings hold the same array Rc, mutation through either is visible via both.

## Method Dispatch (v0.8.1)

Every `TypedExpr::MethodCall` carries a `dispatch: MethodDispatch` field resolved by the elaboration pass:

```rust
pub enum MethodDispatch {
    Dynamic,                        // unresolved (e.g. calls on fn/tuple receivers)
    Inherent,                       // direct method on the concrete type
    Aspect { aspect_id: SymbolId }, // routes through a specific aspect impl
}
```

The evaluator branches on this field:

| `dispatch` | Lookup used | Notes |
|---|---|---|
| `Aspect { aspect_id }` | `get_aspect_method_by_id(type_name, aspect_id, method)` | Matches `RuntimeAspectImpl::aspect_id == aspect_id`; falls back to string search for builtins registered without a `SymbolId` |
| `Inherent` | `get_method_for_value(value, method)` | Checks inherent methods first, then aspect impls (string-based) |
| `Dynamic` | `get_method_for_value(value, method)` | Same as Inherent; only occurs when receiver type has no named registry entry |

`RuntimeAspectImpl` carries `aspect_id: Option<SymbolId>` alongside the existing `aspect_name: String`. Aspect impls registered during `run_passes` receive their `SymbolId` from `TypedImplBlock::aspect_id`. Builtins registered in `builtins.rs` use `None` and are found via the string fallback path.

---

## Benchmarking and Profiling Workflow (v0.8.2)

`src/pipeline.rs` now exposes two benchmarking entry points:

- `run_evaluator_fixture(...)` for the existing evaluator integration suite
- `run_file(...)` for the full module-graph pipeline

`run_evaluator_fixture(...)` matches the current evaluator integration harness. It times:

- `parse`
- `typecheck`
- `evaluate`

`run_file(...)` remains available for later module-system benchmarking and times:

- `load_root`
- `resolve`
- `normalize`
- `typecheck`
- `elaborate`
- `evaluate`

The `metel-bench` helper in `src/bin/metel-bench.rs` benchmarks every evaluator integration fixture in `tests/integration/sources/evaluator/integration/` through the same single-file parse/typecheck/evaluate path the test suite uses.

Typical usage:

```bash
cargo run --release --bin metel-bench
```

Useful filters:

```bash
cargo run --release --bin metel-bench -- \
  --fixture int_01_statistics.mtl \
  --iterations 20 \
  --warmups 3
```

Artifacts are written under `docs/benchmarks/v0.8.2-evaluator-integration/` by default:

- `summary.json` - machine-readable per-fixture timing summary
- `summary.md` - human-readable phase breakdown plus hot functions and edges
- `<fixture>.profile.json` - dynamic evaluator call graph with call counts and inclusive/self timings
- `<fixture>.callgraph.dot` - Graphviz rendering of the dynamic call graph

The evaluator profiler is language-level, not a Rust sampler. It records:

- per-function call counts
- inclusive time per function
- self time per function
- caller -> callee edge counts and inclusive time

Instrumentation hooks live at the evaluator call boundary:

- `push_frame` / `pop_frame` record user-defined function calls
- `call_runtime_callable` wraps intrinsic calls so builtin hot paths also appear in the graph
- `run_main` emits the synthetic `<entry> -> main` root edge

Use this profiler to decide which Metel-level call paths dominate a program, then use external Rust profilers only on the worst fixtures if implementation-level detail is still needed.

---

## Function Call Dispatch

`call_function(func, args, span)` handles three cases:

- `Value::Callable(RuntimeCallable::Intrinsic { fun, .. })` — calls the intrinsic function pointer directly.
- `Value::Callable(RuntimeCallable::Closure(rc))` — pushes a parameter scope over the
  closure's own capture aggregate (no environment clone since v0.13.0 — see Closure
  Capture), evaluates the body, and converts `Signal::Return` to `Signal::Value` at the
  boundary. For a `mutating` closure the aggregate's writes are kept on the value.
  `Signal::PropagateErr` is also converted: it wraps the error value in `Value::Enum { name: "Result", variant: "Err", fields: { "error": e } }` and returns `Signal::Value` — so the `?` error appears as a `Result::Err` value to the caller.
- `Value::Callable(RuntimeCallable::Closure(rc))` where `rc.body` is `ClosureBody::Untyped(block)` — a polymorphic generic function or let-bound closure. The evaluator re-runs the construction pass on the untyped block at the concrete argument types, producing a `TypedBlock` that is evaluated immediately. This is the monomorphization path.

  **Argument types for this re-construction come from `type_of::value_to_type`
  (v0.10.0, issue #267, ADR-0043)**, which now takes a `registry: &
  TypeDefinitionRegistry` and `span: &Span` to recover a generic struct/enum
  argument's own type parameters from its field values — runtime `Value::Struct`/
  `Value::Enum` carry no type-argument info intrinsically (`Wrapper { value: 5 }`'s
  own type tag is bare `Named("Wrapper", [])`), so without this, unifying the
  receiver's declared generic type against the argument's erased runtime type
  always failed on an arity mismatch and silently defaulted the type parameter to
  `Unit`. All three call sites (`call_runtime_callable`, both branches of
  `call_method_function`) pass the `type_ctx`'s registry through; the one call
  site without a guaranteed `type_ctx` (the early receiver-type capture in
  `call_method_function`, needed before `closure.body` is matched on) falls back
  to a synthetic empty registry, which is harmless since that specific value is
  never consumed by a generic (`ClosureBody::Untyped`) path.

Method dispatch no longer looks up synthetic environment keys. `eval_expr` resolves methods through the owning type's runtime entry, checking receiver methods first and then explicit aspect impl entries. Static paths such as `Type::new(...)` resolve through type-owned associated values. `impl From<S> for T` coercions resolve through the target type's `From<S>` aspect impl rather than by environment strings, and receiver binding now follows the runtime method metadata instead of closure parameter inspection.

### Aspect object dispatch — `dyn Aspect` (v0.13.0, RFC-0008)

> *Runtime shape recorded in ADR-0053.*

A `dyn Aspect` value is `Value::DynAspect { data: Rc<RefCell<Value>>, type_id, aspect_id,
aspect_name, type_args }` — a tagged wrapper, **not** a fat pointer, and there is **no
generated vtable**. `type_id` is the wrapped value's concrete type, resolved once by
`resolve_value_type_id` at coercion time. A method call on a `dyn Aspect` goes through the
exact same path as any method call: `resolve_value_type_id` returns `type_id` directly, and
`get_regular_method(type_id, name)` finds the concrete type's method — the type-keyed
registry *is* the dispatch table. `aspect_id` is not consulted at call time (it is for
`value_to_type` and object-safety diagnostics). `&var dyn` mutable-receiver dispatch works
because `data` is a shared `RefCell`.

Coercion is an explicit `TypedExpr::DynCoerce` node the checker plants at every
expected-`dyn` position (argument, `let`, array / `List` element, `return`, `break`);
object safety (RFC-0008 §3) is enforced entirely in the frontend, so a value only reaches
`DynCoerce` if its aspect already passed.

---

## Known Limitations

> **Per-module isolation** (flat environment, declaration collisions across modules) was fixed in v0.6.0 by `evaluate_graph`. Each module runs in its own isolated `Environment`; names from other modules are seeded explicitly from their evaluated environments.

### Generic function dispatch — re-constructs on each call

Generic functions and let-polymorphic closures re-run the construction pass at every call site. This is correct but not optimal: for hot generic functions, monomorphization at a higher level (pre-compiling all instantiation sites) would be faster. Acceptable for the tree-walk interpreter.

### Cross-module mutual recursion is not supported (#189)

`run_passes` runs all three passes (1a placeholders, 1b closures, 2 bindings) for one module before moving to the next. If function `foo` in module A calls `bar` in module B and `bar` calls `foo`, the circular dependency requires a specific multi-module structure (A and B are peers, both importing a third module C). When A is being evaluated, B's environment doesn't exist yet, so A's closures cannot capture B's functions. The fix requires running Pass 1a for all modules before Pass 1b for any module. No current test program exercises this pattern.

### `?` with mismatched error types — From coercion is required

> *Updated in v0.7.0 (METEL-80).*

The `?` operator is desugared in the `path_normalizer` pre-pass and then, during construction, checked for error-type compatibility. If the inner `Result<_, E1>` and the enclosing function's return type `Result<_, E2>` have different error types, the typechecker looks up `impl From<E1> for E2`. If a matching impl is found, the desugared Err arm calls `From::from`; if not, the program is rejected with T0007 (invalid cast). The only built-in From impls are `From<Float> for Int` and `From<Int> for Float`. User types must register a `From` impl explicitly. Full coercion for arbitrary type pairs is tracked in #13.

### Closure capture semantics (settled in v0.13.0)

> *Resolved. Was: "the PoC's `Rc<RefCell<Value>>` environment gives closures reference
> semantics for captured variables, not the intended permanent behaviour (RFC-0006)."*

Closure capture is now an explicit capture list with move-by-default, `&` / `&var` for
deliberate sharing, and in-place mutation with write-back for `var` closures — RFC-0050 /
RFC-0134 / RFC-0152 / RFC-0153 / RFC-0157, implementation shape ADR-0052, runtime summary
in the Closure Capture section above. A test may rely on a `[&var x]` closure mutating
`x`; a test must **not** rely on a bare `[x]` capture aliasing the enclosing binding —
that no longer happens.

---

## Extension Points

### v0.7.0 — `?` From coercion (shipped, METEL-80)

`?` From coercion is fully wired: when `E1 ≠ E2` the construction pass checks `has_from_impl(E2, E1)` and, if found, emits a `PropagateError` node carrying the `from_key`; the evaluator calls the impl at runtime. If no impl exists, T0007 (invalid cast) is emitted at typecheck time. Built-in impls: `From<Float> for Int`, `From<Int> for Float`. Additional user-defined impls may be registered via `aspect From<S>` implementations.

### Rewrite

The evaluator is designed to be thrown away. The correct rewrite path is:
1. Decide the permanent value representation (likely a tagged pointer or NaN-boxing scheme).
2. Carry the v0.13.0 closure capture model forward (RFC-0050 capture lists, RFC-0153
   mutation axis) — the aggregate/write-back shape is settled (ADR-0052); a compiled
   backend replaces the in-call flag with RFC-0122 borrow checking and gives `dyn Aspect`
   the real fat-pointer/vtable representation RFC-0008 §2 specifies (ADR-0053 is the
   tree-walk stand-in).

Per-module scope isolation is **already implemented** (v0.6.0). `evaluate_graph` runs each `TypedModule` in its own isolated `Environment`, seeding imported names from already-evaluated dependency environments. See the Pipeline Position section above.
