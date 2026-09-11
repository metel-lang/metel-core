// PoC evaluator — this implementation will almost certainly be rewritten.
// Implement the simplest correct thing; do not over-engineer.

pub(crate) mod builtins;
mod call;
mod display;
mod lvalue;
mod pattern;
mod type_of;

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashMap};
use std::ops::ControlFlow;
use std::rc::Rc;
use std::time::{Duration, Instant};

use serde::Serialize;

use crate::ast::{BinOp, CaptureSpec, Literal, Param, Span, TypeExpr, UnaryOp};
use crate::error::{FrameInfo, MetelError, RuntimeErrorCode};
use crate::typeinference::TypeCtx;

thread_local! {
    static CALL_STACK: RefCell<Vec<FrameInfo>> = const { RefCell::new(Vec::new()) };
    static PROFILER: RefCell<Option<ProfilerState>> = const { RefCell::new(None) };
}

pub(super) fn push_frame(fn_name: String, call_site: Span) {
    profiler_enter(&fn_name);
    CALL_STACK.with(|s| s.borrow_mut().push(FrameInfo { fn_name, call_site }));
}

pub(super) fn pop_frame() {
    profiler_exit();
    CALL_STACK.with(|s| {
        s.borrow_mut().pop();
    });
}

fn snapshot_stack() -> Vec<FrameInfo> {
    CALL_STACK.with(|s| s.borrow().clone())
}

pub(super) fn attach_stack(err: MetelError) -> MetelError {
    err.with_stack(snapshot_stack())
}
use crate::ast::Block;
use crate::elaborator::ElaboratedModuleGraph;
use crate::identity::LocalId;
use crate::symbols::SymbolId;
use crate::typed_ast::{
    FunBody, MethodDispatch, ResolvedImportRef, TypedBlock, TypedDecl, TypedExpr, TypedForInit,
    TypedProgram, TypedStmt,
};

// ── Runtime values ────────────────────────────────────────────────────────────

/// One step in a `MutFieldReference` path.
#[derive(Debug, Clone)]
pub enum PathSegment {
    Field(String),
    TupleIndex(usize),
    ArrayIndex(usize),
}

#[derive(Debug, Clone)]
pub enum Value {
    // ── Primitive types ───────────────────────────────────────────────────────
    I64(i64),
    /// Sized signed integers.
    I8(i8),
    I16(i16),
    I32(i32),
    /// Sized unsigned integers.
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    F64(f64),
    /// 32-bit float.
    F32(f32),
    Char(char),
    Boolean(bool),
    Str(String),
    Unit,
    // ── Compound types ────────────────────────────────────────────────────────
    Tuple(Vec<Value>),
    Array(Rc<RefCell<Vec<Value>>>),
    Record {
        fields: HashMap<String, Value>,
    },
    Struct {
        name: String,
        /// Stable identity of the struct's declaration (METEL-185 / ADR-0041). Lets
        /// method dispatch resolve the receiver to a type `SymbolId` instead of its
        /// surface name, so two modules' same-named structs never collide. `None`
        /// for values built without resolver context (the single-program path) and
        /// for builtins not yet threaded; dispatch falls back to the name then.
        type_id: Option<SymbolId>,
        fields: HashMap<String, Value>,
    },
    // Perhaps<T> and Result<T,E> use Value::Enum like all other enums. See ADR-0028.
    Enum {
        name: String,
        /// Stable identity of the enum's declaration. See `Struct::type_id`.
        type_id: Option<SymbolId>,
        variant: String,
        fields: HashMap<String, Value>,
    },
    Callable(RuntimeCallable),
    /// Read-only pointer to a named binding cell.
    Reference(Rc<RefCell<Value>>),
    /// Writable pointer to a named binding cell.
    MutReference(Rc<RefCell<Value>>),
    /// Read-only fat pointer for sub-element lvalue paths.
    /// `root` is the binding cell; `path` navigates to the leaf.
    FieldReference {
        root: Rc<RefCell<Value>>,
        path: Vec<PathSegment>,
    },
    /// Fat mutable pointer for sub-element lvalue paths (RFC-0045).
    /// `root` is the binding cell; `path` navigates to the leaf.
    MutFieldReference {
        root: Rc<RefCell<Value>>,
        path: Vec<PathSegment>,
    },
    /// An aspect object (RFC-0008 `dyn Aspect`) — a fat pointer: a data pointer to
    /// the concrete value plus a `(type_id, aspect_id)` pair standing in for the
    /// vtable pointer (RFC-0008 slice 2's own design call: reuse
    /// `RuntimeRegistry::get_aspect_method_by_id`'s existing `(type_id, aspect_id)`
    /// lookup instead of a separately-generated vtable). `type_id` is the wrapped
    /// value's *concrete* type, resolved once at coercion time; `aspect_id` is the
    /// principal aspect the value was coerced to (§9 UQ1: at most one
    /// method-bearing aspect). `aspect_name`/`type_args` duplicate what `aspect_id`
    /// already identifies (same redundancy `Struct`/`Enum` already keep between
    /// `name` and `type_id`) — needed so `value_to_type` can reconstruct
    /// `Type::Dyn { aspect, type_args }` *without* unwrapping `data`: the whole
    /// point of erasure is that a `dyn Aspect` value's static type must stay `dyn
    /// Aspect`, never leak back out as the wrapped concrete type, including when a
    /// generic function's body is reconstructed from a runtime argument (#286).
    DynAspect {
        data: Rc<RefCell<Value>>,
        type_id: SymbolId,
        aspect_id: SymbolId,
        aspect_name: String,
        type_args: Vec<crate::types::Type>,
    },
}

/// The body of a closure — either a fully type-checked block (monomorphic) or the
/// original untyped block (generic / let-polymorphic). The evaluator dispatches on
/// this to choose between `eval_block` and `eval_untyped_block`.
#[derive(Debug, Clone)]
pub enum ClosureBody {
    Typed(TypedBlock),
    Untyped(Block),
}

/// Signature of every native (host-implemented) `std::core` function.
pub(super) type NativeFn = fn(&[Value], &Span) -> Result<Value, MetelError>;

#[derive(Debug, Clone)]
pub enum RuntimeCallable {
    Closure(Rc<ClosureValue>),
    Intrinsic { label: String, fun: NativeFn },
}

#[derive(Debug, Clone, Copy, Default, Serialize)]
pub struct EvaluationOptions {
    pub collect_profile: bool,
}

/// Program-wide frozen identity (ADR-0054 / metel-core#1052), built once by
/// the pipeline from the same `Allocation` used for the ahead-of-time
/// construction pass. `Rc`-shared into every module's `TypeCtx`, so
/// `construct_generic_body`'s runtime reconstruction of a generic body — the
/// evaluator's one identity-free construction path — gets a real `BindingId`
/// at every binding site too, closing the last gap the dual-path evaluator
/// (metel-core#1052b) relied on a name-keyed fallback for.
#[derive(Debug, Clone)]
pub struct RuntimeIdentity {
    pub members: Rc<crate::identity::MemberTable>,
    pub binding_spans: Rc<crate::identity::BindingSpans>,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct EvaluationReport {
    pub profile: Option<EvaluatorProfile>,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct EvaluatorProfile {
    pub functions: Vec<FunctionProfile>,
    pub edges: Vec<CallEdgeProfile>,
}

#[derive(Debug, Clone, Serialize)]
pub struct FunctionProfile {
    pub function: String,
    pub calls: u64,
    pub inclusive_ns: u64,
    pub self_ns: u64,
}

#[derive(Debug, Clone, Serialize)]
pub struct CallEdgeProfile {
    pub caller: Option<String>,
    pub callee: String,
    pub calls: u64,
    pub inclusive_ns: u64,
}

#[derive(Debug, Default)]
struct ProfilerState {
    functions: HashMap<String, FunctionAccumulator>,
    edges: HashMap<(Option<String>, String), EdgeAccumulator>,
    active_frames: Vec<ActiveProfilerFrame>,
}

#[derive(Debug, Default)]
struct FunctionAccumulator {
    calls: u64,
    inclusive_ns: u64,
    self_ns: u64,
}

#[derive(Debug, Default)]
struct EdgeAccumulator {
    calls: u64,
    inclusive_ns: u64,
}

#[derive(Debug)]
struct ActiveProfilerFrame {
    function: String,
    started_at: Instant,
    child_time: Duration,
}

impl ProfilerState {
    fn into_profile(self) -> EvaluatorProfile {
        let functions = self
            .functions
            .into_iter()
            .map(|(function, acc)| FunctionProfile {
                function,
                calls: acc.calls,
                inclusive_ns: acc.inclusive_ns,
                self_ns: acc.self_ns,
            })
            .collect::<Vec<_>>();
        let edges = self
            .edges
            .into_iter()
            .map(|((caller, callee), acc)| CallEdgeProfile {
                caller,
                callee,
                calls: acc.calls,
                inclusive_ns: acc.inclusive_ns,
            })
            .collect::<Vec<_>>();

        let mut function_map: BTreeMap<String, FunctionProfile> = BTreeMap::new();
        for function in functions {
            function_map.insert(function.function.clone(), function);
        }
        let mut edges = edges;
        edges.sort_by(|lhs, rhs| {
            lhs.caller
                .cmp(&rhs.caller)
                .then(lhs.callee.cmp(&rhs.callee))
        });

        EvaluatorProfile {
            functions: function_map.into_values().collect(),
            edges,
        }
    }
}

fn reset_runtime_state(collect_profile: bool) {
    CALL_STACK.with(|s| s.borrow_mut().clear());
    PROFILER.with(|profiler| {
        *profiler.borrow_mut() = collect_profile.then(ProfilerState::default);
    });
}

fn finish_profile() -> Option<EvaluatorProfile> {
    PROFILER.with(|profiler| {
        profiler
            .borrow_mut()
            .take()
            .map(ProfilerState::into_profile)
    })
}

pub(super) fn profiler_enter(function: &str) {
    PROFILER.with(|profiler| {
        let mut profiler = profiler.borrow_mut();
        let Some(state) = profiler.as_mut() else {
            return;
        };

        let caller = state
            .active_frames
            .last()
            .map(|frame| frame.function.clone());
        state
            .functions
            .entry(function.to_string())
            .or_default()
            .calls += 1;
        state
            .edges
            .entry((caller, function.to_string()))
            .or_default()
            .calls += 1;
        state.active_frames.push(ActiveProfilerFrame {
            function: function.to_string(),
            started_at: Instant::now(),
            child_time: Duration::ZERO,
        });
    });
}

pub(super) fn profiler_exit() {
    PROFILER.with(|profiler| {
        let mut profiler = profiler.borrow_mut();
        let Some(state) = profiler.as_mut() else {
            return;
        };
        let Some(frame) = state.active_frames.pop() else {
            return;
        };

        let elapsed = frame.started_at.elapsed();
        let inclusive_ns = duration_ns(elapsed);
        let self_ns = duration_ns(elapsed.saturating_sub(frame.child_time));

        if let Some(acc) = state.functions.get_mut(&frame.function) {
            acc.inclusive_ns += inclusive_ns;
            acc.self_ns += self_ns;
        }

        let caller = state
            .active_frames
            .last()
            .map(|active| active.function.clone());
        if let Some(acc) = state.edges.get_mut(&(caller, frame.function.clone())) {
            acc.inclusive_ns += inclusive_ns;
        }
        if let Some(parent) = state.active_frames.last_mut() {
            parent.child_time += elapsed;
        }
    });
}

fn duration_ns(duration: Duration) -> u64 {
    duration.as_nanos().min(u128::from(u64::MAX)) as u64
}

#[derive(Debug, Clone, Default)]
pub struct RuntimeModuleEntry {
    values: HashMap<String, Value>,
}

#[derive(Debug, Clone, Default)]
pub struct RuntimeTypeEntry {
    associated_values: HashMap<String, RuntimeMethod>,
    inherent_methods: HashMap<String, RuntimeMethod>,
    aspect_impls: Vec<RuntimeAspectImpl>,
}

#[derive(Debug, Clone, Default)]
pub struct RuntimeAspectImpl {
    aspect_name: String,
    /// Stable identity of the aspect; `None` when aspect was registered via the old
    /// string-only path (builtins / single-module pipeline without name resolver).
    aspect_id: Option<SymbolId>,
    type_args: Vec<String>,
    methods: HashMap<String, RuntimeMethod>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeTypeRef {
    Named(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RuntimeTypePattern {
    Str,
    Array,
    Primitive(String),
}

#[derive(Debug, Clone, Default)]
pub struct RuntimeSignature {
    #[allow(dead_code)] // stored for future diagnostics/reflection and System F transition work
    pub params: Vec<RuntimeTypeRef>,
    #[allow(dead_code)] // stored for future diagnostics/reflection and System F transition work
    pub ret: Option<RuntimeTypeRef>,
}

#[derive(Debug, Clone)]
pub struct RuntimeMethod {
    #[allow(dead_code)] // stored for diagnostics/debugging; not used for structural lookup
    pub label: String,
    pub receiver: Option<crate::ast::ReceiverKind>,
    #[allow(dead_code)] // stored for future diagnostics/reflection and System F transition work
    pub signature: RuntimeSignature,
    pub body: RuntimeCallable,
}

#[derive(Debug, Clone, Default)]
pub struct RuntimeRegistry {
    modules: HashMap<Vec<String>, RuntimeModuleEntry>,
    /// Struct/enum type entries keyed by the type's stable `SymbolId` (METEL-185 /
    /// ADR-0041). Instance method dispatch resolves the receiver `Value` to this id
    /// directly, so two modules' same-named types never collide.
    types: HashMap<SymbolId, RuntimeTypeEntry>,
    /// Surface type name → `SymbolId`, the single name→id resolution step (ADR-0041)
    /// for sites that only have a name: static-member access (`List::new`), `From`
    /// targets, and host-built values whose `type_id` was not threaded. Not a method
    /// lookup — it only maps a name to an id, which then keys `types`.
    type_ids: HashMap<String, SymbolId>,
    pattern_methods: HashMap<RuntimeTypePattern, HashMap<String, RuntimeMethod>>,
    /// Aspect-tagged methods for structural (pattern-dispatched) targets, e.g.
    /// `impl<T: Display> Display for T[]` -- mirrors `RuntimeTypeEntry::aspect_impls`,
    /// which only covers `Struct`/`Enum` receivers (those carry a `type_id`;
    /// arrays/tuples/etc. don't and dispatch via `RuntimeTypePattern` instead).
    /// Needed so that when two different aspects register the same method name
    /// for the same pattern (issue #272), `MethodDispatch::Aspect { aspect_id }`
    /// -- stamped by construction once it's already picked the right one via
    /// bound satisfaction -- can look up that *specific* aspect's method
    /// instead of falling back to `pattern_methods`' plain last-registration-
    /// wins entry.
    pattern_aspect_methods: HashMap<RuntimeTypePattern, Vec<RuntimeAspectImpl>>,
    /// Callables dispatched by stable `SymbolId` rather than by name — overloaded
    /// free-function definitions (METEL-180) and ordinary top-level functions
    /// (METEL-187), whose surface name cannot always identify a single definition.
    symbol_values: HashMap<SymbolId, Value>,
    /// Every top-level (module-level) `let`/`mut`'s `def_id` (ADR-0042), populated
    /// once before Pass 1 from the whole program's declarations. Unlike a top-level
    /// `fn`'s `def_id` (always registered in `symbol_values` by Pass 1b, before any
    /// user code runs), a `let`/`mut`'s value is only registered when its Pass 2
    /// initializer actually executes — so a `Call::callee_id` miss on one of these ids
    /// can be a legitimate "used before it was defined" runtime error, not a bug. This
    /// set is exactly what distinguishes that case from an unconditional internal
    /// error (see the `TypedExpr::Call` handling in `eval_expr`).
    let_mut_def_ids: std::collections::HashSet<SymbolId>,
    /// Live, cell-backed storage for every top-level `let` / `var`, keyed by its
    /// `def_id` (metel-core#1052b). The cell is shared with the module
    /// environment's name entry, so a reassignment through either key is seen by
    /// both. This is what lets a function body resolve a module-level binding by
    /// its frozen `SymbolId` — a non-`main` function captures a pre-Pass-2
    /// snapshot of the module env and so never had the name in scope.
    global_value_slots: HashMap<SymbolId, Rc<RefCell<Value>>>,
}

type FieldWriteback = (Rc<RefCell<Value>>, Vec<String>, Rc<RefCell<Value>>);

impl RuntimeRegistry {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn register_symbol_value(&mut self, id: SymbolId, value: Value) {
        self.symbol_values.insert(id, value);
    }

    #[must_use]
    pub fn get_symbol_value(&self, id: SymbolId) -> Option<&Value> {
        self.symbol_values.get(&id)
    }

    /// Record that `id` belongs to a top-level `let`/`mut` (ADR-0042) — see the field
    /// doc on `let_mut_def_ids`.
    pub fn mark_let_mut_def_id(&mut self, id: SymbolId) {
        self.let_mut_def_ids.insert(id);
    }

    /// Whether `id` is a top-level `let`/`mut`'s identity, i.e. a `symbol_values` miss
    /// on it can be a legitimate "used before it was defined" runtime error rather
    /// than an internal bug.
    #[must_use]
    pub fn is_let_mut_def_id(&self, id: SymbolId) -> bool {
        self.let_mut_def_ids.contains(&id)
    }

    /// Publish the live cell of a top-level `let` / `var` under its `def_id`
    /// (metel-core#1052b). Called from Pass 2 right after the initializer runs,
    /// with the same `Rc` the module environment holds by name.
    pub fn register_global_slot(&mut self, id: SymbolId, cell: Rc<RefCell<Value>>) {
        self.global_value_slots.insert(id, cell);
    }

    /// The live cell of the top-level `let` / `var` whose identity is `id`, if
    /// its initializer has run.
    #[must_use]
    pub fn global_slot(&self, id: SymbolId) -> Option<&Rc<RefCell<Value>>> {
        self.global_value_slots.get(&id)
    }

    pub fn register_module_value(
        &mut self,
        module_path: impl Into<Vec<String>>,
        name: impl Into<String>,
        value: Value,
    ) {
        self.modules
            .entry(module_path.into())
            .or_default()
            .values
            .insert(name.into(), value);
    }

    pub fn register_std_core_value(&mut self, name: impl Into<String>, value: Value) {
        self.register_module_value(vec!["std".to_string(), "core".to_string()], name, value);
    }

    /// Get (or create) the type entry for `type_id`, recording the `type_name → id`
    /// resolution so name-only sites can resolve to this id later.
    fn type_entry_mut(&mut self, type_id: SymbolId, type_name: &str) -> &mut RuntimeTypeEntry {
        self.type_ids.insert(type_name.to_string(), type_id);
        self.types.entry(type_id).or_default()
    }

    /// Resolve a surface type name to its registered `SymbolId` (single resolution
    /// step; see [`RuntimeRegistry::type_ids`]).
    fn type_id_for_name(&self, type_name: &str) -> Option<SymbolId> {
        self.type_ids.get(type_name).copied()
    }

    pub fn register_type_value(
        &mut self,
        type_id: SymbolId,
        type_name: &str,
        name: impl Into<String>,
        value: RuntimeMethod,
    ) {
        self.type_entry_mut(type_id, type_name)
            .associated_values
            .insert(name.into(), value);
    }

    pub fn register_inherent_method(
        &mut self,
        type_id: SymbolId,
        type_name: &str,
        method_name: impl Into<String>,
        value: RuntimeMethod,
    ) {
        self.type_entry_mut(type_id, type_name)
            .inherent_methods
            .insert(method_name.into(), value);
    }

    #[allow(clippy::too_many_arguments)]
    pub fn register_aspect_method(
        &mut self,
        type_id: SymbolId,
        type_name: &str,
        aspect_name: impl Into<String>,
        aspect_id: Option<SymbolId>,
        type_args: Vec<String>,
        method_name: impl Into<String>,
        value: RuntimeMethod,
    ) {
        let entry = self.type_entry_mut(type_id, type_name);
        let aspect_name = aspect_name.into();
        let method_name = method_name.into();
        if let Some(aspect_impl) = entry.aspect_impls.iter_mut().find(|aspect_impl| {
            aspect_impl.aspect_name == aspect_name && aspect_impl.type_args == type_args
        }) {
            // Update aspect_id if we now have one (a later registration may have the id).
            if aspect_impl.aspect_id.is_none() {
                aspect_impl.aspect_id = aspect_id;
            }
            aspect_impl.methods.insert(method_name, value);
            return;
        }

        let mut methods = HashMap::new();
        methods.insert(method_name, value);
        entry.aspect_impls.push(RuntimeAspectImpl {
            aspect_name,
            aspect_id,
            type_args,
            methods,
        });
    }

    /// Look up a method belonging to a specific aspect impl, by the aspect's stable
    /// `SymbolId`. Selection is purely id-based: builtin aspect impls are seeded with
    /// their `SYM_ASPECT_*` ids and user impls carry the elaboration-stamped id, so
    /// no surface-name fallback is needed (METEL-185 / ADR-0041).
    #[must_use]
    pub fn get_aspect_method_by_id(
        &self,
        type_id: SymbolId,
        aspect_id: SymbolId,
        method_name: &str,
    ) -> Option<RuntimeMethod> {
        self.types
            .get(&type_id)?
            .aspect_impls
            .iter()
            .rev()
            .find_map(|ai| {
                if ai.aspect_id == Some(aspect_id) {
                    ai.methods
                        .get(method_name)
                        .cloned()
                        .filter(|m| m.receiver.is_some())
                } else {
                    None
                }
            })
    }

    pub fn register_pattern_method(
        &mut self,
        pattern: RuntimeTypePattern,
        method_name: impl Into<String>,
        value: RuntimeMethod,
    ) {
        self.pattern_methods
            .entry(pattern)
            .or_default()
            .insert(method_name.into(), value);
    }

    /// Register an aspect-tagged method for a structural (pattern-dispatched)
    /// target -- see `pattern_aspect_methods`'s doc. Mirrors
    /// `register_aspect_method`'s per-aspect grouping, just keyed by pattern
    /// instead of type id.
    pub fn register_pattern_aspect_method(
        &mut self,
        pattern: RuntimeTypePattern,
        aspect_name: impl Into<String>,
        aspect_id: Option<SymbolId>,
        method_name: impl Into<String>,
        value: RuntimeMethod,
    ) {
        let entries = self.pattern_aspect_methods.entry(pattern).or_default();
        let aspect_name = aspect_name.into();
        let method_name = method_name.into();
        if let Some(existing) = entries.iter_mut().find(|ai| ai.aspect_name == aspect_name) {
            if existing.aspect_id.is_none() {
                existing.aspect_id = aspect_id;
            }
            existing.methods.insert(method_name, value);
            return;
        }
        let mut methods = HashMap::new();
        methods.insert(method_name, value);
        entries.push(RuntimeAspectImpl {
            aspect_name,
            aspect_id,
            type_args: Vec::new(),
            methods,
        });
    }

    /// Look up a pattern-dispatched method belonging to a specific aspect impl,
    /// by the aspect's stable `SymbolId` -- the structural-target counterpart
    /// to `get_aspect_method_by_id`.
    #[must_use]
    pub fn get_pattern_aspect_method_by_id(
        &self,
        pattern: &RuntimeTypePattern,
        aspect_id: SymbolId,
        method_name: &str,
    ) -> Option<RuntimeMethod> {
        self.pattern_aspect_methods
            .get(pattern)?
            .iter()
            .rev()
            .find_map(|ai| {
                if ai.aspect_id == Some(aspect_id) {
                    ai.methods
                        .get(method_name)
                        .cloned()
                        .filter(|m| m.receiver.is_some())
                } else {
                    None
                }
            })
    }

    #[must_use]
    pub fn get_module_value(&self, module_path: &[String], name: &str) -> Option<Value> {
        self.modules.get(module_path)?.values.get(name).cloned()
    }

    #[must_use]
    pub fn get_type_value(&self, type_name: &str, name: &str) -> Option<Value> {
        let type_entry = self.types.get(&self.type_id_for_name(type_name)?)?;
        type_entry
            .associated_values
            .get(name)
            .map(|method| Value::Callable(method.body.clone()))
            .or_else(|| {
                type_entry
                    .aspect_impls
                    .iter()
                    .rev()
                    .find_map(|aspect_impl| {
                        aspect_impl
                            .methods
                            .get(name)
                            .filter(|method| method.receiver.is_none())
                            .map(|method| Value::Callable(method.body.clone()))
                    })
            })
    }

    #[must_use]
    pub fn get_inherent_method(
        &self,
        type_id: SymbolId,
        method_name: &str,
    ) -> Option<RuntimeMethod> {
        self.types
            .get(&type_id)?
            .inherent_methods
            .get(method_name)
            .cloned()
            .filter(|method| method.receiver.is_some())
    }

    #[must_use]
    pub fn get_regular_method(
        &self,
        type_id: SymbolId,
        method_name: &str,
    ) -> Option<RuntimeMethod> {
        self.get_inherent_method(type_id, method_name).or_else(|| {
            self.types
                .get(&type_id)?
                .aspect_impls
                .iter()
                .rev()
                .find_map(|aspect_impl| {
                    aspect_impl
                        .methods
                        .get(method_name)
                        .cloned()
                        .filter(|method| method.receiver.is_some())
                })
        })
    }

    #[must_use]
    pub fn get_method_for_value(&self, value: &Value, method_name: &str) -> Option<RuntimeMethod> {
        self.resolve_value_type_id(value)
            .and_then(|type_id| self.get_regular_method(type_id, method_name))
            .or_else(|| {
                runtime_type_pattern(value).and_then(|pattern| {
                    self.pattern_methods
                        .get(&pattern)?
                        .get(method_name)
                        .cloned()
                        .filter(|method| method.receiver.is_some())
                })
            })
    }

    /// Resolve a receiver `Value` to its type's `SymbolId` for method dispatch:
    /// the value's carried `type_id` when present (cross-module correct), else the
    /// name→id index (host-built values, primitives). `None` for values with no
    /// type entry (Array/Tuple/etc., which dispatch via `pattern_methods`).
    fn resolve_value_type_id(&self, value: &Value) -> Option<SymbolId> {
        match value {
            Value::Struct { type_id, name, .. } | Value::Enum { type_id, name, .. } => {
                type_id.or_else(|| self.type_id_for_name(name))
            }
            // A `dyn Aspect` fat pointer dispatches as its *wrapped* concrete type,
            // not as some synthetic "DynAspect" type — `type_id` was resolved once,
            // at coercion time, from the concrete value it wraps (RFC-0008 §2/§6).
            Value::DynAspect { type_id, .. } => Some(*type_id),
            _ => runtime_type_name(value).and_then(|name| self.type_id_for_name(name)),
        }
    }

    #[must_use]
    pub fn get_from_method(&self, target: &str, source: &str) -> Option<RuntimeMethod> {
        let target_id = self.type_id_for_name(target)?;
        self.types
            .get(&target_id)?
            .aspect_impls
            .iter()
            .rev()
            .find_map(|aspect_impl| {
                (aspect_impl.aspect_name == "From"
                    && aspect_impl.type_args.len() == 1
                    && aspect_impl.type_args[0] == source)
                    .then(|| aspect_impl.methods.get("from").cloned())
                    .flatten()
            })
            .or_else(|| {
                self.types
                    .get(&target_id)?
                    .associated_values
                    .get("from")
                    .cloned()
                    .or_else(|| self.inherent_method_without_receiver(target_id, "from"))
            })
    }

    fn inherent_method_without_receiver(
        &self,
        type_id: SymbolId,
        method_name: &str,
    ) -> Option<RuntimeMethod> {
        self.types
            .get(&type_id)?
            .inherent_methods
            .get(method_name)
            .cloned()
            .filter(|method| method.receiver.is_none())
    }

    #[must_use]
    pub fn resolve_module_export(&self, module_path: &[String], local_name: &str) -> Option<Value> {
        self.get_module_value(module_path, local_name).or_else(|| {
            let mut segments = local_name.split("::");
            let type_name = segments.next()?;
            let member_name = segments.next()?;
            if segments.next().is_some() {
                return None;
            }
            self.get_type_value(type_name, member_name)
        })
    }

    #[must_use]
    pub fn resolve_path_value(&self, segments: &[String]) -> Option<Value> {
        if segments.len() >= 3 {
            let module_path = segments[..2].to_vec();
            let local_name = segments[2..].join("::");
            if let Some(value) = self.resolve_module_export(&module_path, &local_name) {
                return Some(value);
            }
        }

        if segments.len() == 2 {
            return self.get_type_value(&segments[0], &segments[1]);
        }

        None
    }
}

#[derive(Debug, Clone)]
pub struct ClosureValue {
    pub name: Option<String>,
    pub captures: Vec<CaptureSpec>,
    /// Structural [`LocalId`] of each capture's *enclosing* binding, positionally
    /// aligned with `captures` (metel-core#1052b). A closure body's reference to
    /// a captured variable resolves to that enclosing id, so the capture cell is
    /// installed in the id-indexed frame under this key. `None` where identity
    /// allocation had nothing to stamp.
    pub capture_ids: Vec<Option<LocalId>>,
    pub params: Vec<Param>,
    /// Structural [`LocalId`] of each parameter binding, positionally aligned
    /// with `params` (metel-core#1052b). `None` where identity allocation had
    /// nothing to stamp (e.g. a body built by construction-at-call-time). The
    /// call path binds each argument into the id-indexed frame by this id.
    pub param_ids: Vec<Option<LocalId>>,
    pub body: ClosureBody,
    pub captured: Environment,
    pub call_mutation: crate::types::CallMutation,
    pub in_call: Cell<bool>,
    /// Present only when `body` is `ClosureBody::Untyped` (generic function). Provides
    /// the type context for construction-at-call-time so the untyped path is not needed.
    pub type_ctx: Option<std::rc::Rc<TypeCtx>>,
    /// The concrete function type of this closure, if known. Used by `value_to_type` to
    /// recover the closure's parameter/return types when it is passed as a generic argument.
    pub fun_type: Option<crate::types::Type>,
}

/// Deep-clone a value so that arrays get independent copies.
/// Tuples, structs, and enums are recursed into so that nested arrays are also copied.
/// All other value kinds contain no shared mutable state and can be cloned shallowly.
fn deep_clone_value(v: Value) -> Value {
    match v {
        Value::Callable(RuntimeCallable::Closure(closure))
            if matches!(
                closure.fun_type,
                Some(crate::types::Type::Fun(
                    _,
                    _,
                    _,
                    crate::types::UseMultiplicity::Copy,
                    _
                ))
            ) =>
        {
            Value::Callable(RuntimeCallable::Closure(Rc::new(ClosureValue {
                name: closure.name.clone(),
                captures: closure.captures.clone(),
                capture_ids: closure.capture_ids.clone(),
                params: closure.params.clone(),
                param_ids: closure.param_ids.clone(),
                body: closure.body.clone(),
                // A Copy closure is copied as a value, not Rc-aliased. Its owned
                // environment cells therefore begin as equal but independent state.
                captured: closure
                    .captured
                    .capture_closure_copy(&closure.captures, &closure.capture_ids),
                call_mutation: closure.call_mutation,
                in_call: Cell::new(false),
                type_ctx: closure.type_ctx.clone(),
                fun_type: closure.fun_type.clone(),
            })))
        }
        Value::Array(rc) => {
            let cloned: Vec<Value> = rc.borrow().iter().cloned().map(deep_clone_value).collect();
            Value::Array(Rc::new(RefCell::new(cloned)))
        }
        Value::Tuple(items) => Value::Tuple(items.into_iter().map(deep_clone_value).collect()),
        Value::Record { fields } => Value::Record {
            fields: fields
                .into_iter()
                .map(|(k, v)| (k, deep_clone_value(v)))
                .collect(),
        },
        Value::Struct {
            name,
            type_id,
            fields,
        } => Value::Struct {
            name,
            type_id,
            fields: fields
                .into_iter()
                .map(|(k, v)| (k, deep_clone_value(v)))
                .collect(),
        },
        Value::Enum {
            name,
            type_id,
            variant,
            fields,
        } => Value::Enum {
            name,
            type_id,
            variant,
            fields: fields
                .into_iter()
                .map(|(k, v)| (k, deep_clone_value(v)))
                .collect(),
        },
        other => other,
    }
}

/// Walk a `PathSegment` path into `root`, returning a clone of the leaf value.
fn read_path(root: &Value, path: &[PathSegment], span: &Span) -> Result<Value, MetelError> {
    let mut cur = root.clone();
    for seg in path {
        cur = deref_value(&cur, span)?.unwrap_or(cur);
        cur = match (seg, cur) {
            (
                PathSegment::Field(f),
                Value::Record { fields }
                | Value::Struct { fields, .. }
                | Value::Enum { fields, .. },
            ) => fields.get(f.as_str()).cloned().ok_or_else(|| {
                MetelError::panic(
                    RuntimeErrorCode::R0008,
                    format!("fat pointer: no field `{f}`"),
                    span,
                )
            })?,
            (PathSegment::TupleIndex(i), Value::Tuple(elems)) => {
                elems.get(*i).cloned().ok_or_else(|| {
                    MetelError::panic(
                        RuntimeErrorCode::R0008,
                        format!("fat pointer: tuple index {i} out of bounds"),
                        span,
                    )
                })?
            }
            (PathSegment::ArrayIndex(i), Value::Array(rc)) => {
                rc.borrow().get(*i).cloned().ok_or_else(|| {
                    MetelError::panic(
                        RuntimeErrorCode::R0004,
                        format!("fat pointer: array index {i} out of bounds"),
                        span,
                    )
                })?
            }
            _ => {
                return Err(MetelError::internal(
                    "fat pointer path: segment type mismatch",
                ))
            }
        };
    }
    Ok(cur)
}

/// Walk a `PathSegment` path into `root` and write `new_val` at the leaf.
fn write_path(
    root: &mut Value,
    path: &[PathSegment],
    new_val: Value,
    span: &Span,
) -> Result<(), MetelError> {
    if path.is_empty() {
        *root = new_val;
        return Ok(());
    }
    match root {
        Value::Reference(_) | Value::FieldReference { .. } => {
            return Err(MetelError::panic(
                RuntimeErrorCode::R0003,
                "cannot write through a shared reference",
                span,
            ))
        }
        Value::MutReference(rc) => {
            let mut referent = rc.borrow_mut();
            return write_path(&mut referent, path, new_val, span);
        }
        Value::MutFieldReference {
            root,
            path: ref_path,
        } => {
            let mut full_path = ref_path.clone();
            full_path.extend_from_slice(path);
            let mut referent = root.borrow_mut();
            return write_path(&mut referent, &full_path, new_val, span);
        }
        _ => {}
    }
    match (&path[0], root) {
        (
            PathSegment::Field(f),
            Value::Record { fields } | Value::Struct { fields, .. } | Value::Enum { fields, .. },
        ) => {
            let child = fields.get_mut(f.as_str()).ok_or_else(|| {
                MetelError::panic(
                    RuntimeErrorCode::R0008,
                    format!("fat pointer: no field `{f}`"),
                    span,
                )
            })?;
            write_path(child, &path[1..], new_val, span)
        }
        (PathSegment::TupleIndex(i), Value::Tuple(elems)) => {
            let child = elems.get_mut(*i).ok_or_else(|| {
                MetelError::panic(
                    RuntimeErrorCode::R0008,
                    format!("fat pointer: tuple index {i} out of bounds"),
                    span,
                )
            })?;
            write_path(child, &path[1..], new_val, span)
        }
        (PathSegment::ArrayIndex(i), Value::Array(rc)) => {
            let mut borrow = rc.borrow_mut();
            let child = borrow.get_mut(*i).ok_or_else(|| {
                MetelError::panic(
                    RuntimeErrorCode::R0004,
                    format!("fat pointer: array index {i} out of bounds"),
                    span,
                )
            })?;
            write_path(child, &path[1..], new_val, span)
        }
        _ => Err(MetelError::internal(
            "fat pointer path: segment type mismatch during write",
        )),
    }
}

/// Like `Reference`/`MutReference` deref but also handles `MutFieldReference` with a
/// proper span. Peels every layer of a reference chain (RFC-0067a §3's auto-deref
/// chain guarantee — `&&T` derefs through both levels) down to the first non-reference
/// value: both call sites (field access, method-dispatch value lookup) want the fully
/// dereferenced value, never an intermediate reference-to-a-reference.
fn deref_value(value: &Value, span: &Span) -> Result<Option<Value>, MetelError> {
    let mut current = match value {
        Value::Reference(rc) | Value::MutReference(rc) => rc.borrow().clone(),
        Value::FieldReference { root, path } | Value::MutFieldReference { root, path } => {
            read_path(&root.borrow(), path, span)?
        }
        // A `dyn Aspect` fat pointer "is" the concrete value it erases, the same
        // way a `Reference` "is" its referent (RFC-0008 §1) -- every caller of
        // `deref_value` wants the concrete value to inspect/dispatch on, never
        // the wrapper itself. `display.rs`/`type_of.rs` handle `Value::DynAspect`
        // separately, without going through `deref_value`, because they need to
        // choose deliberately whether to preserve the erasure (`type_of.rs`) or
        // see through it (`display.rs`) -- this function's callers all want the
        // latter.
        Value::DynAspect { data, .. } => data.borrow().clone(),
        _ => return Ok(None),
    };
    loop {
        current = match &current {
            Value::Reference(rc) | Value::MutReference(rc) => rc.borrow().clone(),
            Value::FieldReference { root, path } | Value::MutFieldReference { root, path } => {
                read_path(&root.borrow(), path, span)?
            }
            Value::DynAspect { data, .. } => data.borrow().clone(),
            _ => break,
        };
    }
    Ok(Some(current))
}

fn receiver_cell_from_value(value: &Value) -> Option<Rc<RefCell<Value>>> {
    match value {
        Value::Reference(rc) | Value::MutReference(rc) => Some(Rc::clone(rc)),
        // Same reasoning as the `TypedExpr::Ident` receiver loop above -- an
        // owned `dyn Aspect` value's own cell isn't the concrete receiver.
        Value::DynAspect { data, .. } => Some(Rc::clone(data)),
        _ => None,
    }
}

fn runtime_type_name(value: &Value) -> Option<&str> {
    match value {
        Value::Struct { name, .. } | Value::Enum { name, .. } => Some(name.as_str()),
        Value::I64(_) => Some("i64"),
        Value::I8(_) => Some("i8"),
        Value::I16(_) => Some("i16"),
        Value::I32(_) => Some("i32"),
        Value::U8(_) => Some("u8"),
        Value::U16(_) => Some("u16"),
        Value::U32(_) => Some("u32"),
        Value::U64(_) => Some("u64"),
        Value::F64(_) => Some("f64"),
        Value::F32(_) => Some("f32"),
        Value::Char(_) => Some("Char"),
        Value::Boolean(_) => Some("boolean"),
        Value::Str(_) => Some("String"),
        _ => None,
    }
}

fn runtime_type_pattern(value: &Value) -> Option<RuntimeTypePattern> {
    match value {
        Value::Str(_) => Some(RuntimeTypePattern::Str),
        Value::Array(_) => Some(RuntimeTypePattern::Array),
        Value::I64(_) => Some(RuntimeTypePattern::Primitive("i64".to_string())),
        Value::I8(_) => Some(RuntimeTypePattern::Primitive("i8".to_string())),
        Value::I16(_) => Some(RuntimeTypePattern::Primitive("i16".to_string())),
        Value::I32(_) => Some(RuntimeTypePattern::Primitive("i32".to_string())),
        Value::U8(_) => Some(RuntimeTypePattern::Primitive("u8".to_string())),
        Value::U16(_) => Some(RuntimeTypePattern::Primitive("u16".to_string())),
        Value::U32(_) => Some(RuntimeTypePattern::Primitive("u32".to_string())),
        Value::U64(_) => Some(RuntimeTypePattern::Primitive("u64".to_string())),
        Value::F64(_) => Some(RuntimeTypePattern::Primitive("f64".to_string())),
        Value::F32(_) => Some(RuntimeTypePattern::Primitive("f32".to_string())),
        Value::Char(_) => Some(RuntimeTypePattern::Primitive("Char".to_string())),
        Value::Boolean(_) => Some(RuntimeTypePattern::Primitive("boolean".to_string())),
        _ => None,
    }
}

fn runtime_type_key(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Named(name, args) if args.is_empty() => name.clone(),
        TypeExpr::Named(name, args) => format!(
            "{name}<{}>",
            args.iter()
                .map(runtime_type_key)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        TypeExpr::Unit => "()".to_string(),
        TypeExpr::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(runtime_type_key)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        TypeExpr::Record(fields) => format!(
            "{{ {} }}",
            fields
                .iter()
                .map(|(name, ty)| format!("{name}: {}", runtime_type_key(ty)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        TypeExpr::Array(inner) => format!("{}[]", runtime_type_key(inner)),
        TypeExpr::SizedArray(inner, size) => format!("[{}; {}]", runtime_type_key(inner), size),
        TypeExpr::Reference(inner) => format!("&{}", runtime_type_key(inner)),
        TypeExpr::MutReference(inner) => format!("&var {}", runtime_type_key(inner)),
        TypeExpr::Fun {
            params,
            return_type: ret,
            call_multiplicity,
            call_mutation,
        } => {
            let params = params
                .iter()
                .map(runtime_type_key)
                .collect::<Vec<_>>()
                .join(", ");
            let mut prefix = String::new();
            if *call_multiplicity == crate::types::CallMultiplicity::Once {
                prefix.push_str("once ");
            }
            if *call_mutation == crate::types::CallMutation::Mutating {
                prefix.push_str("var ");
            }
            match ret {
                Some(ret) => format!("{prefix}({params}) -> {}", runtime_type_key(ret)),
                None => format!("{prefix}({params})"),
            }
        }
        TypeExpr::ImplAspect { bound, .. } => format!("impl {}", runtime_type_key(bound)),
        TypeExpr::Projection {
            base, assoc_name, ..
        } => {
            format!("{}::{assoc_name}", runtime_type_key(base))
        }
        TypeExpr::RecordProjection { path, fields, .. } => {
            format!("{} .{{ {} }}", path.join("::"), fields.join(", "))
        }
        TypeExpr::DynAspect { bound, .. } => format!("dyn {}", runtime_type_key(bound)),
    }
}

fn runtime_type_ref(ty: &TypeExpr) -> RuntimeTypeRef {
    RuntimeTypeRef::Named(runtime_type_key(ty))
}

fn runtime_signature(
    params: impl IntoIterator<Item = TypeExpr>,
    ret: Option<TypeExpr>,
) -> RuntimeSignature {
    RuntimeSignature {
        params: params.into_iter().map(|ty| runtime_type_ref(&ty)).collect(),
        ret: ret.map(|ty| runtime_type_ref(&ty)),
    }
}

fn runtime_method_from_decl(
    label: String,
    method: &crate::typed_ast::TypedFunDecl,
    body: RuntimeCallable,
) -> RuntimeMethod {
    let receiver = method
        .params
        .first()
        .and_then(|param| param.receiver.clone());
    let params = method
        .params
        .iter()
        .filter_map(|param| {
            if param.receiver.is_some() {
                None
            } else {
                Some(
                    param
                        .type_ann
                        .clone()
                        .unwrap_or_else(|| TypeExpr::Named("_".to_string(), vec![])),
                )
            }
        })
        .collect::<Vec<_>>();
    let signature = runtime_signature(params, method.return_type.clone());

    RuntimeMethod {
        label,
        receiver,
        signature,
        body,
    }
}

fn std_core_lookup(name: &str, runtime: &RuntimeRegistry) -> Option<Value> {
    runtime.get_module_value(&["std".to_string(), "core".to_string()], name)
}

/// Resolve a bare identifier's storage cell for `&` / `&var` reference-taking
/// on it, preferring the id-indexed frame or the live global slot over the
/// name map (metel-core#1052b).
fn ident_rc(
    name: &str,
    binding: Option<crate::identity::BindingId>,
    env: &Environment,
    runtime: &RuntimeRegistry,
) -> Option<Rc<RefCell<Value>>> {
    match binding {
        Some(crate::identity::BindingId::Local(id)) => {
            env.get_local_rc(id).or_else(|| env.get_rc(name))
        }
        Some(crate::identity::BindingId::Global(sym)) => runtime
            .global_slot(sym)
            .cloned()
            .or_else(|| env.get_rc(name)),
        None => env.get_rc(name),
    }
}

// For a FieldAccess receiver like `a.b.c`, returns:
//   (struct_cell, ["a","b","c"], leaf_cell)
// where struct_cell is the Rc for the root variable (pointer-followed if needed),
// the path encodes every field segment, and leaf_cell is a fresh Rc wrapping a clone
// of the leaf value.  After a &mut self call the caller writes leaf_cell's value back.
fn lvalue_field_cell(
    receiver: &crate::typed_ast::TypedExpr,
    env: &Environment,
) -> Option<FieldWriteback> {
    use crate::typed_ast::TypedExpr;
    fn walk_path(expr: &TypedExpr, path: &mut Vec<String>) -> Option<String> {
        match expr {
            TypedExpr::Ident(name, _, _, _) => Some(name.clone()),
            TypedExpr::FieldAccess { object, field, .. } => {
                let root = walk_path(object, path)?;
                path.push(field.clone());
                Some(root)
            }
            _ => None,
        }
    }
    let mut path = Vec::new();
    let root = walk_path(receiver, &mut path)?;

    let root_cell = env.get_rc(&root)?;
    let struct_cell = {
        let inner = match &*root_cell.borrow() {
            Value::Reference(c) | Value::MutReference(c) => Some(Rc::clone(c)),
            _ => None,
        };
        inner.unwrap_or(root_cell)
    };
    let leaf_val = {
        let borrowed = struct_cell.borrow();
        let mut cur: &Value = &borrowed;
        for seg in &path {
            match cur {
                Value::Struct { fields, .. } | Value::Enum { fields, .. } => {
                    cur = fields.get(seg.as_str())?;
                }
                _ => return None,
            }
        }
        cur.clone()
    };
    let leaf_cell = Rc::new(RefCell::new(leaf_val));
    Some((struct_cell, path, leaf_cell))
}

use crate::typed_ast::is_lvalue_path as is_lvalue_path_typed;

/// Recursively walk a typed lvalue path, collecting `PathSegment`s.
/// Returns the root binding name and the full segment list (root-to-leaf order).
fn build_mut_path(
    expr: &TypedExpr,
    env: &mut Environment,
    runtime: &RuntimeRegistry,
    span: &Span,
) -> Result<ControlFlow<Signal, (String, Vec<PathSegment>)>, MetelError> {
    match expr {
        TypedExpr::Ident(name, _, _, _) => Ok(ControlFlow::Continue((name.clone(), vec![]))),
        TypedExpr::FieldAccess { object, field, .. } => {
            let (root, mut path) = match build_mut_path(object, env, runtime, span)? {
                ControlFlow::Continue(path) => path,
                ControlFlow::Break(signal) => return Ok(ControlFlow::Break(signal)),
            };
            path.push(PathSegment::Field(field.clone()));
            Ok(ControlFlow::Continue((root, path)))
        }
        TypedExpr::TupleAccess { object, index, .. } => {
            let (root, mut path) = match build_mut_path(object, env, runtime, span)? {
                ControlFlow::Continue(path) => path,
                ControlFlow::Break(signal) => return Ok(ControlFlow::Break(signal)),
            };
            path.push(PathSegment::TupleIndex(*index));
            Ok(ControlFlow::Continue((root, path)))
        }
        TypedExpr::Index { object, index, .. } => {
            let (root, mut path) = match build_mut_path(object, env, runtime, span)? {
                ControlFlow::Continue(path) => path,
                ControlFlow::Break(signal) => return Ok(ControlFlow::Break(signal)),
            };
            let idx_val = match eval_to_value(index, env, runtime)? {
                ControlFlow::Continue(value) => value,
                ControlFlow::Break(signal) => return Ok(ControlFlow::Break(signal)),
            };
            let i = match idx_val {
                Value::I64(n) if n >= 0 => n as usize,
                Value::U64(n) => n as usize,
                _ => {
                    return Err(MetelError::panic(
                        RuntimeErrorCode::R0004,
                        "&var: array index must be a non-negative integer",
                        span,
                    ))
                }
            };
            path.push(PathSegment::ArrayIndex(i));
            Ok(ControlFlow::Continue((root, path)))
        }
        TypedExpr::UnaryOp(crate::ast::UnaryOp::Deref, object, _, _) => {
            build_mut_path(object, env, runtime, span)
        }
        _ => Err(MetelError::internal("build_mut_path: not a lvalue path")),
    }
}

// ── Control flow signals ──────────────────────────────────────────────────────

/// Returned by evaluation functions to handle non-local control flow.
/// Regular expression evaluation returns `Signal::Value`.
#[derive(Debug)]
pub enum Signal {
    Value(Value),
    Return(Value),
    Break(Value), // carries value for `loop { break expr; }`
    Continue,
}

impl Signal {
    /// Extract the inner `Value`, consuming the signal.
    ///
    /// # Panics
    /// Panics for non-`Value` signals (`Return`/`Break`/`Continue`) — callers that
    /// need the full signal must match directly instead.
    #[must_use]
    pub fn into_value(self) -> Value {
        match self {
            Signal::Value(v) => v,
            other => panic!("Signal::into_value called on non-Value signal: {other:?}"),
        }
    }

    pub fn into_value_or_signal(self) -> ControlFlow<Signal, Value> {
        match self {
            Signal::Value(v) => ControlFlow::Continue(v),
            other => ControlFlow::Break(other),
        }
    }
}

fn eval_to_value(
    expr: &TypedExpr,
    env: &mut Environment,
    runtime: &RuntimeRegistry,
) -> Result<ControlFlow<Signal, Value>, MetelError> {
    Ok(eval_expr(expr, env, runtime)?.into_value_or_signal())
}

// ── Environment ───────────────────────────────────────────────────────────────

/// Lexically-scoped environment — a stack of hashmaps.
/// Runtime storage stays cell-backed, but closure capture chooses whether to
/// clone cells by value (`capture_clone`) or share them explicitly (`define_rc`,
/// pointers, reference receivers).
#[derive(Debug, Clone)]
pub struct Environment {
    scopes: Vec<HashMap<String, Rc<RefCell<Value>>>>,
    /// Activation-flat, id-indexed binding slots (metel-core#1052b). Written
    /// alongside `scopes` whenever a binding's [`LocalId`] is known; `eval`
    /// consults it before the name map and falls back to the name map on a
    /// miss. A `LocalId` hashes the binding's full lexical path, so shadowing
    /// and block nesting need no runtime nesting here — the map is flat and
    /// lives for a single call activation (each call clones a fresh
    /// environment from the closure's captured one).
    frame: HashMap<LocalId, Rc<RefCell<Value>>>,
    /// Nested `fun`s `hoist_nested_funs` placeholdered but didn't build yet
    /// (metel-core#712). `eval_call_expr` builds one on demand if it's called before
    /// its declaration line runs. Keyed by the nested function's structural
    /// [`LocalId`] (metel-core#1052b).
    pending_funs: Vec<HashMap<LocalId, Rc<crate::typed_ast::TypedFunDecl>>>,
    /// Type context for construction-at-call-time of generic closures. Set once per module
    /// in `run_passes`; shared via `Rc` so cloning the environment is cheap.
    pub type_ctx: Option<std::rc::Rc<TypeCtx>>,
}

impl Default for Environment {
    fn default() -> Self {
        Self::new()
    }
}

impl Environment {
    #[must_use]
    pub fn new() -> Self {
        Self {
            scopes: vec![HashMap::new()],
            frame: HashMap::new(),
            pending_funs: vec![HashMap::new()],
            type_ctx: None,
        }
    }

    pub fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
        self.pending_funs.push(HashMap::new());
    }

    pub fn pop_scope(&mut self) {
        self.scopes.pop();
        self.pending_funs.pop();
    }

    /// Record that the nested `fun` with structural identity `id` has a
    /// placeholder but no closure yet (metel-core#712) — see the `pending_funs`
    /// field doc.
    ///
    /// # Panics
    /// Panics if called with no scope pushed — see [`Environment::define`].
    pub fn register_pending_fun(&mut self, id: LocalId, f: Rc<crate::typed_ast::TypedFunDecl>) {
        self.pending_funs.last_mut().unwrap().insert(id, f);
    }

    /// Remove and return a pending `fun` by its [`LocalId`] (innermost scope
    /// first), so it is built at most once.
    pub fn take_pending_fun(&mut self, id: LocalId) -> Option<Rc<crate::typed_ast::TypedFunDecl>> {
        for scope in self.pending_funs.iter_mut().rev() {
            if let Some(f) = scope.remove(&id) {
                return Some(f);
            }
        }
        None
    }

    /// Define a new binding in the current scope.
    /// Arrays are deep-cloned so each binding has an independent copy.
    ///
    /// # Panics
    /// Panics if called with no scope pushed — cannot happen through normal use,
    /// since `Environment::new` always starts with one scope and callers never pop
    /// past it.
    pub fn define(&mut self, name: &str, value: Value) {
        let cell = Rc::new(RefCell::new(deep_clone_value(value)));
        self.scopes
            .last_mut()
            .unwrap()
            .insert(name.to_string(), cell);
    }

    /// # Panics
    /// Panics if called with no scope pushed — see [`Environment::define`].
    pub fn define_rc(&mut self, name: &str, cell: Rc<RefCell<Value>>) {
        self.scopes
            .last_mut()
            .unwrap()
            .insert(name.to_string(), cell);
    }

    /// [`define`](Self::define), also recording the binding in the id-indexed
    /// `frame` when its [`LocalId`] is known (metel-core#1052b). The name map
    /// stays in step so the not-yet-migrated lookup and assignment paths keep
    /// working.
    ///
    /// # Panics
    /// Panics if called with no scope pushed — see [`Environment::define`].
    pub fn define_binding(&mut self, id: Option<LocalId>, name: &str, value: Value) {
        let cell = Rc::new(RefCell::new(deep_clone_value(value)));
        if let Some(id) = id {
            self.frame.insert(id, Rc::clone(&cell));
        }
        self.scopes
            .last_mut()
            .unwrap()
            .insert(name.to_string(), cell);
    }

    /// [`define_rc`](Self::define_rc), also recording the shared cell in the
    /// id-indexed `frame` when the binding's [`LocalId`] is known
    /// (metel-core#1052b).
    ///
    /// # Panics
    /// Panics if called with no scope pushed — see [`Environment::define`].
    pub fn define_binding_rc(&mut self, id: Option<LocalId>, name: &str, cell: Rc<RefCell<Value>>) {
        if let Some(id) = id {
            self.frame.insert(id, Rc::clone(&cell));
        }
        self.scopes
            .last_mut()
            .unwrap()
            .insert(name.to_string(), cell);
    }

    /// Look up a binding by its structural [`LocalId`] in the id-indexed frame
    /// (metel-core#1052b). `None` means no id-keyed slot — the caller falls
    /// back to the name map.
    #[must_use]
    pub fn get_local(&self, id: LocalId) -> Option<Value> {
        self.frame.get(&id).map(|cell| cell.borrow().clone())
    }

    /// Look up a binding, searching from innermost to outermost scope.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<Value> {
        for scope in self.scopes.iter().rev() {
            if let Some(cell) = scope.get(name) {
                return Some(cell.borrow().clone());
            }
        }
        None
    }

    /// Assign to an existing binding anywhere in the scope chain.
    /// Arrays are deep-cloned so each binding has an independent copy.
    #[must_use]
    pub fn set(&self, name: &str, value: Value) -> bool {
        for scope in self.scopes.iter().rev() {
            if let Some(cell) = scope.get(name) {
                *cell.borrow_mut() = deep_clone_value(value);
                return true;
            }
        }
        false
    }

    /// Return the Rc for a binding (used by closures to share mutable state).
    #[must_use]
    pub fn get_rc(&self, name: &str) -> Option<Rc<RefCell<Value>>> {
        for scope in self.scopes.iter().rev() {
            if let Some(cell) = scope.get(name) {
                return Some(Rc::clone(cell));
            }
        }
        None
    }

    /// The shared cell of a lexical local by its [`LocalId`], for `&`/`&var`
    /// reference-taking on an identifier that resolved to a local
    /// (metel-core#1052b).
    #[must_use]
    pub fn get_local_rc(&self, id: LocalId) -> Option<Rc<RefCell<Value>>> {
        self.frame.get(&id).map(Rc::clone)
    }

    #[must_use]
    pub fn capture_clone(&self) -> Self {
        let scopes = self
            .scopes
            .iter()
            .map(|scope| {
                scope
                    .iter()
                    .map(|(name, cell)| {
                        let cloned = deep_clone_value(cell.borrow().clone());
                        (name.clone(), Rc::new(RefCell::new(cloned)))
                    })
                    .collect()
            })
            .collect();
        Self {
            scopes,
            // The id-indexed frame is an activation-local mirror of the name
            // map (metel-core#1052b). A capture snapshot rebuilds bindings under
            // fresh name-keyed cells; re-deriving the id keys here would need a
            // name↔LocalId map this method does not have, and a parallel set of
            // cells would drift out of sync with `scopes`. Leave it empty — a
            // body reference to a captured binding then falls back to the name
            // map, which this snapshot does populate. #1052b-2 threads
            // `capture_ids` through so captures land in the frame directly.
            frame: HashMap::new(),
            // AST reference data, immutable once produced — sharing the `Rc`s across
            // this deep-cloned environment is fine, only `scopes`' runtime values need
            // independent cells.
            pending_funs: self.pending_funs.clone(),
            type_ctx: self.type_ctx.clone(),
        }
    }

    /// Copy a closure environment. By-value capture cells are independent in the
    /// copy; explicit `&` / `&var` captures retain the referent cell they borrowed.
    ///
    /// `capture_ids` is positionally aligned with `captures`; each capture's cell
    /// (the re-pointed one for a by-ref capture) is mirrored into the id-indexed
    /// frame under its enclosing [`LocalId`] so a body reference resolves there
    /// (metel-core#1052b).
    #[must_use]
    pub fn capture_closure_copy(
        &self,
        captures: &[CaptureSpec],
        capture_ids: &[Option<LocalId>],
    ) -> Self {
        let mut copied = self.capture_clone();
        for (i, capture) in captures.iter().enumerate() {
            let id = capture_ids.get(i).copied().flatten();
            let (name, shared) = match capture {
                // `id`, when known, is this capture's own LocalId in `self`
                // (metel-core#1052b) — read from `self`'s own frame first.
                CaptureSpec::SharedRef { name, .. } | CaptureSpec::MutRef { name, .. } => (
                    name,
                    id.and_then(|id| self.get_local_rc(id))
                        .or_else(|| self.get_rc(name)),
                ),
                CaptureSpec::Owned { name, .. } | CaptureSpec::Clone { name, .. } => (name, None),
            };
            if let Some(source) = shared {
                for scope in copied.scopes.iter_mut().rev() {
                    if scope.contains_key(name) {
                        scope.insert(name.clone(), source);
                        break;
                    }
                }
            }
            if let Some(id) = id {
                if let Some(cell) = copied.get_rc(name) {
                    copied.frame.insert(id, cell);
                }
            }
        }
        copied
    }

    /// Captures the bindings named by a closure capture list.
    ///
    /// # Errors
    ///
    /// Returns a runtime error when a capture is not available in this environment.
    ///
    /// `capture_ids` is positionally aligned with `captures`; each capture is
    /// installed in the id-indexed frame under its enclosing [`LocalId`] as well
    /// as by name, on one shared cell, so a closure-body reference resolves
    /// through the frame (metel-core#1052b).
    pub fn capture_closure(
        &self,
        captures: &[CaptureSpec],
        capture_ids: &[Option<LocalId>],
        span: &Span,
    ) -> Result<Self, MetelError> {
        if captures.is_empty() {
            return Ok(self.capture_clone());
        }
        let mut closure_environment = Environment::new();
        closure_environment
            .pending_funs
            .clone_from(&self.pending_funs);
        closure_environment.type_ctx.clone_from(&self.type_ctx);
        for (i, capture) in captures.iter().enumerate() {
            // `id`, when known, is this capture's *own* LocalId in `self` — the
            // same id `define_binding`/`define_binding_rc` would have filed it
            // under when the enclosing binding was created — so it is read from
            // `self`'s own frame first, falling back to the name map
            // (metel-core#1052b).
            let id = capture_ids.get(i).copied().flatten();
            match capture {
                CaptureSpec::Owned { name, .. } | CaptureSpec::Clone { name, .. } => {
                    let value = id
                        .and_then(|id| self.get_local(id))
                        .or_else(|| self.get(name))
                        .ok_or_else(|| {
                            MetelError::panic(
                                RuntimeErrorCode::R0003,
                                format!("undefined variable `{name}`"),
                                span,
                            )
                        })?;
                    closure_environment.define_binding(id, name, value);
                }
                CaptureSpec::SharedRef { name, .. } | CaptureSpec::MutRef { name, .. } => {
                    let cell = id
                        .and_then(|id| self.get_local_rc(id))
                        .or_else(|| self.get_rc(name))
                        .ok_or_else(|| {
                            MetelError::panic(
                                RuntimeErrorCode::R0003,
                                format!("undefined variable `{name}`"),
                                span,
                            )
                        })?;
                    closure_environment.define_binding_rc(id, name, cell);
                }
            }
        }
        Ok(closure_environment)
    }
}

// ── Entry point ───────────────────────────────────────────────────────────────

/// Evaluate a typed module graph produced by `check_graph`.
///
/// Each module is initialised in its own `Environment` seeded with builtins,
/// then cross-linked via the `imported_names` table populated by `check_graph`.
/// Modules are processed in topological order (dependencies before dependents).
/// See ADR-0029 for the isolation design and ADR-0019 for the superseded flat-merge approach.
///
/// # Errors
/// Returns an error if evaluating any module raises an unhandled runtime error.
pub fn evaluate_graph(elaborated: ElaboratedModuleGraph) -> Result<(), MetelError> {
    evaluate_graph_with_options(elaborated, EvaluationOptions::default(), None).map(|_| ())
}

/// # Errors
/// Returns an error if evaluating any module raises an unhandled runtime error.
pub fn evaluate_graph_with_options(
    elaborated: ElaboratedModuleGraph,
    options: EvaluationOptions,
    identity: Option<&RuntimeIdentity>,
) -> Result<EvaluationReport, MetelError> {
    let graph = elaborated.0;
    reset_runtime_state(options.collect_profile);
    let mut runtime = builtins::runtime_registry();

    // module_envs: path → fully initialised Environment.
    // Built incrementally; later modules can look up values from earlier ones.
    let mut module_envs: HashMap<Vec<String>, Environment> = HashMap::new();

    let root_path = graph
        .modules
        .last()
        .map(|m| m.module_path.clone())
        .unwrap_or_default();

    for module in graph.modules {
        let mut env = Environment::new();

        // Seed names imported from already-initialised dependency modules.
        for (local_name, import_ref) in &module.imported_names {
            let ResolvedImportRef {
                source_module,
                canonical_name,
                ..
            } = import_ref;
            if let Some(src_env) = module_envs.get(source_module) {
                if let Some(val) = src_env.get(canonical_name) {
                    env.define(local_name, val);
                }
            } else if let Some(val) = runtime.get_module_value(source_module, canonical_name) {
                env.define(local_name, val);
            }
        }

        // Build type context for construction-at-call-time of generic function bodies.
        let type_ctx = std::rc::Rc::new(TypeCtx {
            scheme_env: module.scheme_env.clone(),
            registry: graph.type_registry.clone(),
            members: identity.map(|i| Rc::clone(&i.members)),
            binding_spans: identity.map(|i| Rc::clone(&i.binding_spans)),
        });

        // Run the standard 3-pass + alias evaluation on this module's decls.
        run_passes(
            &module.decls,
            &module.import_aliases,
            &mut env,
            &mut runtime,
            Some(type_ctx),
        )?;

        module_envs.insert(module.module_path, env);
    }

    // Run main() from the root module's environment.
    let dummy = Span {
        start: 0,
        end: 0,
        filename: "<program>".to_string(),
        line: 0,
        col: 0,
    };
    let env = module_envs.get_mut(&root_path).ok_or_else(|| {
        MetelError::panic(RuntimeErrorCode::R0001, "root module not found", &dummy)
    })?;
    let result = run_main(env, &runtime);
    let profile = finish_profile();
    result?;
    Ok(EvaluationReport { profile })
}

/// Run the standard 3-pass evaluation on `decls` into `env`.
///
/// Pass 1a: placeholder bindings so closures can capture each other's Rc.
/// Pass 1b: replace placeholders with real closures ("ties the knot").
/// Alias registration: bind aliased import names after closures exist.
/// Pass 2: evaluate top-level let/mut/stmt declarations in order.
///
/// `type_ctx` must be set on `env` before calling so that generic function bodies
/// capture it for construction-at-call-time.
// Exhaustive match over every AST/type-system variant; splitting it up would
// scatter one coherent dispatch table across many small functions with no
// real gain in clarity.
#[allow(clippy::too_many_lines)]
fn run_passes(
    decls: &TypedProgram,
    aliases: &std::collections::HashMap<String, String>,
    env: &mut Environment,
    runtime: &mut RuntimeRegistry,
    type_ctx: Option<std::rc::Rc<TypeCtx>>,
) -> Result<(), MetelError> {
    env.type_ctx = type_ctx;
    // Pass 0 (ADR-0042): record this module's top-level let/mut identities before
    // anything else runs, so a later `Call::callee_id` miss on one of them can be
    // recognized as "not registered yet" rather than an internal-error bug.
    for decl in decls {
        match decl {
            TypedDecl::Let(d) => {
                if let Some(id) = d.def_id {
                    runtime.mark_let_mut_def_id(id);
                }
            }
            TypedDecl::Mut(d) => {
                if let Some(id) = d.def_id {
                    runtime.mark_let_mut_def_id(id);
                }
            }
            _ => {}
        }
    }
    // Pass 1a. Overloaded definitions (symbol_id set) are dispatched through
    // the runtime's symbol registry, never by name — no env binding for them.
    for decl in decls {
        if let TypedDecl::Fun(f) = decl {
            if f.symbol_id.is_none() {
                env.define(&f.name, Value::Unit);
            }
        }
    }

    // Pass 1b
    for decl in decls {
        match decl {
            TypedDecl::Fun(f) => {
                // Native functions bind directly to their host implementation.
                // Overloaded ones (symbol_id set) go to the symbol registry.
                if let FunBody::Native(key) = &f.body {
                    let value = Value::Callable(crate::evaluator::builtins::native_host_impl(*key));
                    if let Some(id) = f.symbol_id {
                        runtime.register_symbol_value(id, value);
                    } else {
                        // Ordinary top-level fn: bind by name (first-class uses) and,
                        // when it has a stable identity, also register it by SymbolId so
                        // direct calls dispatch through `callee_id` (METEL-187).
                        if let Some(id) = f.def_id {
                            runtime.register_symbol_value(id, value.clone());
                        }
                        let _ = env.set(&f.name, value);
                    }
                    continue;
                }
                let (body, ctx) = match &f.body {
                    FunBody::Typed(b) => (ClosureBody::Typed(b.clone()), None),
                    FunBody::Generic(b) => (ClosureBody::Untyped(b.clone()), env.type_ctx.clone()),
                    FunBody::Native(_) => unreachable!("native handled above"),
                };
                let captured = env.clone();
                let value = Value::Callable(RuntimeCallable::Closure(Rc::new(ClosureValue {
                    name: Some(f.name.clone()),
                    captures: vec![],
                    capture_ids: vec![],
                    params: f.params.clone(),
                    param_ids: f.param_ids.clone(),
                    body,
                    captured,
                    call_mutation: crate::types::CallMutation::Reading,
                    in_call: Cell::new(false),
                    type_ctx: ctx,
                    fun_type: None,
                })));
                if let Some(id) = f.symbol_id {
                    runtime.register_symbol_value(id, value);
                } else {
                    if let Some(id) = f.def_id {
                        runtime.register_symbol_value(id, value.clone());
                    }
                    let _ = env.set(&f.name, value);
                }
            }
            TypedDecl::Impl(impl_block) => match &impl_block.target_type {
                crate::ast::TypeExpr::Named(type_name, _) => {
                    let Some(target_id) = impl_block
                        .target_type_id
                        .or_else(|| builtins::builtin_type_id(type_name))
                    else {
                        continue;
                    };
                    for method in &impl_block.methods {
                        let body_callable = match &method.body {
                            FunBody::Native(key) => {
                                crate::evaluator::builtins::native_host_impl(*key)
                            }
                            FunBody::Typed(b) => RuntimeCallable::Closure(Rc::new(ClosureValue {
                                name: Some(method.name.clone()),
                                captures: vec![],
                                capture_ids: vec![],
                                params: method.params.clone(),
                                param_ids: method.param_ids.clone(),
                                body: ClosureBody::Typed(b.clone()),
                                captured: env.clone(),
                                call_mutation: crate::types::CallMutation::Reading,
                                in_call: Cell::new(false),
                                type_ctx: None,
                                fun_type: None,
                            })),
                            FunBody::Generic(b) => {
                                RuntimeCallable::Closure(Rc::new(ClosureValue {
                                    name: Some(method.name.clone()),
                                    captures: vec![],
                                    capture_ids: vec![],
                                    params: method.params.clone(),
                                    param_ids: method.param_ids.clone(),
                                    body: ClosureBody::Untyped(b.clone()),
                                    captured: env.clone(),
                                    call_mutation: crate::types::CallMutation::Reading,
                                    in_call: Cell::new(false),
                                    type_ctx: env.type_ctx.clone(),
                                    fun_type: None,
                                }))
                            }
                        };
                        let runtime_method = runtime_method_from_decl(
                            format!("{type_name}::{}", method.name),
                            method,
                            body_callable,
                        );
                        if let Some(aspect_name) = &impl_block.aspect_name {
                            let aspect_type_args = impl_block
                                .aspect_type_args
                                .iter()
                                .map(runtime_type_key)
                                .collect();
                            runtime.register_aspect_method(
                                target_id,
                                type_name,
                                aspect_name,
                                impl_block.aspect_id,
                                aspect_type_args,
                                &method.name,
                                runtime_method,
                            );
                        } else if runtime_method.receiver.is_none() {
                            runtime.register_type_value(
                                target_id,
                                type_name,
                                &method.name,
                                runtime_method,
                            );
                        } else {
                            runtime.register_inherent_method(
                                target_id,
                                type_name,
                                &method.name,
                                runtime_method,
                            );
                        }
                    }
                }
                crate::ast::TypeExpr::Array(_) => {
                    for method in &impl_block.methods {
                        let body_callable = match &method.body {
                            FunBody::Native(key) => {
                                crate::evaluator::builtins::native_host_impl(*key)
                            }
                            FunBody::Typed(b) => RuntimeCallable::Closure(Rc::new(ClosureValue {
                                name: Some(method.name.clone()),
                                captures: vec![],
                                capture_ids: vec![],
                                params: method.params.clone(),
                                param_ids: method.param_ids.clone(),
                                body: ClosureBody::Typed(b.clone()),
                                captured: env.clone(),
                                call_mutation: crate::types::CallMutation::Reading,
                                in_call: Cell::new(false),
                                type_ctx: None,
                                fun_type: None,
                            })),
                            FunBody::Generic(b) => {
                                RuntimeCallable::Closure(Rc::new(ClosureValue {
                                    name: Some(method.name.clone()),
                                    captures: vec![],
                                    capture_ids: vec![],
                                    params: method.params.clone(),
                                    param_ids: method.param_ids.clone(),
                                    body: ClosureBody::Untyped(b.clone()),
                                    captured: env.clone(),
                                    call_mutation: crate::types::CallMutation::Reading,
                                    in_call: Cell::new(false),
                                    type_ctx: env.type_ctx.clone(),
                                    fun_type: None,
                                }))
                            }
                        };
                        let runtime_method = runtime_method_from_decl(
                            format!("Array::{}", method.name),
                            method,
                            body_callable,
                        );
                        if runtime_method.receiver.is_some() {
                            // Also register aspect-tagged (issue #272), mirroring the
                            // `TypeExpr::Named` arm above: `register_pattern_method`
                            // alone can't distinguish two different aspects providing
                            // the same method name for `T[]`, silently keeping only
                            // the last one registered. Construction now stamps
                            // `MethodDispatch::Aspect { aspect_id }` once it has
                            // already picked the right one via bound satisfaction, so
                            // the aspect-tagged entry is what that dispatch mode
                            // actually looks up; `register_pattern_method` stays for
                            // the plain-name (`Inherent`/`Dynamic`) fallback path.
                            if let Some(aspect_name) = &impl_block.aspect_name {
                                runtime.register_pattern_aspect_method(
                                    RuntimeTypePattern::Array,
                                    aspect_name,
                                    impl_block.aspect_id,
                                    &method.name,
                                    runtime_method.clone(),
                                );
                            }
                            runtime.register_pattern_method(
                                RuntimeTypePattern::Array,
                                &method.name,
                                runtime_method,
                            );
                        }
                    }
                }
                _ => {}
            },
            _ => {}
        }
    }

    // Alias registration
    for (alias, canonical) in aliases {
        if let Some(val) = env
            .get(canonical)
            .or_else(|| std_core_lookup(canonical, runtime))
        {
            if env.get(alias).is_none() {
                env.define(alias, val);
            }
        }
    }

    // Pass 2
    for decl in decls {
        if !matches!(decl, TypedDecl::Fun(_) | TypedDecl::Impl(_)) {
            eval_decl(decl, env, runtime)?;
            // ADR-0042: register a top-level `let`'s value by SymbolId too, right
            // after its initializer runs — the same moment `env.define` already binds
            // it by name. This is what lets `Call::callee_id` dispatch work for a
            // module-level first-class function value the same way it already does
            // for `fn` declarations, without changing when the binding becomes
            // available (a call before this line executes still misses, exactly as
            // it does today via `env`).
            //
            // Deliberately `Let` only, not `Mut`: a `let` is immutable, so caching its
            // value once is permanently correct. A top-level `mut` can be reassigned
            // later (`TypedPlace::Ident` assignment updates `env` only, never
            // `symbol_values` — reworking that is a bigger change than this fix
            // warrants), so caching its value here would go stale and silently
            // resurrect an old value through `Call::callee_id` dispatch after a
            // reassignment, exactly the kind of silent-wrong-behavior bug this ADR
            // exists to close, not reintroduce. A `mut`'s id is still marked in
            // `let_mut_def_ids` (Pass 0) so a miss on it is correctly treated as
            // legitimate rather than an internal-error bug — it's simply never
            // registered, so every call through it falls back to `env`, same as
            // before this ADR's work, which is the only place its current value
            // actually lives.
            let stamped = match decl {
                TypedDecl::Let(d) => d.def_id.map(|id| (id, d.name.as_str())),
                _ => None,
            };
            if let Some((id, name)) = stamped {
                if let Some(value) = env.get(name) {
                    runtime.register_symbol_value(id, value);
                }
            }
            // metel-core#1052b: publish the live cell of every top-level
            // `let` / `var` under its `def_id` so a function body can resolve
            // the binding by its frozen identity. The cell is shared with the
            // module env's name entry, so a `var` reassignment through either
            // key is visible to both (fixes the read-from-non-`main` gap).
            let global = match decl {
                TypedDecl::Let(d) => d.def_id.map(|id| (id, d.name.as_str())),
                TypedDecl::Mut(d) => d.def_id.map(|id| (id, d.name.as_str())),
                _ => None,
            };
            if let Some((id, name)) = global {
                if let Some(cell) = env.get_rc(name) {
                    runtime.register_global_slot(id, cell);
                }
            }
        }
    }

    Ok(())
}

/// Locate and execute `main()` in `env`. Called after all passes complete.
fn run_main(env: &mut Environment, runtime: &RuntimeRegistry) -> Result<(), MetelError> {
    let dummy = Span {
        start: 0,
        end: 0,
        filename: "<program>".to_string(),
        line: 0,
        col: 0,
    };
    let (main_body, main_params, main_type_ctx) = match env.get("main") {
        Some(Value::Callable(RuntimeCallable::Closure(rc))) => {
            (rc.body.clone(), rc.params.clone(), rc.type_ctx.clone())
        }
        Some(Value::Unit) => {
            return Err(MetelError::panic(
                RuntimeErrorCode::R0002,
                "main() is generic — not supported",
                &dummy,
            ))
        }
        Some(_) => {
            return Err(MetelError::panic(
                RuntimeErrorCode::R0002,
                "`main` is not a function",
                &dummy,
            ))
        }
        None => {
            return Err(MetelError::panic(
                RuntimeErrorCode::R0001,
                "no main() function defined",
                &dummy,
            ))
        }
    };
    profiler_enter("main");
    let main_sig = match &main_body {
        ClosureBody::Typed(b) => eval_block(b, env, runtime),
        // An unannotated, all-diverging `main` has a free return variable: `!`
        // satisfies it without binding it during inference, so it is stored as a
        // generic body despite having no source-level generic parameters. Construct
        // that zero-argument body here just as ordinary generic calls do.
        ClosureBody::Untyped(b) => match main_type_ctx {
            Some(type_ctx) => match type_ctx.scheme_env.get("main") {
                Some(scheme) => crate::typechecker::construct_generic_body(
                    scheme,
                    &main_params,
                    &[],
                    b,
                    &dummy,
                    &type_ctx,
                    None,
                )
                .and_then(|typed| eval_block(&typed, env, runtime)),
                None => Err(MetelError::panic(
                    RuntimeErrorCode::R0002,
                    "main() body could not be typed",
                    &dummy,
                )),
            },
            None => Err(MetelError::panic(
                RuntimeErrorCode::R0002,
                "main() body could not be typed",
                &dummy,
            )),
        },
    };
    profiler_exit();
    match main_sig? {
        Signal::Value(_) | Signal::Return(_) => Ok(()),
        other => Err(MetelError::internal(format!(
            "unexpected signal from main(): {other:?}"
        ))),
    }
}

// ── Block and declaration evaluation ─────────────────────────────────────────

/// Build `f`'s closure, capturing `env` exactly as it stands right now, and
/// install it over its own binding (already `define`d as a placeholder by
/// `hoist_nested_funs`, or by a previous call to this same function).
fn build_and_set_nested_fun(
    f: &crate::typed_ast::TypedFunDecl,
    env: &mut Environment,
) -> Result<(), MetelError> {
    let (body, ctx) = match &f.body {
        FunBody::Typed(b) => (ClosureBody::Typed(b.clone()), None),
        FunBody::Generic(b) => (ClosureBody::Untyped(b.clone()), env.type_ctx.clone()),
        // `native` functions are stdlib-only and top-level; they cannot
        // appear as a nested declaration.
        FunBody::Native(_) => {
            return Err(MetelError::internal(
                "native function in nested declaration position",
            ))
        }
    };
    let captured = env.clone();
    let closure = Value::Callable(RuntimeCallable::Closure(Rc::new(ClosureValue {
        name: Some(f.name.clone()),
        captures: vec![],
        capture_ids: vec![],
        params: f.params.clone(),
        param_ids: f.param_ids.clone(),
        body,
        captured,
        call_mutation: crate::types::CallMutation::Reading,
        in_call: Cell::new(false),
        type_ctx: ctx,
        fun_type: None,
    })));
    let _ = env.set(&f.name, closure);
    Ok(())
}

/// Give every `fun` declared directly in `decls` a placeholder binding, so a
/// forward reference resolves to *something* rather than "undefined
/// variable" — mirroring `run_passes`'s top-level Pass 1a. Then, only when
/// it's safe to, build each one's real closure immediately, before any other
/// statement in the block runs, so siblings get full mutual visibility
/// regardless of textual order, including being callable from a statement
/// that precedes their own declaration — exactly like the spec's own
/// hoisting example (metel-core#656). The type checker's own hoisting pass
/// (`hoist_fun_decls`) already accepts such programs; this closes the
/// runtime gap where a nested block only built a `fun`'s closure once the
/// ordinary sequential loop below reached its declaration statement.
///
/// "Safe to" means: `decls` contains no `let`/`var` at all. Building eagerly
/// captures the block's environment as it stands *before anything in the
/// block has run* — if a `let`/`var` sits between an early call and the
/// callee's own declaration line, that eager closure would miss it even
/// though it had, by the time of the call, already executed. That's not a
/// merely-confusing error, it's a wrong answer: the same variable, already
/// initialized, is invisible depending on an unrelated detail (whether the
/// loop has reached the *fun's* declaration yet, not the *let's*). Rather
/// than a free-variable analysis to scope eager-building to exactly the
/// funs that don't touch such a `let` (finer-grained, but real new analysis
/// code with its own room for under-approximation bugs), this all-or-nothing
/// check per block trades a little precision for zero risk of a stale
/// snapshot: a block mixing `fun`s with `let`/`var` falls back to the
/// pre-#656-fix behavior for every fun in it (not callable before its own
/// declaration line — same "undefined `<the fun>`" as always), while a
/// block of `fun`s with no `let`/`var` among them — `is_even`/`is_odd`-style
/// mutual helpers, the case #656 itself reports — gets full hoisting with no
/// caveat.
///
/// **A deferred block's placeholder isn't dead-on-arrival any more (metel-core#712).**
/// Each deferred `fun` also goes into `env`'s `pending_funs` table; `eval_call_expr`
/// builds it on demand if something calls it before its own declaration line runs.
fn hoist_nested_funs(decls: &[TypedDecl], env: &mut Environment) -> Result<(), MetelError> {
    for decl in decls {
        if let TypedDecl::Fun(f) = decl {
            env.define_binding(f.local_id, &f.name, Value::Unit);
        }
    }
    let safe_to_build_eagerly = !decls
        .iter()
        .any(|d| matches!(d, TypedDecl::Let(_) | TypedDecl::Mut(_)));
    if safe_to_build_eagerly {
        for decl in decls {
            if let TypedDecl::Fun(f) = decl {
                build_and_set_nested_fun(f, env)?;
            }
        }
    } else {
        for decl in decls {
            if let TypedDecl::Fun(f) = decl {
                // A nested `fun` always carries a `LocalId` (metel-core#1052a);
                // without one it simply cannot be deferred-built, only reached
                // through its own declaration line.
                if let Some(id) = f.local_id {
                    env.register_pending_fun(id, Rc::new(f.clone()));
                }
            }
        }
    }
    Ok(())
}

/// Evaluate a block: push scope, run stmts, return tail (or Unit).
/// Non-Value signals (Return, Break, Continue) short-circuit and propagate out.
///
/// # Errors
/// Returns an error if evaluating any statement or the tail expression raises
/// an unhandled runtime error.
pub fn eval_block(
    block: &TypedBlock,
    env: &mut Environment,
    runtime: &RuntimeRegistry,
) -> Result<Signal, MetelError> {
    env.push_scope();
    hoist_nested_funs(&block.stmts, env)?;
    for decl in &block.stmts {
        let sig = eval_decl(decl, env, runtime)?;
        match sig {
            Signal::Value(_) => {}
            other => {
                env.pop_scope();
                return Ok(other);
            }
        }
    }
    let result = match &block.tail {
        Some(tail) => eval_expr(tail, env, runtime),
        None => Ok(Signal::Value(Value::Unit)),
    };
    env.pop_scope();
    result
}

/// Evaluate a single declaration inside a block or at the top level.
fn eval_decl(
    decl: &TypedDecl,
    env: &mut Environment,
    runtime: &RuntimeRegistry,
) -> Result<Signal, MetelError> {
    match decl {
        TypedDecl::Let(d) => match eval_expr(&d.value, env, runtime)? {
            Signal::Value(val) => {
                env.define_binding(d.local_id, &d.name, val);
                Ok(Signal::Value(Value::Unit))
            }
            other => Ok(other),
        },
        TypedDecl::Mut(d) => match eval_expr(&d.value, env, runtime)? {
            Signal::Value(val) => {
                env.define_binding(d.local_id, &d.name, val);
                Ok(Signal::Value(Value::Unit))
            }
            other => Ok(other),
        },
        TypedDecl::Fun(f) => {
            // `hoist_nested_funs` already gave `f` a placeholder and a
            // provisional closure before this block's statements started
            // running (metel-core#656). Rebuild it now that every `let`/`var`
            // preceding it in this block is actually in scope, so a call from
            // here on captures the fully lexically-correct environment.
            build_and_set_nested_fun(f, env)?;
            Ok(Signal::Value(Value::Unit))
        }
        TypedDecl::Stmt(s) => eval_stmt(s, env, runtime),
        // Type-level declarations have no runtime representation.
        TypedDecl::Struct(_) | TypedDecl::Enum(_) | TypedDecl::Impl(_) | TypedDecl::Aspect(_) => {
            Ok(Signal::Value(Value::Unit))
        }
    }
}

// ── Statement evaluation ──────────────────────────────────────────────────────

/// # Errors
/// Returns an error if evaluating the statement's inner expression(s) raises an
/// unhandled runtime error.
pub fn eval_stmt(
    stmt: &TypedStmt,
    env: &mut Environment,
    runtime: &RuntimeRegistry,
) -> Result<Signal, MetelError> {
    match stmt {
        TypedStmt::Expr(e) => {
            // Must propagate non-Value signals (Break/Continue/Return) that arise from
            // control-flow expressions used in statement position, e.g. `if (x) { break; }`.
            match eval_expr(e, env, runtime)? {
                Signal::Value(_) => Ok(Signal::Value(Value::Unit)),
                other => Ok(other),
            }
        }
        TypedStmt::While(w) => {
            loop {
                match eval_expr(&w.condition, env, runtime)? {
                    Signal::Value(Value::Boolean(false)) => break,
                    Signal::Value(Value::Boolean(true)) => {}
                    Signal::Value(_) => return Err(MetelError::internal(
                        "while: expected boolean condition (typechecker should have caught this)",
                    )),
                    other => return Ok(other), // propagate Return from condition
                }
                match eval_block(&w.body, env, runtime)? {
                    Signal::Value(_) | Signal::Continue => {}
                    Signal::Break(_) => break,
                    Signal::Return(v) => return Ok(Signal::Return(v)),
                }
            }
            Ok(Signal::Value(Value::Unit))
        }

        TypedStmt::For(f) => {
            // The init binding lives in its own scope so it doesn't leak out.
            // PoC note: if eval_block errors inside the loop, this scope is not
            // popped (errors are fatal so it doesn't matter in practice).
            env.push_scope();
            if let Some(init) = &f.init {
                match init {
                    TypedForInit::Let(d) => {
                        let val = match eval_to_value(&d.value, env, runtime)? {
                            ControlFlow::Continue(value) => value,
                            ControlFlow::Break(signal) => return Ok(signal),
                        };
                        env.define_binding(d.local_id, &d.name, val);
                    }
                    TypedForInit::Mut(d) => {
                        let val = match eval_to_value(&d.value, env, runtime)? {
                            ControlFlow::Continue(value) => value,
                            ControlFlow::Break(signal) => return Ok(signal),
                        };
                        env.define_binding(d.local_id, &d.name, val);
                    }
                    TypedForInit::Expr(e) => {
                        eval_expr(e, env, runtime)?;
                    }
                }
            }
            let result = loop {
                if let Some(cond) = &f.condition {
                    match eval_expr(cond, env, runtime)? {
                        Signal::Value(Value::Boolean(false)) => {
                            break Ok(Signal::Value(Value::Unit))
                        }
                        Signal::Value(Value::Boolean(true)) => {}
                        Signal::Value(_) => break Err(MetelError::internal(
                            "for: expected boolean condition (typechecker should have caught this)",
                        )),
                        other => break Ok(other),
                    }
                }
                match eval_block(&f.body, env, runtime)? {
                    Signal::Value(_) | Signal::Continue => {}
                    Signal::Break(_) => break Ok(Signal::Value(Value::Unit)),
                    Signal::Return(v) => break Ok(Signal::Return(v)),
                }
                if let Some(step) = &f.step {
                    eval_expr(step, env, runtime)?;
                }
            };
            env.pop_scope();
            result
        }

        TypedStmt::ForIn(fi) => {
            let iterable = match eval_to_value(&fi.iterable, env, runtime)? {
                ControlFlow::Continue(value) => value,
                ControlFlow::Break(signal) => return Ok(signal),
            };
            eval_for_in(fi, iterable, env, runtime)
        }
    }
}

fn eval_for_in(
    fi: &crate::typed_ast::TypedForInStmt,
    iterable: Value,
    env: &mut Environment,
    runtime: &RuntimeRegistry,
) -> Result<Signal, MetelError> {
    let binding = fi.binding.as_str();
    let binding_id = fi.binding_id;
    let body = &fi.body;
    let span = &fi.span;
    let iterable = deref_value(&iterable, span)?.unwrap_or(iterable);
    // Fast path for built-in sequence types.
    let fast_items: Option<Vec<Value>> = match &iterable {
        Value::Array(rc) => Some(rc.borrow().clone()),
        Value::Struct { name, fields, .. } if name == "Range" => {
            let s = range_field(fields, "start", span)?;
            let e = range_field(fields, "end", span)?;
            Some((s..e).map(Value::I64).collect())
        }
        Value::Struct { name, fields, .. } if name == "RangeInclusive" => {
            let s = range_field(fields, "start", span)?;
            let e = range_field(fields, "end", span)?;
            Some((s..=e).map(Value::I64).collect())
        }
        _ => None,
    };

    if let Some(items) = fast_items {
        for item in items {
            match run_for_in_iteration(binding_id, binding, item, body, env, runtime)? {
                ControlFlow::Continue(()) => {}
                ControlFlow::Break(sig) => return Ok(sig),
            }
        }
        return Ok(Signal::Value(Value::Unit));
    }

    // User-defined Iterable: dispatch through the receiver type's `next` (by id).
    let type_name = match &iterable {
        Value::Struct { name, .. } => name.clone(),
        _ => {
            return Err(MetelError::panic(
                RuntimeErrorCode::R0011,
                "for-in: expected Array, Range, or Iterable value",
                span,
            ))
        }
    };
    let next_fn = runtime
        .resolve_value_type_id(&iterable)
        .and_then(|id| runtime.get_regular_method(id, "next"))
        .ok_or_else(|| {
            MetelError::panic(
                RuntimeErrorCode::R0011,
                format!("for-in: `{type_name}` does not implement Iterable (no `next` method)"),
                span,
            )
        })?;

    let iter_cell = Rc::new(RefCell::new(deep_clone_value(iterable)));
    loop {
        let result = call::call_method_function(
            next_fn.body.clone(),
            call::ReceiverBinding::Shared(Rc::clone(&iter_cell)),
            vec![],
            None,
            None,
            None,
            span,
            runtime,
        )?
        .into_value();
        let maybe_item: Option<Value> = match result {
            Value::Enum {
                name,
                variant,
                mut fields,
                ..
            } if name == "Perhaps" => {
                if variant == "None" {
                    None
                } else {
                    Some(fields.remove("value").unwrap_or(Value::Unit))
                }
            }
            _ => {
                return Err(MetelError::internal(
                    "Iterable::next: expected Perhaps value",
                ))
            }
        };
        match maybe_item {
            None => break,
            Some(item) => {
                match run_for_in_iteration(binding_id, binding, item, body, env, runtime)? {
                    ControlFlow::Continue(()) => {}
                    ControlFlow::Break(sig) => return Ok(sig),
                }
            }
        }
    }
    Ok(Signal::Value(Value::Unit))
}

/// Run one iteration of a `for`-`in` loop: bind the loop variable — by its
/// [`LocalId`] in the id-indexed frame when known (metel-core#1052b) — then
/// evaluate the body in a fresh scope. `Break` carries the loop's result value
/// (`Unit` for a plain `break`, the returned value for a `return`).
fn run_for_in_iteration(
    binding_id: Option<LocalId>,
    binding: &str,
    item: Value,
    body: &TypedBlock,
    env: &mut Environment,
    runtime: &RuntimeRegistry,
) -> Result<ControlFlow<Signal, ()>, MetelError> {
    env.push_scope();
    env.define_binding(binding_id, binding, item);
    let sig = eval_block(body, env, runtime)?;
    env.pop_scope();
    Ok(match sig {
        Signal::Value(_) | Signal::Continue => ControlFlow::Continue(()),
        Signal::Break(_) => ControlFlow::Break(Signal::Value(Value::Unit)),
        Signal::Return(v) => ControlFlow::Break(Signal::Return(v)),
    })
}

fn range_field(
    fields: &HashMap<String, Value>,
    name: &str,
    _span: &Span,
) -> Result<i64, MetelError> {
    match fields.get(name) {
        Some(Value::I64(n)) => Ok(*n),
        _ => Err(MetelError::internal(format!(
            "range: missing or non-Int field `{name}`"
        ))),
    }
}

// ── Expression evaluation ─────────────────────────────────────────────────────

#[inline(never)]
#[allow(clippy::too_many_lines)]
fn eval_assign_expr(
    target: &crate::typed_ast::TypedPlace,
    op: &crate::ast::AssignOp,
    value: &TypedExpr,
    span: &Span,
    env: &mut Environment,
    runtime: &RuntimeRegistry,
) -> Result<Signal, MetelError> {
    use crate::typed_ast::TypedPlace;

    let rhs = match eval_to_value(value, env, runtime)? {
        ControlFlow::Continue(value) => value,
        ControlFlow::Break(signal) => return Ok(signal),
    };
    match target {
        TypedPlace::Ident(name, binding, ident_span) => {
            // A top-level `let` / `var` assigned from a non-`main` function is
            // absent from this activation's name map (that body captured a
            // pre-Pass-2 snapshot); write its live global slot directly
            // (metel-core#1052b). Locals stay on `env.set` — the frame and the
            // name entry share one cell.
            let global_cell = match binding {
                Some(crate::identity::BindingId::Global(sym)) => runtime.global_slot(*sym).cloned(),
                _ => None,
            };
            let new_val = if matches!(op, crate::ast::AssignOp::Assign) {
                rhs
            } else {
                let cur = global_cell
                    .as_ref()
                    .map(|c| c.borrow().clone())
                    .or_else(|| env.get(name))
                    .ok_or_else(|| {
                        MetelError::panic(
                            RuntimeErrorCode::R0003,
                            format!("assign: undefined `{name}`"),
                            ident_span,
                        )
                    })?;
                lvalue::apply_assign_op(op, cur, rhs, span)?
            };
            if let Some(cell) = &global_cell {
                *cell.borrow_mut() = deep_clone_value(new_val);
            } else if !env.set(name, new_val) {
                return Err(MetelError::panic(
                    RuntimeErrorCode::R0003,
                    format!("assign: undefined `{name}`"),
                    ident_span,
                ));
            }
            Ok(Signal::Value(Value::Unit))
        }

        TypedPlace::Deref {
            object,
            span: tspan,
        } => {
            let ptr = match eval_to_value(object, env, runtime)? {
                ControlFlow::Continue(value) => value,
                ControlFlow::Break(signal) => return Ok(signal),
            };
            match ptr {
                Value::Reference(rc) | Value::MutReference(rc) => {
                    let new_val = if matches!(op, crate::ast::AssignOp::Assign) {
                        rhs
                    } else {
                        let cur = rc.borrow().clone();
                        lvalue::apply_assign_op(op, cur, rhs, span)?
                    };
                    *rc.borrow_mut() = new_val;
                }
                Value::MutFieldReference { root, path } => {
                    let new_val = if matches!(op, crate::ast::AssignOp::Assign) {
                        rhs
                    } else {
                        let cur = read_path(&root.borrow(), &path, tspan)?;
                        lvalue::apply_assign_op(op, cur, rhs, span)?
                    };
                    write_path(&mut root.borrow_mut(), &path, new_val, tspan)?;
                }
                _ => {
                    return Err(MetelError::panic(
                        RuntimeErrorCode::R0003,
                        "assign: dereference target is not a pointer",
                        tspan,
                    ))
                }
            }
            Ok(Signal::Value(Value::Unit))
        }

        TypedPlace::Index {
            object,
            index,
            span: tspan,
        } => {
            let raw_arr_val = lvalue::eval_typed_place_value(object, env, runtime)?;
            // RFC-0110 §4.1: reach through a reference at the root, matching the peel
            // Pass 1 now performs. `Value::Array` holds an `Rc<RefCell<Vec<_>>>`, so the
            // peeled value shares the same backing store and writes propagate.
            let arr_val = deref_value(&raw_arr_val, tspan)?.unwrap_or(raw_arr_val);
            let idx_val = match eval_to_value(index, env, runtime)? {
                ControlFlow::Continue(value) => value,
                ControlFlow::Break(signal) => return Ok(signal),
            };
            let i = match idx_val {
                Value::U64(u) => u as usize,
                _ => {
                    return Err(MetelError::internal(
                        "index: expected u64 index (typechecker should have caught this)",
                    ))
                }
            };
            match arr_val {
                Value::Array(rc) => {
                    let len = rc.borrow().len();
                    if i >= len {
                        return Err(MetelError::panic(
                            RuntimeErrorCode::R0004,
                            format!("index {i} out of bounds (len {len})"),
                            span,
                        ));
                    }
                    let new_val = if matches!(op, crate::ast::AssignOp::Assign) {
                        rhs
                    } else {
                        let cur = rc.borrow()[i].clone();
                        lvalue::apply_assign_op(op, cur, rhs, span)?
                    };
                    rc.borrow_mut()[i] = new_val;
                    Ok(Signal::Value(Value::Unit))
                }
                _ => Err(MetelError::internal(
                    "index assign: receiver is not an Array (typechecker should have caught this)",
                )),
            }
        }

        TypedPlace::Field {
            object: _,
            field: _,
            span: tspan,
        }
        | TypedPlace::Tuple {
            object: _,
            index: _,
            span: tspan,
        } => {
            let (rc, path) = lvalue::resolve_place_assign_root(target, env, runtime, tspan)?;
            let new_val = if matches!(op, crate::ast::AssignOp::Assign) {
                rhs
            } else {
                let cur = read_path(&rc.borrow(), &path, tspan)?;
                lvalue::apply_assign_op(op, cur, rhs, span)?
            };
            write_path(&mut rc.borrow_mut(), &path, new_val, tspan)?;
            Ok(Signal::Value(Value::Unit))
        }
    }
}

#[inline(never)]
fn eval_struct_literal_expr(
    path: &[String],
    fields: &[(String, TypedExpr)],
    type_id: Option<SymbolId>,
    env: &mut Environment,
    runtime: &RuntimeRegistry,
) -> Result<Signal, MetelError> {
    let mut field_vals: HashMap<String, Value> = HashMap::new();
    for (name, expr) in fields {
        let value = match eval_to_value(expr, env, runtime)? {
            ControlFlow::Continue(value) => value,
            ControlFlow::Break(signal) => return Ok(signal),
        };
        field_vals.insert(name.clone(), value);
    }
    if path.len() == 2 {
        Ok(Signal::Value(Value::Enum {
            name: path[0].clone(),
            type_id,
            variant: path[1].clone(),
            fields: field_vals,
        }))
    } else {
        let name = path
            .last()
            .ok_or_else(|| MetelError::internal("struct literal: empty path"))?
            .clone();
        Ok(Signal::Value(Value::Struct {
            name,
            type_id,
            fields: field_vals,
        }))
    }
}

// Keep this as one dispatch table so receiver-mode handling stays in one place.
#[allow(clippy::too_many_lines)]
#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn eval_method_call_expr(
    receiver: &TypedExpr,
    method: &str,
    args: &[TypedExpr],
    dispatch: &MethodDispatch,
    expected_ret: &crate::types::Type,
    span: &Span,
    env: &mut Environment,
    runtime: &RuntimeRegistry,
) -> Result<Signal, MetelError> {
    let recv_val = match eval_to_value(receiver, env, runtime)? {
        ControlFlow::Continue(value) => value,
        ControlFlow::Break(signal) => return Ok(signal),
    };
    let mut arg_vals = Vec::with_capacity(args.len());
    for arg in args {
        let value = match eval_to_value(arg, env, runtime)? {
            ControlFlow::Continue(value) => value,
            ControlFlow::Break(signal) => return Ok(signal),
        };
        arg_vals.push(value);
    }
    // metel-core#286: exact static argument types from the typed nodes, for a generic
    // body constructed at call time.
    let static_arg_tys: Vec<crate::types::Type> = args.iter().map(|a| a.ty().clone()).collect();
    let static_receiver_ty = receiver.ty().clone();

    let recv_type_view = deref_value(&recv_val, span)?.unwrap_or_else(|| recv_val.clone());
    let method_entry = match dispatch {
        MethodDispatch::Aspect { aspect_id } => runtime
            .resolve_value_type_id(&recv_type_view)
            .and_then(|tid| runtime.get_aspect_method_by_id(tid, *aspect_id, method))
            .or_else(|| {
                // Structural receivers (arrays/tuples/etc.) have no type_id, so
                // `resolve_value_type_id` above is always `None` for them --
                // check the pattern-keyed aspect table instead (issue #272).
                runtime_type_pattern(&recv_type_view).and_then(|pattern| {
                    runtime.get_pattern_aspect_method_by_id(&pattern, *aspect_id, method)
                })
            })
            .or_else(|| runtime.get_method_for_value(&recv_type_view, method)),
        MethodDispatch::Inherent | MethodDispatch::Dynamic => {
            runtime.get_method_for_value(&recv_type_view, method)
        }
    }
    .ok_or_else(|| {
        MetelError::panic(
            RuntimeErrorCode::R0009,
            format!("method `{method}` not found on this value"),
            span,
        )
    })?;
    let func = method_entry.body.clone();
    match method_entry.receiver {
        Some(crate::ast::ReceiverKind::Ref | crate::ast::ReceiverKind::RefMut) => {
            let mut field_writeback: Option<FieldWriteback> = None;

            let receiver_binding = match receiver {
                TypedExpr::Ident(name, binding, _, _) => {
                    match ident_rc(name, *binding, env, runtime).map(|cell| {
                        let mut current = cell;
                        loop {
                            let inner = match &*current.borrow() {
                                Value::Reference(inner) | Value::MutReference(inner) => {
                                    Some(Rc::clone(inner))
                                }
                                // An owned `dyn Aspect` binding's own cell holds the
                                // fat pointer, not the concrete value -- `self`
                                // inside the method body must bind to `data`
                                // (RFC-0008 §2), or field access there would try to
                                // read a field off the wrapper itself.
                                Value::DynAspect { data, .. } => Some(Rc::clone(data)),
                                _ => None,
                            };
                            match inner {
                                Some(inner) => current = inner,
                                None => break,
                            }
                        }
                        current
                    }) {
                        Some(cell) => call::ReceiverBinding::Shared(cell),
                        None => call::ReceiverBinding::Value(recv_type_view.clone()),
                    }
                }
                TypedExpr::FieldAccess { .. } => match lvalue_field_cell(receiver, env) {
                    Some((struct_cell, path, leaf_cell)) => {
                        let binding = call::ReceiverBinding::Shared(Rc::clone(&leaf_cell));
                        field_writeback = Some((struct_cell, path, leaf_cell));
                        binding
                    }
                    None => receiver_cell_from_value(&recv_val)
                        .map(call::ReceiverBinding::Shared)
                        .unwrap_or(call::ReceiverBinding::Value(recv_type_view.clone())),
                },
                _ => receiver_cell_from_value(&recv_val)
                    .map(call::ReceiverBinding::Shared)
                    .unwrap_or(call::ReceiverBinding::Value(recv_type_view.clone())),
            };

            let result = call::call_method_function(
                func,
                receiver_binding,
                arg_vals,
                Some(&static_arg_tys),
                Some(&static_receiver_ty),
                Some(expected_ret),
                span,
                runtime,
            )?;

            if let Some((struct_cell, path, leaf_cell)) = field_writeback {
                let new_val = leaf_cell.borrow().clone();
                let last = path.last().unwrap();
                let prefix = &path[..path.len() - 1];
                let mut borrow = struct_cell.borrow_mut();
                let mut cur: &mut Value = &mut borrow;
                for seg in prefix {
                    match cur {
                        Value::Struct { fields, .. } | Value::Enum { fields, .. } => {
                            cur = fields.get_mut(seg.as_str()).unwrap();
                        }
                        _ => break,
                    }
                }
                if let Value::Struct { fields, .. } | Value::Enum { fields, .. } = cur {
                    fields.insert(last.clone(), new_val);
                }
            }

            Ok(result)
        }
        Some(crate::ast::ReceiverKind::Value) => call::call_method_function(
            func,
            call::ReceiverBinding::Value(recv_type_view),
            arg_vals,
            Some(&static_arg_tys),
            Some(&static_receiver_ty),
            Some(expected_ret),
            span,
            runtime,
        ),
        None => Err(MetelError::panic(
            RuntimeErrorCode::R0009,
            format!("runtime method `{method}` is not callable with a receiver"),
            span,
        )),
    }
}

#[inline(never)]
fn eval_call_expr(
    callee: &TypedExpr,
    args: &[TypedExpr],
    callee_id: Option<SymbolId>,
    expected_ret: &crate::types::Type,
    span: &Span,
    env: &mut Environment,
    runtime: &RuntimeRegistry,
) -> Result<Signal, MetelError> {
    let func_val = match callee_id {
        Some(id) => match runtime.get_symbol_value(id).cloned() {
            Some(value) => value,
            None if id.0 >= crate::symbols::OVERLOAD_SYM_START => {
                return Err(MetelError::internal(format!(
                    "no runtime value registered for overload symbol {id:?}"
                )));
            }
            None if runtime.is_let_mut_def_id(id) => match eval_to_value(callee, env, runtime)? {
                ControlFlow::Continue(value) => value,
                ControlFlow::Break(signal) => return Ok(signal),
            },
            None => {
                return Err(MetelError::internal(format!(
                    "no runtime value registered for callable symbol {id:?}"
                )));
            }
        },
        None => match eval_to_value(callee, env, runtime)? {
            ControlFlow::Continue(value) => value,
            ControlFlow::Break(signal) => return Ok(signal),
        },
    };
    // metel-core#712: a Unit here can be a deferred nested fun's placeholder, called
    // before its declaration line runs. Build it now instead of failing.
    let func_val = if matches!(func_val, Value::Unit) {
        if let TypedExpr::Ident(name, Some(crate::identity::BindingId::Local(id)), ..) = callee {
            if let Some(f) = env.take_pending_fun(*id) {
                build_and_set_nested_fun(&f, env)?;
                env.get_local(*id)
                    .or_else(|| env.get(name))
                    .unwrap_or(Value::Unit)
            } else {
                func_val
            }
        } else {
            func_val
        }
    } else {
        func_val
    };
    let mut arg_vals = Vec::with_capacity(args.len());
    for arg in args {
        let value = match eval_to_value(arg, env, runtime)? {
            ControlFlow::Continue(value) => value,
            ControlFlow::Break(signal) => return Ok(signal),
        };
        arg_vals.push(value);
    }
    // metel-core#286: the typed argument nodes already carry their exact static types.
    // Hand them down so a generic body constructed at call time does not have to
    // re-derive them from runtime values, which loses precision an empty collection
    // cannot supply.
    let static_arg_tys: Vec<crate::types::Type> = args.iter().map(|a| a.ty().clone()).collect();
    call::call_function(
        func_val,
        &arg_vals,
        Some(&static_arg_tys),
        Some(expected_ret),
        span,
        runtime,
    )
}

#[allow(clippy::too_many_lines)]
/// # Errors
/// Returns an error if evaluating `expr` (or any subexpression) raises an
/// unhandled runtime error.
///
/// # Panics
/// Panics only on internal invariant violations (e.g. a resolved path with no
/// segments), which indicate a bug in an earlier compiler pass rather than a
/// user-reachable condition.
pub fn eval_expr(
    expr: &TypedExpr,
    env: &mut Environment,
    runtime: &RuntimeRegistry,
) -> Result<Signal, MetelError> {
    match expr {
        TypedExpr::Literal(lit, ty, _) => {
            use crate::ast::{FloatKind, IntKind};
            let val = match lit {
                // Unsuffixed int/float literals are polymorphic; their resolved type
                // is determined by context (defaulting to i64/f64 when unconstrained).
                Literal::Int(n) => match ty {
                    crate::types::Type::I8 => Value::I8(*n as i8),
                    crate::types::Type::I16 => Value::I16(*n as i16),
                    crate::types::Type::I32 => Value::I32(*n as i32),
                    crate::types::Type::U8 => Value::U8(*n as u8),
                    crate::types::Type::U16 => Value::U16(*n as u16),
                    crate::types::Type::U32 => Value::U32(*n as u32),
                    crate::types::Type::U64 => Value::U64(*n as u64),
                    _ => Value::I64(*n), // i64 (default) and Int alias
                },
                Literal::Float(f) => match ty {
                    crate::types::Type::F32 => Value::F32(*f as f32),
                    _ => Value::F64(*f), // f64 (default) and Float alias
                },
                Literal::SizedInt { value, kind } => match kind {
                    IntKind::I8 => Value::I8(*value as i8),
                    IntKind::I16 => Value::I16(*value as i16),
                    IntKind::I32 => Value::I32(*value as i32),
                    IntKind::I64 => Value::I64(*value as i64),
                    IntKind::U8 => Value::U8(*value as u8),
                    IntKind::U16 => Value::U16(*value as u16),
                    IntKind::U32 => Value::U32(*value as u32),
                    IntKind::U64 => Value::U64(*value as u64),
                },
                Literal::SizedFloat { value, kind } => match kind {
                    FloatKind::F32 => Value::F32(*value as f32),
                    FloatKind::F64 => Value::F64(*value),
                },
                Literal::Char(c) => Value::Char(*c),
                Literal::Boolean(b) => Value::Boolean(*b),
                Literal::Str(s) => Value::Str(s.clone()),
                Literal::Unit => Value::Unit,
            };
            Ok(Signal::Value(val))
        }

        TypedExpr::Ident(name, binding, _, span) => {
            // Resolve by frozen identity first (metel-core#1052b): a lexical
            // local through the id-indexed frame, a global through the
            // `SymbolId` value registry. The name map / stdlib remain the
            // fallback for still-unmigrated sites and for a `None` binding.
            match binding {
                Some(crate::identity::BindingId::Local(id)) => {
                    if let Some(val) = env.get_local(*id) {
                        return Ok(Signal::Value(val));
                    }
                }
                Some(crate::identity::BindingId::Global(sym)) => {
                    // A top-level `let` / `var` has a live cell in the global
                    // slot table; every other global — `fn`, constructor,
                    // imported name — is a stable registered value.
                    if let Some(cell) = runtime.global_slot(*sym) {
                        return Ok(Signal::Value(cell.borrow().clone()));
                    }
                    if let Some(val) = runtime.get_symbol_value(*sym).cloned() {
                        return Ok(Signal::Value(val));
                    }
                }
                None => {}
            }
            match env.get(name).or_else(|| std_core_lookup(name, runtime)) {
                Some(val) => Ok(Signal::Value(val)),
                None => Err(MetelError::panic(
                    RuntimeErrorCode::R0003,
                    format!("undefined variable `{name}`"),
                    span,
                )),
            }
        }

        TypedExpr::Path(segments, _, _) => {
            // Unit enum variant: `Colour::Red` → Value::Enum { name: "Colour", variant: "Red", fields: {} }
            // A single-segment path is treated as an ident lookup.
            if segments.len() == 1 {
                let name = &segments[0];
                let span = expr.span();
                match env.get(name).or_else(|| std_core_lookup(name, runtime)) {
                    Some(val) => Ok(Signal::Value(val)),
                    None => Err(MetelError::panic(
                        RuntimeErrorCode::R0003,
                        format!("undefined variable `{name}`"),
                        span,
                    )),
                }
            } else {
                if let Some(val) = runtime
                    .resolve_path_value(segments)
                    .or_else(|| env.get(&segments.join("::")))
                {
                    return Ok(Signal::Value(val));
                }
                let name = segments[segments.len() - 2].clone();
                let variant = segments[segments.len() - 1].clone();
                Ok(Signal::Value(Value::Enum {
                    name,
                    // Unit enum variant resolved by surface path at runtime; no
                    // resolver context here, so dispatch falls back to the name.
                    type_id: None,
                    variant,
                    fields: HashMap::new(),
                }))
            }
        }

        TypedExpr::Tuple(elems, _, _) => {
            let mut vals = Vec::with_capacity(elems.len());
            for e in elems {
                let value = match eval_to_value(e, env, runtime)? {
                    ControlFlow::Continue(value) => value,
                    ControlFlow::Break(signal) => return Ok(signal),
                };
                vals.push(value);
            }
            Ok(Signal::Value(Value::Tuple(vals)))
        }

        TypedExpr::Array(elems, _, _) => {
            let mut vals = Vec::with_capacity(elems.len());
            for e in elems {
                let value = match eval_to_value(e, env, runtime)? {
                    ControlFlow::Continue(value) => value,
                    ControlFlow::Break(signal) => return Ok(signal),
                };
                vals.push(value);
            }
            Ok(Signal::Value(Value::Array(Rc::new(RefCell::new(vals)))))
        }

        TypedExpr::RecordLiteral { fields, .. } => {
            let mut values = HashMap::with_capacity(fields.len());
            for (name, expr) in fields {
                let value = match eval_to_value(expr, env, runtime)? {
                    ControlFlow::Continue(value) => value,
                    ControlFlow::Break(signal) => return Ok(signal),
                };
                values.insert(name.clone(), value);
            }
            Ok(Signal::Value(Value::Record { fields: values }))
        }

        TypedExpr::RepeatArray(elem, n, _, _) => {
            let val = match eval_to_value(elem, env, runtime)? {
                ControlFlow::Continue(value) => value,
                ControlFlow::Break(signal) => return Ok(signal),
            };
            let vals = (0..*n).map(|_| val.clone()).collect::<Vec<_>>();
            Ok(Signal::Value(Value::Array(Rc::new(RefCell::new(vals)))))
        }

        TypedExpr::BinOp(lhs, op, rhs, _, span) => {
            // Short-circuit logical ops before evaluating rhs.
            if matches!(op, BinOp::And) {
                let l = match eval_to_value(lhs, env, runtime)? {
                    ControlFlow::Continue(value) => value,
                    ControlFlow::Break(signal) => return Ok(signal),
                };
                return match l {
                    Value::Boolean(false) => Ok(Signal::Value(Value::Boolean(false))),
                    Value::Boolean(true) => eval_expr(rhs, env, runtime),
                    _ => Err(MetelError::internal(
                        "&&: expected boolean (typechecker should have caught this)",
                    )),
                };
            }
            if matches!(op, BinOp::Or) {
                let l = match eval_to_value(lhs, env, runtime)? {
                    ControlFlow::Continue(value) => value,
                    ControlFlow::Break(signal) => return Ok(signal),
                };
                return match l {
                    Value::Boolean(true) => Ok(Signal::Value(Value::Boolean(true))),
                    Value::Boolean(false) => eval_expr(rhs, env, runtime),
                    _ => Err(MetelError::internal(
                        "||: expected boolean (typechecker should have caught this)",
                    )),
                };
            }

            let lv = match eval_to_value(lhs, env, runtime)? {
                ControlFlow::Continue(value) => value,
                ControlFlow::Break(signal) => return Ok(signal),
            };
            let rv = match eval_to_value(rhs, env, runtime)? {
                ControlFlow::Continue(value) => value,
                ControlFlow::Break(signal) => return Ok(signal),
            };
            lvalue::eval_binop(op, lv, rv, span)
        }

        TypedExpr::RefTemp { init, mutable, .. } => {
            // Temporary lifetime extension: `init` has no addressable place of its
            // own, so materialize it into a fresh, independent cell rather than
            // sharing storage with anything — nothing else can ever reach this cell,
            // by construction (the typechecker only emits this node for a non-lvalue
            // operand).
            //
            // `init` can diverge (`&(return x)`, `&(break x)`) the same as any other
            // subexpression position, so its Signal must be checked before assuming
            // it produced a plain Value — propagate a control-flow signal upward
            // rather than force it through `into_value()`.
            let signal = eval_expr(init, env, runtime)?;
            let v = match signal {
                Signal::Value(v) => v,
                other => return Ok(other),
            };
            let cell = Rc::new(RefCell::new(v));
            Ok(Signal::Value(if *mutable {
                Value::MutReference(cell)
            } else {
                Value::Reference(cell)
            }))
        }

        TypedExpr::UnaryOp(op, operand, _, span) => {
            match op {
                // RFC-0110 §6: `&*p` is a *reborrow* — it must share the referent's
                // storage, not snapshot it into a fresh cell the way an lvalue *path*
                // does. Handled before the general path arm below for that reason.
                UnaryOp::Ref
                    if matches!(&**operand, TypedExpr::UnaryOp(UnaryOp::Deref, ..)) =>
                {
                    let TypedExpr::UnaryOp(_, inner, _, _) = &**operand else { unreachable!() };
                    let inner = match eval_to_value(inner, env, runtime)? {
                        ControlFlow::Continue(value) => value,
                        ControlFlow::Break(signal) => return Ok(signal),
                    };
                    return match inner {
                        Value::Reference(rc) | Value::MutReference(rc) => {
                            Ok(Signal::Value(Value::Reference(rc)))
                        }
                        // A reborrow of a *path* reference must carry the root+path
                        // through, not re-wrap it in a cell — re-wrapping produced a
                        // `Reference(Rc(FieldReference))` whose single-layer deref
                        // yielded the inner reference instead of the referent.
                        // `&var` reborrowed as `&` downgrades to shared.
                        Value::FieldReference { root, path }
                        | Value::MutFieldReference { root, path } => {
                            Ok(Signal::Value(Value::FieldReference { root, path }))
                        }
                        other => Ok(Signal::Value(Value::Reference(Rc::new(RefCell::new(other))))),
                    };
                }
                UnaryOp::RefMut
                    if matches!(&**operand, TypedExpr::UnaryOp(UnaryOp::Deref, ..)) =>
                {
                    let TypedExpr::UnaryOp(_, inner, _, _) = &**operand else { unreachable!() };
                    let inner = match eval_to_value(inner, env, runtime)? {
                        ControlFlow::Continue(value) => value,
                        ControlFlow::Break(signal) => return Ok(signal),
                    };
                    return match inner {
                        Value::MutReference(rc) => Ok(Signal::Value(Value::MutReference(rc))),
                        Value::MutFieldReference { root, path } => {
                            Ok(Signal::Value(Value::MutFieldReference { root, path }))
                        }
                        other => Err(MetelError::panic(
                            RuntimeErrorCode::R0003,
                            format!("cannot take `&var` through a shared reference: {other:?}"),
                            span,
                        )),
                    };
                }
                UnaryOp::Ref => return match &**operand {
                    TypedExpr::Ident(name, binding, _, _) => ident_rc(name, *binding, env, runtime)
                        .map(|rc| Signal::Value(Value::Reference(rc)))
                        .ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0003, format!("undefined variable `{name}`"), span)),
                    other if is_lvalue_path_typed(other) => {
                        let (root_name, path) = match build_mut_path(other, env, runtime, span)? {
                            ControlFlow::Continue(path) => path,
                            ControlFlow::Break(signal) => return Ok(signal),
                        };
                        let root = env.get_rc(&root_name).ok_or_else(|| MetelError::panic(
                            RuntimeErrorCode::R0003, format!("undefined variable `{root_name}`"), span))?;
                        Ok(Signal::Value(Value::FieldReference { root, path }))
                    }
                    _ => Err(MetelError::internal("address-of requires an addressable lvalue (identifier, field access, tuple access, or array index)")),
                },
                UnaryOp::RefMut => return match &**operand {
                    TypedExpr::Ident(name, binding, _, _) => ident_rc(name, *binding, env, runtime)
                        .map(|rc| Signal::Value(Value::MutReference(rc)))
                        .ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0003, format!("undefined variable `{name}`"), span)),
                    other if is_lvalue_path_typed(other) => {
                        let (root_name, path) = match build_mut_path(other, env, runtime, span)? {
                            ControlFlow::Continue(path) => path,
                            ControlFlow::Break(signal) => return Ok(signal),
                        };
                        let root = env.get_rc(&root_name).ok_or_else(|| MetelError::panic(
                            RuntimeErrorCode::R0003, format!("undefined variable `{root_name}`"), span))?;
                        Ok(Signal::Value(Value::MutFieldReference { root, path }))
                    }
                    _ => Err(MetelError::internal("mutable address-of requires an addressable lvalue")),
                },
                _ => {}
            }
            let v = match eval_to_value(operand, env, runtime)? {
                ControlFlow::Continue(value) => value,
                ControlFlow::Break(signal) => return Ok(signal),
            };
            let result = match (op, v) {
                (UnaryOp::Neg, Value::I64(n)) => Value::I64(n.wrapping_neg()),
                (UnaryOp::Neg, Value::I8(n)) => Value::I8(n.wrapping_neg()),
                (UnaryOp::Neg, Value::I16(n)) => Value::I16(n.wrapping_neg()),
                (UnaryOp::Neg, Value::I32(n)) => Value::I32(n.wrapping_neg()),
                (UnaryOp::Neg, Value::F64(f)) => Value::F64(-f),
                (UnaryOp::Neg, Value::F32(f)) => Value::F32(-f),
                (UnaryOp::Not, Value::Boolean(b)) => Value::Boolean(!b),
                (UnaryOp::Deref, Value::Reference(rc) | Value::MutReference(rc)) => {
                    rc.borrow().clone()
                }
                (
                    UnaryOp::Deref,
                    Value::FieldReference { root, path } | Value::MutFieldReference { root, path },
                ) => read_path(&root.borrow(), &path, span)?,
                (UnaryOp::Neg, _) => {
                    return Err(MetelError::internal(
                        "unary `-`: expected numeric type (typechecker should have caught this)",
                    ))
                }
                (UnaryOp::Not, _) => {
                    return Err(MetelError::internal(
                        "unary `!`: expected boolean (typechecker should have caught this)",
                    ))
                }
                (UnaryOp::Deref, _) => {
                    return Err(MetelError::internal(
                        "unary `*`: expected pointer (typechecker should have caught this)",
                    ))
                }
                _ => unreachable!("Ref/RefMut handled above"),
            };
            Ok(Signal::Value(result))
        }

        TypedExpr::Cast {
            expr: inner,
            target_type,
            span,
            ..
        } => {
            let v = match eval_to_value(inner, env, runtime)? {
                ControlFlow::Continue(value) => value,
                ControlFlow::Break(signal) => return Ok(signal),
            };
            // Dispatch through From impl using the full aspect-signature key
            // "Target::From<Source>::from", then fall back to "Target::from"
            // (used by built-in Int::from / Float::from which have no type arg).
            if let crate::ast::TypeExpr::Named(target_name, _) = target_type {
                let from_fn = runtime_type_name(&v)
                    .and_then(|source| runtime.get_from_method(target_name, source));
                if let Some(f) = from_fn {
                    return call::call_function(
                        Value::Callable(f.body),
                        &[v],
                        None,
                        None,
                        span,
                        runtime,
                    );
                }
            }
            // Identity cast fallback (same type, no from registered).
            Ok(Signal::Value(v))
        }

        TypedExpr::TupleAccess {
            object,
            index,
            span,
            ..
        } => {
            let v = match eval_to_value(object, env, runtime)? {
                ControlFlow::Continue(value) => value,
                ControlFlow::Break(signal) => return Ok(signal),
            };
            let v = deref_value(&v, span)?.unwrap_or(v);
            match v {
                // R0005: same defensive-fallback reasoning as lvalue.rs's own
                // TypedPlace::Tuple site -- metel-core#987, #986.
                Value::Tuple(elems) => {
                    elems
                        .into_iter()
                        .nth(*index)
                        .map(Signal::Value)
                        .ok_or_else(|| {
                            MetelError::panic(
                                RuntimeErrorCode::R0005,
                                format!("tuple index {index} out of bounds"),
                                span,
                            )
                        })
                }
                _ => Err(MetelError::internal(
                    "tuple access on non-tuple (typechecker should have caught this)",
                )),
            }
        }

        TypedExpr::Index {
            object,
            index,
            span,
            ..
        } => {
            let arr = match eval_to_value(object, env, runtime)? {
                ControlFlow::Continue(value) => value,
                ControlFlow::Break(signal) => return Ok(signal),
            };
            let arr = match deref_value(&arr, span)? {
                Some(value) => value,
                None => arr,
            };
            let idx = match eval_to_value(index, env, runtime)? {
                ControlFlow::Continue(value) => value,
                ControlFlow::Break(signal) => return Ok(signal),
            };
            let i: usize = match idx {
                Value::U64(u) => u as usize,
                _ => {
                    return Err(MetelError::internal(
                        "index: expected u64 index (typechecker should have caught this)",
                    ))
                }
            };
            match arr {
                Value::Array(rc) => {
                    let borrowed = rc.borrow();
                    if i >= borrowed.len() {
                        Err(MetelError::panic(
                            RuntimeErrorCode::R0004,
                            format!("index {i} out of bounds (len {})", borrowed.len()),
                            span,
                        ))
                    } else {
                        Ok(Signal::Value(borrowed[i].clone()))
                    }
                }
                _ => Err(MetelError::internal(
                    "index: expected Array (typechecker should have caught this)",
                )),
            }
        }

        TypedExpr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            match eval_expr(condition, env, runtime)? {
                Signal::Value(Value::Boolean(true)) => eval_block(then_branch, env, runtime),
                Signal::Value(Value::Boolean(false)) => match else_branch {
                    Some(branch) => eval_block(branch, env, runtime),
                    None => Ok(Signal::Value(Value::Unit)),
                },
                Signal::Value(_) => Err(MetelError::internal(
                    "if: expected boolean condition (typechecker should have caught this)",
                )),
                other => Ok(other), // propagate Return from condition
            }
        }

        TypedExpr::Loop { body, .. } => loop {
            match eval_block(body, env, runtime)? {
                Signal::Value(_) | Signal::Continue => {}
                Signal::Break(val) => return Ok(Signal::Value(val)),
                Signal::Return(v) => return Ok(Signal::Return(v)),
            }
        },

        TypedExpr::Match(m) => {
            // RFC-0108: a reference-typed scrutinee matches against the referent's
            // patterns — unwrap any reference layers before matching, using the same
            // `deref_value` helper method dispatch already uses. `match_pattern` then
            // only ever sees a plain value, exactly as before.
            let scrutinee_raw = match eval_to_value(&m.scrutinee, env, runtime)? {
                ControlFlow::Continue(value) => value,
                ControlFlow::Break(signal) => return Ok(signal),
            };
            let scrutinee = deref_value(&scrutinee_raw, &m.span)?.unwrap_or(scrutinee_raw);
            for arm in &m.arms {
                let mut bindings: Vec<pattern::PatternBinding> = Vec::new();
                if !pattern::match_pattern(&arm.pattern, &scrutinee, &mut bindings) {
                    continue;
                }
                // Evaluate the guard (if any) in a scope that includes pattern bindings.
                if let Some(guard) = &arm.guard {
                    env.push_scope();
                    for (name, id, v) in &bindings {
                        env.define_binding(*id, name, v.clone());
                    }
                    let guard_val = match eval_to_value(guard, env, runtime)? {
                        ControlFlow::Continue(value) => value,
                        ControlFlow::Break(signal) => {
                            env.pop_scope();
                            return Ok(signal);
                        }
                    };
                    env.pop_scope();
                    match guard_val {
                        Value::Boolean(true) => {}
                        Value::Boolean(false) => continue,
                        _ => return Err(MetelError::internal(
                            "match guard: expected boolean (typechecker should have caught this)",
                        )),
                    }
                }
                // Execute the arm body in a scope with pattern bindings.
                env.push_scope();
                for (name, id, v) in bindings {
                    env.define_binding(id, &name, v);
                }
                let result = eval_block(&arm.body, env, runtime);
                env.pop_scope();
                return result;
            }
            Err(MetelError::panic(
                RuntimeErrorCode::R0006,
                "match: no arm matched scrutinee",
                &m.span,
            ))
        }

        // RFC-0078 §3.3: inhabited-singleton coercion. No runtime tag check is
        // needed — the typecheck-time uninhabited-variant exemption that licenses
        // this node guarantees no other variant could ever have been constructed.
        TypedExpr::SingletonCoerce { inner, field, .. } => {
            let value = match eval_to_value(inner, env, runtime)? {
                ControlFlow::Continue(value) => value,
                ControlFlow::Break(signal) => return Ok(signal),
            };
            match value {
                Value::Enum { mut fields, .. } => {
                    fields.remove(field).map(Signal::Value).ok_or_else(|| {
                        MetelError::internal(format!("singleton coercion: missing field `{field}`"))
                    })
                }
                _ => Err(MetelError::internal("singleton coercion on non-enum value")),
            }
        }

        // RFC-0008 §6: implicit coercion to `dyn Aspect`. Everything that could
        // reject this was already checked at construction time (object safety by
        // `ty_at`'s `TypeExpr::DynAspect` arm; `inner`'s type satisfying the
        // aspect by `maybe_dyn_coerce`) — nothing left to check here, just wrap.
        TypedExpr::DynCoerce {
            inner,
            aspect_id,
            ty,
            ..
        } => {
            let value = match eval_to_value(inner, env, runtime)? {
                ControlFlow::Continue(value) => value,
                ControlFlow::Break(signal) => return Ok(signal),
            };
            let type_id = runtime.resolve_value_type_id(&value).ok_or_else(|| {
                MetelError::internal("dyn Aspect coercion: value has no resolvable concrete type")
            })?;
            let crate::types::Type::Dyn { aspect, type_args } = ty else {
                unreachable!("TypedExpr::DynCoerce::ty is always Type::Dyn")
            };
            Ok(Signal::Value(Value::DynAspect {
                data: Rc::new(RefCell::new(value)),
                type_id,
                aspect_id: *aspect_id,
                aspect_name: aspect.clone(),
                type_args: type_args.clone(),
            }))
        }

        // Issue #229: `return`/`break`/`continue` as expressions. Mechanical
        // port of the former `eval_stmt` bodies -- `eval_block`/`TypedExpr::If`/
        // `TypedExpr::Loop` already thread arbitrary `Signal`s transparently.
        TypedExpr::Return(r) => {
            let val = match &r.value {
                Some(e) => match eval_to_value(e, env, runtime)? {
                    ControlFlow::Continue(value) => value,
                    ControlFlow::Break(signal) => return Ok(signal),
                },
                None => Value::Unit,
            };
            Ok(Signal::Return(val))
        }
        TypedExpr::Break(b) => {
            let val = match &b.value {
                Some(e) => match eval_to_value(e, env, runtime)? {
                    ControlFlow::Continue(value) => value,
                    ControlFlow::Break(signal) => return Ok(signal),
                },
                None => Value::Unit,
            };
            Ok(Signal::Break(val))
        }
        TypedExpr::Continue(_) => Ok(Signal::Continue),

        TypedExpr::Assign {
            target,
            op,
            value,
            span,
            ..
        } => eval_assign_expr(target, op, value, span, env, runtime),

        TypedExpr::StructLiteral {
            path,
            fields,
            type_id,
            ..
        } => eval_struct_literal_expr(path, fields, *type_id, env, runtime),

        TypedExpr::FieldAccess {
            object,
            field,
            span,
            ..
        } => {
            let mut val = match eval_to_value(object, env, runtime)? {
                ControlFlow::Continue(value) => value,
                ControlFlow::Break(signal) => return Ok(signal),
            };
            if let Some(deref) = deref_value(&val, span)? {
                val = deref;
            }
            let (Value::Record { fields }
            | Value::Struct { fields, .. }
            | Value::Enum { fields, .. }) = &val
            else {
                return Err(MetelError::internal(
                    "field access on non-record/struct/enum (typechecker should have caught this)",
                ));
            };
            fields
                .get(field)
                .cloned()
                .map(Signal::Value)
                .ok_or_else(|| {
                    MetelError::panic(
                        RuntimeErrorCode::R0008,
                        format!("no field `{field}` on value"),
                        span,
                    )
                })
        }

        TypedExpr::MethodCall {
            receiver,
            method,
            args,
            ty,
            dispatch,
            span,
        } => eval_method_call_expr(receiver, method, args, dispatch, ty, span, env, runtime),

        TypedExpr::Call {
            callee,
            args,
            ty,
            callee_id,
            span,
            ..
        } => eval_call_expr(callee, args, *callee_id, ty, span, env, runtime),

        TypedExpr::Closure {
            captures,
            capture_ids,
            call_mutation,
            params,
            param_ids,
            body,
            ty,
            span,
            ..
        } => {
            let captured = env.capture_closure(captures, capture_ids, span)?;
            Ok(Signal::Value(Value::Callable(RuntimeCallable::Closure(
                Rc::new(ClosureValue {
                    name: None,
                    captures: captures.clone(),
                    capture_ids: capture_ids.clone(),
                    params: params.clone(),
                    param_ids: param_ids.clone(),
                    body: ClosureBody::Typed(body.clone()),
                    captured,
                    call_mutation: *call_mutation,
                    in_call: Cell::new(false),
                    type_ctx: None,
                    fun_type: Some(ty.clone()),
                }),
            ))))
        }

        TypedExpr::GenericClosure {
            name,
            captures,
            capture_ids,
            call_mutation,
            params,
            param_ids,
            body,
            span,
            ..
        } => {
            let captured = env.capture_closure(captures, capture_ids, span)?;
            Ok(Signal::Value(Value::Callable(RuntimeCallable::Closure(
                Rc::new(ClosureValue {
                    name: name.clone(),
                    captures: captures.clone(),
                    capture_ids: capture_ids.clone(),
                    params: params.clone(),
                    param_ids: param_ids.clone(),
                    body: ClosureBody::Untyped(body.clone()),
                    captured,
                    call_mutation: *call_mutation,
                    in_call: Cell::new(false),
                    type_ctx: env.type_ctx.clone(),
                    fun_type: None,
                }),
            ))))
        }
    }
}

#[cfg(test)]
mod frame_tests {
    //! metel-core#1052b -- the id-indexed activation frame and its name-map
    //! fallback.

    use super::{Environment, Value};
    use crate::identity::LocalId;

    fn as_i64(v: Option<Value>) -> Option<i64> {
        match v {
            Some(Value::I64(n)) => Some(n),
            _ => None,
        }
    }

    #[test]
    fn define_binding_is_readable_by_local_id() {
        let mut env = Environment::new();
        let id = LocalId(0x1234);
        env.define_binding(Some(id), "x", Value::I64(7));
        assert_eq!(as_i64(env.get_local(id)), Some(7));
        // The name map is written in step so unmigrated paths keep working.
        assert_eq!(as_i64(env.get("x")), Some(7));
    }

    #[test]
    fn a_name_only_binding_has_no_frame_slot() {
        let mut env = Environment::new();
        env.define("y", Value::I64(1));
        assert!(env.get_local(LocalId(0x9999)).is_none());
        assert_eq!(as_i64(env.get("y")), Some(1));
    }

    #[test]
    fn distinct_local_ids_do_not_alias_when_the_name_is_reused() {
        // Two bindings that share the spelling `n` but sit at different
        // lexical paths hash to different `LocalId`s and keep independent
        // slots, even though the later one shadows the former in the name map.
        let mut env = Environment::new();
        let outer = LocalId(1);
        let inner = LocalId(2);
        env.define_binding(Some(outer), "n", Value::I64(10));
        env.define_binding(Some(inner), "n", Value::I64(20));
        assert_eq!(as_i64(env.get_local(outer)), Some(10));
        assert_eq!(as_i64(env.get_local(inner)), Some(20));
        assert_eq!(as_i64(env.get("n")), Some(20));
    }

    #[test]
    fn capture_clone_drops_frame_slots_but_keeps_the_name_snapshot() {
        // A capture snapshot rebuilds bindings under fresh name-keyed cells;
        // the id frame is intentionally cleared so a body reference to a
        // captured binding resolves through the name-map fallback rather than
        // a cell that has drifted out of sync.
        let mut env = Environment::new();
        let id = LocalId(42);
        env.define_binding(Some(id), "c", Value::I64(5));
        let snapshot = env.capture_clone();
        assert!(snapshot.get_local(id).is_none());
        assert_eq!(as_i64(snapshot.get("c")), Some(5));
    }

    #[test]
    fn capture_closure_installs_captures_in_the_frame_by_enclosing_id() {
        // metel-core#1052b-2: a closure body's reference to a captured variable
        // resolves to the *enclosing* binding's `LocalId`, so that id keys the
        // capture cell in the closure environment's frame.
        use crate::ast::{CaptureSpec, Span};
        let mut outer = Environment::new();
        let n_id = LocalId(7);
        outer.define_binding(Some(n_id), "n", Value::I64(3));
        let sp = Span::new(0, 0, "t");
        let caps = vec![CaptureSpec::Clone {
            name: "n".to_string(),
            span: sp.clone(),
        }];
        let closure_env = outer.capture_closure(&caps, &[Some(n_id)], &sp).unwrap();
        assert_eq!(as_i64(closure_env.get_local(n_id)), Some(3));
        assert_eq!(as_i64(closure_env.get("n")), Some(3));
    }

    #[test]
    fn mut_ref_capture_shares_one_cell_across_name_and_id() {
        use crate::ast::{CaptureSpec, Span};
        let mut outer = Environment::new();
        let n_id = LocalId(8);
        outer.define_binding(Some(n_id), "n", Value::I64(0));
        let sp = Span::new(0, 0, "t");
        let caps = vec![CaptureSpec::MutRef {
            name: "n".to_string(),
            span: sp.clone(),
        }];
        let closure_env = outer.capture_closure(&caps, &[Some(n_id)], &sp).unwrap();
        // One cell backs both keys: a write via the name map is seen by the
        // id-indexed read.
        assert!(closure_env.set("n", Value::I64(42)));
        assert_eq!(as_i64(closure_env.get_local(n_id)), Some(42));
    }

    #[test]
    fn ident_rc_prefers_the_frame_cell_over_the_name_map() {
        // `&x` / `&var x` resolves the same cell the frame holds for a local
        // binding, without a name lookup, when the id is known.
        use super::{ident_rc, RuntimeRegistry};
        use crate::identity::BindingId;

        let mut env = Environment::new();
        let id = LocalId(99);
        env.define_binding(Some(id), "x", Value::I64(3));
        let runtime = RuntimeRegistry::new();
        let cell =
            ident_rc("x", Some(BindingId::Local(id)), &env, &runtime).expect("resolves by id");
        assert_eq!(as_i64(Some(cell.borrow().clone())), Some(3));

        // A name the frame doesn't know about still falls back to the name map.
        env.define("y", Value::I64(9));
        let cell = ident_rc("y", None, &env, &runtime).expect("falls back by name");
        assert_eq!(as_i64(Some(cell.borrow().clone())), Some(9));
    }
}
