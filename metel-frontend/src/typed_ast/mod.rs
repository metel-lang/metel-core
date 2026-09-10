// ── Typed AST ─────────────────────────────────────────────────────────────────
// Mirrors the untyped AST but every expression node carries resolved type information.
// Generic declarations do not appear here — they are monomorphised by the type checker.

use std::collections::HashMap;

use crate::ast::{
    AspectMethod, AssignOp, BinOp, Block, CaptureSpec, FieldDef, GenericParam, Literal, Param,
    Polarity, Span, TypeExpr, UnaryOp, VariantDef,
};
use crate::identity::{BindingId, FieldId, LocalId, VariantId};
use crate::symbols::SymbolId;
use crate::typeinference::{TypeDefinitionRegistry, TypeScheme};
use crate::types::{CallMultiplicity, CallMutation, Type};

/// How a method call is dispatched, resolved by the elaboration pass.
#[derive(Debug, Clone, PartialEq)]
pub enum MethodDispatch {
    /// Dispatch could not be statically resolved; the evaluator falls back to runtime lookup.
    Dynamic,
    /// Direct method call on the concrete receiver type (not through an aspect).
    Inherent,
    /// Dispatches through a named aspect. `aspect_id` is the stable identity of the aspect.
    Aspect { aspect_id: SymbolId },
}

/// A resolved import entry: the stable source location and symbol identity of an imported name.
#[derive(Debug, Clone)]
pub struct ResolvedImportRef {
    pub source_module: Vec<String>,
    pub canonical_name: String,
    /// Stable cross-module identity assigned by the name resolver. `None` for
    /// glob-resolved names that have no explicit binding (e.g. std auto-imports).
    pub symbol_id: Option<SymbolId>,
}

// ── Program ───────────────────────────────────────────────────────────────────

/// A fully typed program — list of typed declarations.
/// Used by the old single-module pipeline; kept for compatibility.
pub type TypedProgram = Vec<TypedDecl>;

/// A single typed module, produced by `check_graph`.
#[derive(Debug, Clone)]
pub struct TypedModule {
    pub module_path: Vec<String>,
    pub decls: Vec<TypedDecl>,
    /// Alias → canonical name for imports declared `import mod::name as alias`.
    /// The evaluator registers these so that `alias` resolves to the same value as `name`.
    pub import_aliases: HashMap<String, String>,
    /// Every explicitly imported name: `local_name` → resolved import reference.
    /// Used by `evaluate_graph` to seed each module's environment from its dependencies.
    pub imported_names: HashMap<String, ResolvedImportRef>,
    /// The full type-scheme environment produced by the typechecker for this module.
    /// Used at runtime to run `construct_block` for generic function bodies
    /// (`ClosureBody::Untyped`) without a separate untyped evaluator pipeline.
    pub scheme_env: HashMap<String, TypeScheme>,
}

/// The output of `check_graph` — one typed module per loaded module, in
/// topological order (dependencies before dependents).
#[derive(Debug)]
pub struct TypedModuleGraph {
    pub modules: Vec<TypedModule>,
    /// Accumulated type-definition registry produced during type-checking, containing
    /// all struct, enum, aspect, and method definitions visible after the full graph is
    /// checked. Available to the evaluator for construction-at-call-time of generic bodies.
    pub type_registry: TypeDefinitionRegistry,
}

// ── Typed Declarations ────────────────────────────────────────────────────────

/// Mirrors `ast::Decl` but with typed expressions.
/// Struct/Enum/Aspect variants carry no runtime data — the evaluator ignores them.
/// They exist for structural completeness and future tooling (reflection, docs, LSP).
#[derive(Debug, Clone)]
pub enum TypedDecl {
    Let(TypedLetDecl),
    Mut(TypedMutDecl),
    Fun(TypedFunDecl),
    Struct(#[allow(dead_code)] TypedStructDecl),
    Enum(#[allow(dead_code)] TypedEnumDecl),
    Impl(TypedImplBlock),
    Aspect(#[allow(dead_code)] TypedAspectDecl),
    Stmt(Box<TypedStmt>),
}

#[derive(Debug, Clone)]
pub struct TypedLetDecl {
    pub name: String,
    #[allow(dead_code)] // kept for future tooling (hover types, LSP)
    pub type_ann: Option<TypeExpr>,
    pub value: TypedExpr,
    /// Stable identity of a top-level (module-level) `let` (ADR-0042). The evaluator
    /// registers the binding's value under this id, in addition to its lexical-env
    /// binding, once its Pass 2 initializer has run — so `Call::callee_id` dispatch
    /// works for a top-level first-class function value the same way it already does
    /// for `fn` declarations. `None` for block-local/`for`-init `let`s, which stay
    /// name-keyed only (ADR-0041 design: locals are never given a top-level identity).
    pub def_id: Option<SymbolId>,
    /// Lexical identity of a block-local / `for`-init `let` (ADR-0054 /
    /// metel-core#1052). `None` for a module-level `let` (which is a
    /// `SymbolId`, carried on `def_id`) and without identity context.
    pub local_id: Option<LocalId>,
    #[allow(dead_code)] // kept for future error messages
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct TypedMutDecl {
    pub name: String,
    #[allow(dead_code)] // kept for future tooling (hover types, LSP)
    pub type_ann: Option<TypeExpr>,
    pub value: TypedExpr,
    /// See `TypedLetDecl::def_id` — same identity, same rationale, for `mut`.
    pub def_id: Option<SymbolId>,
    /// See `TypedLetDecl::local_id`.
    pub local_id: Option<LocalId>,
    #[allow(dead_code)] // kept for future error messages
    pub span: Span,
}

/// The body of a typed function declaration.
///
/// Monomorphic functions have a fully typed body; polymorphic functions
/// (those with quantified type variables) keep the original untyped AST body
/// because there is no single concrete instantiation to type-check against.
/// The evaluator uses runtime values, not type annotations, so this is safe.
#[derive(Debug, Clone)]
pub enum FunBody {
    Typed(TypedBlock),
    Generic(Block),
    /// A stdlib `native(@…)` function: no Metel body. The evaluator dispatches
    /// to the host implementation registered for this [`NativeKey`] (METEL-182).
    Native(crate::native_keys::NativeKey),
}

#[derive(Debug, Clone)]
pub struct TypedFunDecl {
    pub name: String,
    #[allow(dead_code)] // kept for future reflection / documentation generation
    pub generics: Vec<GenericParam>,
    pub params: Vec<Param>,
    /// Lexical identity of each parameter (ADR-0054 / metel-core#1052), parallel
    /// to `params`. Empty without identity context; entries `None` where a param
    /// span was not a recorded binding site.
    pub param_ids: Vec<Option<LocalId>>,
    #[allow(dead_code)] // kept for future reflection / documentation generation
    pub return_type: Option<TypeExpr>,
    pub body: FunBody,
    /// `Some` only for overloaded free-function definitions (METEL-180): the
    /// evaluator registers the definition under this id (names cannot
    /// disambiguate overloads) and call sites dispatch via `Call::callee_id`.
    pub symbol_id: Option<SymbolId>,
    /// Stable identity of an ordinary (non-overloaded) top-level function (METEL-187 /
    /// ADR-0041). The evaluator registers the definition under this id in addition to
    /// its lexical-env binding, and direct call sites dispatch through it via
    /// `Call::callee_id`. `None` for methods, nested/local functions, and the
    /// single-program path (no resolver). Mutually exclusive with `symbol_id`.
    pub def_id: Option<SymbolId>,
    #[allow(dead_code)] // kept for future error messages
    pub span: Span,
}

/// Carried in `TypedDecl` for structural completeness; the evaluator produces no
/// runtime representation for struct/enum declarations.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct TypedStructDecl {
    pub name: String,
    pub generics: Vec<GenericParam>,
    pub fields: Vec<FieldDef>,
    pub span: Span,
}

/// Carried in `TypedDecl` for structural completeness; the evaluator produces no
/// runtime representation for struct/enum declarations.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct TypedEnumDecl {
    pub name: String,
    pub generics: Vec<GenericParam>,
    pub variants: Vec<VariantDef>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct TypedImplBlock {
    /// See `ast::ImplBlock::polarity`. Not yet coherence-checked (issue #264).
    #[allow(dead_code)] // set by construction.rs; not yet read downstream
    pub polarity: Polarity,
    /// See `ast::ImplBlock::generics` (RFC-0036 conditional impls). `where_clause` is
    /// consumed during construction and not carried to the typed side, same as
    /// `TypedFunDecl` already drops it.
    #[allow(dead_code)] // kept for future reflection, same as TypedFunDecl.generics
    pub generics: Vec<GenericParam>,
    pub aspect_name: Option<String>,
    /// Stable identity of the aspect this impl satisfies.  `None` for inherent impls.
    /// Populated by the typechecker construction pass when `names.symbols` is available.
    pub aspect_id: Option<SymbolId>,
    /// Stable identity of the target type, used to register this impl's methods in the
    /// SymbolId-keyed runtime type registry (METEL-185). `None` without resolver context.
    pub target_type_id: Option<SymbolId>,
    pub aspect_type_args: Vec<TypeExpr>,
    pub target_type: TypeExpr,
    pub methods: Vec<TypedFunDecl>,
    #[allow(dead_code)] // kept for future error messages
    pub span: Span,
}

/// Carried in `TypedDecl` for structural completeness; the evaluator produces no
/// runtime representation for aspect declarations.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct TypedAspectDecl {
    pub name: String,
    pub generics: Vec<String>,
    pub methods: Vec<AspectMethod>,
    pub span: Span,
}

// ── Typed Statements ──────────────────────────────────────────────────────────

/// Mirrors `ast::Stmt` but with typed expressions.
#[derive(Debug, Clone)]
pub enum TypedStmt {
    While(TypedWhileStmt),
    For(Box<TypedForStmt>),
    ForIn(Box<TypedForInStmt>),
    Expr(TypedExpr),
}

#[derive(Debug, Clone)]
pub struct TypedWhileStmt {
    pub condition: TypedExpr,
    pub body: TypedBlock,
    #[allow(dead_code)] // kept for future error messages
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct TypedForStmt {
    pub init: Option<TypedForInit>,
    pub condition: Option<TypedExpr>,
    pub step: Option<TypedExpr>,
    pub body: TypedBlock,
    #[allow(dead_code)] // kept for future error messages
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TypedForInit {
    Let(TypedLetDecl),
    Mut(TypedMutDecl),
    Expr(TypedExpr),
}

#[derive(Debug, Clone)]
pub struct TypedForInStmt {
    pub binding: String,
    /// Lexical identity of the loop binding (ADR-0054 / metel-core#1052). One
    /// `LocalId` per lexical binding, reused across iterations — the frame is
    /// re-slotted, not renumbered.
    pub binding_id: Option<LocalId>,
    pub mutable: bool,
    pub iterable: TypedExpr,
    pub body: TypedBlock,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct TypedReturnExpr {
    pub value: Option<Box<TypedExpr>>,
    #[allow(dead_code)] // kept for future error messages
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct TypedBreakExpr {
    pub value: Option<Box<TypedExpr>>,
    #[allow(dead_code)] // kept for future error messages
    pub span: Span,
}

// ── Typed Block ───────────────────────────────────────────────────────────────

/// `{ decl* expr? }` — mirrors `ast::Block` with typed contents.
#[derive(Debug, Clone)]
pub struct TypedBlock {
    pub stmts: Vec<TypedDecl>,
    pub tail: Option<Box<TypedExpr>>,
    #[allow(dead_code)] // kept for future error messages
    pub span: Span,
}

// ── Typed lvalue places ───────────────────────────────────────────────────────

/// A typed assignment target.  Unlike `ast::AssignTarget`, every sub-expression
/// (including index expressions) is fully typed so the evaluator can use
/// `eval_expr` instead of falling back to the untyped evaluator.
#[derive(Debug, Clone)]
pub enum TypedPlace {
    Ident(String, Span),
    Deref {
        object: Box<TypedExpr>,
        span: Span,
    },
    Field {
        object: Box<TypedPlace>,
        field: String,
        span: Span,
    },
    Tuple {
        object: Box<TypedPlace>,
        index: usize,
        span: Span,
    },
    Index {
        object: Box<TypedPlace>,
        index: Box<TypedExpr>,
        span: Span,
    },
}

// ── Typed Expressions ─────────────────────────────────────────────────────────

/// Mirrors `ast::Expr` but every variant includes a `Type` field.
/// This is the central type: after type inference, every expression is annotated with its type.
#[derive(Debug, Clone)]
pub enum TypedExpr {
    Literal(Literal, Type, Span),
    /// A bare value reference. The second field is the resolved identity of the
    /// binding it denotes (ADR-0054 / metel-core#1052) — `BindingId::Local` for
    /// a lexical binding, `BindingId::Global` for a top-level / imported
    /// declaration. `None` when no identity context was available (the
    /// single-program path, or a generic body reconstructed at runtime); the
    /// spelling is retained for diagnostics and the pre-#1052 evaluator.
    Ident(String, Option<BindingId>, Type, Span),
    Path(Vec<String>, Type, Span),
    Tuple(Vec<TypedExpr>, Type, Span),
    Array(Vec<TypedExpr>, Type, Span),
    RecordLiteral {
        fields: Vec<(String, TypedExpr)>,
        ty: Type,
        span: Span,
    },
    RepeatArray(Box<TypedExpr>, u64, Type, Span),
    BinOp(Box<TypedExpr>, BinOp, Box<TypedExpr>, Type, Span),
    UnaryOp(UnaryOp, Box<TypedExpr>, Type, Span),
    /// `&<rvalue>` / `&var <rvalue>` — a reference to a value with no addressable
    /// place of its own (temporary lifetime extension, matching Rust/C++:
    /// `foo(&Vec::new())`, `foo(&mut Vec::new())`). `init` is materialized into a
    /// fresh, independent storage cell at evaluation time. Nothing outside this
    /// expression can ever alias that cell, so the "shared XOR exclusive" rule
    /// (RFC-0122, not yet enforced) can never be violated through it either way —
    /// both forms are sound. `mutable` selects `Value::Reference` vs
    /// `Value::MutReference` at evaluation.
    RefTemp {
        init: Box<TypedExpr>,
        mutable: bool,
        ty: Type,
        span: Span,
    },
    Assign {
        target: TypedPlace,
        op: AssignOp,
        value: Box<TypedExpr>,
        ty: Type,
        span: Span,
    },
    Call {
        callee: Box<TypedExpr>,
        args: Vec<TypedExpr>,
        ty: Type,
        /// Resolved overload definition (METEL-180): when the callee is an
        /// overloaded free function, construction stamps the selected
        /// candidate's `SymbolId` here and the evaluator dispatches through its
        /// symbol registry instead of evaluating `callee` by name.
        callee_id: Option<SymbolId>,
        span: Span,
    },
    MethodCall {
        receiver: Box<TypedExpr>,
        method: String,
        args: Vec<TypedExpr>,
        ty: Type,
        dispatch: MethodDispatch,
        span: Span,
    },
    FieldAccess {
        object: Box<TypedExpr>,
        field: String,
        /// Stable identity of the selected field declaration (ADR-0054 / #1062).
        /// Resolved from the `MemberTable` at construction, keyed by
        /// `(owning type SymbolId, field name)`. `None` when no identity context
        /// is available or member resolution failed — an explicit
        /// diagnostic-recovery state, never a fabricated id. `field` is retained
        /// for diagnostics and the (pre-#1063) evaluator.
        field_id: Option<FieldId>,
        ty: Type,
        span: Span,
    },
    TupleAccess {
        object: Box<TypedExpr>,
        index: usize,
        ty: Type,
        span: Span,
    },
    Index {
        object: Box<TypedExpr>,
        index: Box<TypedExpr>,
        ty: Type,
        span: Span,
    },
    Cast {
        expr: Box<TypedExpr>,
        target_type: TypeExpr,
        ty: Type,
        span: Span,
    },
    Match(TypedMatchExpr),
    If {
        condition: Box<TypedExpr>,
        then_branch: TypedBlock,
        else_branch: Option<TypedBlock>,
        ty: Type,
        span: Span,
    },
    Loop {
        body: TypedBlock,
        ty: Type,
        span: Span,
    },
    Closure {
        captures: Vec<CaptureSpec>,
        /// Lexical identity of the enclosing-scope binding each capture names
        /// (ADR-0054 / metel-core#1052), parallel to `captures`.
        capture_ids: Vec<Option<LocalId>>,
        call_multiplicity: CallMultiplicity,
        call_mutation: CallMutation,
        params: Vec<Param>,
        /// Lexical identity of each closure parameter, parallel to `params`.
        param_ids: Vec<Option<LocalId>>,
        #[allow(dead_code)] // kept for future type annotation checking
        return_type: Option<TypeExpr>,
        body: TypedBlock,
        ty: Type,
        span: Span,
    },
    /// A let-bound polymorphic closure (let-polymorphism).
    /// The body is kept untyped for runtime re-evaluation at each call site's concrete type.
    GenericClosure {
        /// Binding name from the enclosing `let`/`mut` declaration, used at runtime to look
        /// up the closure's `TypeScheme` from `type_ctx.scheme_env` for construction-at-call-time.
        name: Option<String>,
        captures: Vec<CaptureSpec>,
        /// See `Closure::capture_ids`.
        capture_ids: Vec<Option<LocalId>>,
        call_multiplicity: CallMultiplicity,
        call_mutation: CallMutation,
        params: Vec<Param>,
        /// See `Closure::param_ids`.
        param_ids: Vec<Option<LocalId>>,
        #[allow(dead_code)] // kept for future type annotation checking
        return_type: Option<TypeExpr>,
        body: Block,
        ty: Type,
        span: Span,
    },
    StructLiteral {
        path: Vec<String>,
        fields: Vec<(String, TypedExpr)>,
        ty: Type,
        /// Stable identity of the constructed struct/enum type (METEL-185 / ADR-0041),
        /// copied onto the runtime `Value` so method dispatch keys by `SymbolId`
        /// rather than surface name. `None` when no resolver context is available.
        type_id: Option<SymbolId>,
        /// Stable identity of the selected enum variant (ADR-0054 / #1062), when
        /// this literal constructs an enum variant rather than a plain struct.
        /// Resolved from the `MemberTable`, keyed by `(enum SymbolId, variant
        /// name)`. `None` for a plain struct literal, and for a variant literal
        /// with no identity context or a failed lookup — never a fabricated id.
        variant_id: Option<VariantId>,
        span: Span,
    },
    /// RFC-0078 §3.3: the inhabited-singleton coercion. `inner` is a value of an
    /// enum type with exactly one inhabited variant (`variant`, holding exactly
    /// one field, `field`); this node destructures it directly to that field's
    /// value with no explicit `match` at the use site. Sound unconditionally: the
    /// exhaustiveness check that licenses this coercion already guarantees no
    /// other variant could ever have been constructed, so no runtime tag check is
    /// needed — see `construct_match`'s uninhabited-variant exemption.
    SingletonCoerce {
        inner: Box<TypedExpr>,
        #[allow(dead_code)] // kept for future error messages
        variant: String,
        field: String,
        ty: Type,
        span: Span,
    },
    /// RFC-0008 §6: implicit coercion of a concrete value to an aspect object
    /// (`dyn Aspect`). `ty` is always `Type::Dyn { aspect, type_args }` — the
    /// erasure target — and carries everything the evaluator needs to rebuild it
    /// on the runtime `Value::DynAspect` (so erasure round-trips through
    /// generic-body reconstruction, #286). `aspect_id` is `aspect`'s own
    /// `SymbolId`, resolved once here rather than re-resolved by name at every
    /// dispatch (mirrors `StructLiteral::type_id`).
    DynCoerce {
        inner: Box<TypedExpr>,
        aspect_id: SymbolId,
        ty: Type,
        span: Span,
    },
    /// Issue #229: `return`/`break`/`continue` as expressions, always of type
    /// `!` (RFC-0078) — reachable anywhere an expression is valid, not just as
    /// a braced statement. `ty()` returns `&Type::Never` directly rather than
    /// storing a redundant `ty` field on every node, since it never varies.
    Return(TypedReturnExpr),
    Break(TypedBreakExpr),
    Continue(Span),
}

impl TypedExpr {
    /// Convenience method to get the type of this expression.
    #[must_use]
    pub fn ty(&self) -> &Type {
        match self {
            TypedExpr::Literal(_, ty, _)
            | TypedExpr::Ident(_, _, ty, _)
            | TypedExpr::Path(_, ty, _)
            | TypedExpr::Tuple(_, ty, _)
            | TypedExpr::Array(_, ty, _)
            | TypedExpr::RecordLiteral { ty, .. }
            | TypedExpr::RepeatArray(_, _, ty, _)
            | TypedExpr::BinOp(_, _, _, ty, _)
            | TypedExpr::UnaryOp(_, _, ty, _)
            | TypedExpr::RefTemp { ty, .. }
            | TypedExpr::Assign { ty, .. }
            | TypedExpr::Call { ty, .. }
            | TypedExpr::MethodCall { ty, .. }
            | TypedExpr::FieldAccess { ty, .. }
            | TypedExpr::TupleAccess { ty, .. }
            | TypedExpr::Index { ty, .. }
            | TypedExpr::Cast { ty, .. }
            | TypedExpr::If { ty, .. }
            | TypedExpr::Loop { ty, .. }
            | TypedExpr::Closure { ty, .. }
            | TypedExpr::GenericClosure { ty, .. }
            | TypedExpr::StructLiteral { ty, .. }
            | TypedExpr::SingletonCoerce { ty, .. }
            | TypedExpr::DynCoerce { ty, .. } => ty,
            TypedExpr::Match(m) => &m.expr_type,
            TypedExpr::Return(_) | TypedExpr::Break(_) | TypedExpr::Continue(_) => &Type::Never,
        }
    }

    /// Replace this node's stated type. Used only at a declared-type boundary
    /// (RFC-0166: a value flowing into a written function-type slot takes that
    /// slot's move-only type). `Return` / `Break` / `Continue` are always `!` and
    /// cannot name a binding, so they are returned unchanged.
    #[must_use]
    pub fn with_ty(mut self, new_ty: Type) -> Self {
        match &mut self {
            TypedExpr::Literal(_, ty, _)
            | TypedExpr::Ident(_, _, ty, _)
            | TypedExpr::Path(_, ty, _)
            | TypedExpr::Tuple(_, ty, _)
            | TypedExpr::Array(_, ty, _)
            | TypedExpr::RecordLiteral { ty, .. }
            | TypedExpr::RepeatArray(_, _, ty, _)
            | TypedExpr::BinOp(_, _, _, ty, _)
            | TypedExpr::UnaryOp(_, _, ty, _)
            | TypedExpr::RefTemp { ty, .. }
            | TypedExpr::Assign { ty, .. }
            | TypedExpr::Call { ty, .. }
            | TypedExpr::MethodCall { ty, .. }
            | TypedExpr::FieldAccess { ty, .. }
            | TypedExpr::TupleAccess { ty, .. }
            | TypedExpr::Index { ty, .. }
            | TypedExpr::Cast { ty, .. }
            | TypedExpr::If { ty, .. }
            | TypedExpr::Loop { ty, .. }
            | TypedExpr::Closure { ty, .. }
            | TypedExpr::GenericClosure { ty, .. }
            | TypedExpr::StructLiteral { ty, .. }
            | TypedExpr::SingletonCoerce { ty, .. }
            | TypedExpr::DynCoerce { ty, .. } => *ty = new_ty,
            TypedExpr::Match(m) => m.expr_type = new_ty,
            TypedExpr::Return(_) | TypedExpr::Break(_) | TypedExpr::Continue(_) => {}
        }
        self
    }

    /// Convenience method to get the span of this expression.
    #[must_use]
    pub fn span(&self) -> &Span {
        match self {
            TypedExpr::Literal(_, _, s)
            | TypedExpr::Ident(_, _, _, s)
            | TypedExpr::Path(_, _, s)
            | TypedExpr::Tuple(_, _, s)
            | TypedExpr::Array(_, _, s)
            | TypedExpr::RecordLiteral { span: s, .. }
            | TypedExpr::RepeatArray(_, _, _, s)
            | TypedExpr::BinOp(_, _, _, _, s)
            | TypedExpr::UnaryOp(_, _, _, s)
            | TypedExpr::RefTemp { span: s, .. }
            | TypedExpr::Assign { span: s, .. }
            | TypedExpr::Call { span: s, .. }
            | TypedExpr::MethodCall { span: s, .. }
            | TypedExpr::FieldAccess { span: s, .. }
            | TypedExpr::TupleAccess { span: s, .. }
            | TypedExpr::Index { span: s, .. }
            | TypedExpr::Cast { span: s, .. }
            | TypedExpr::If { span: s, .. }
            | TypedExpr::Loop { span: s, .. }
            | TypedExpr::Closure { span: s, .. }
            | TypedExpr::GenericClosure { span: s, .. }
            | TypedExpr::StructLiteral { span: s, .. }
            | TypedExpr::SingletonCoerce { span: s, .. }
            | TypedExpr::DynCoerce { span: s, .. }
            | TypedExpr::Continue(s) => s,
            TypedExpr::Match(m) => &m.span,
            TypedExpr::Return(r) => &r.span,
            TypedExpr::Break(b) => &b.span,
        }
    }
}

// ── Typed Match ───────────────────────────────────────────────────────────────

/// Mirrors `ast::Pattern`, but every nominal member site carries its interned
/// identity (ADR-0054 / #1062): a struct/enum-variant pattern records the
/// `FieldId` / `VariantId` the checker resolved, so no later phase re-derives a
/// member from its source spelling. `None` is the sanctioned diagnostic-recovery
/// state (no identity context, or a member the table never interned — e.g. a
/// block-local type); it is never a fabricated id. The spelling is retained
/// alongside the id for diagnostics and the pre-#1052 evaluator, which still
/// keys the runtime `Value`'s fields by name.
#[derive(Debug, Clone)]
pub enum TypedPattern {
    Wildcard(Span),
    Literal(Literal, Span),
    /// A binding pattern (`x` in `match v { x => … }`). The second field is the
    /// lexical identity of the binding it introduces (ADR-0054 /
    /// metel-core#1052); `None` without identity context.
    Binding(String, Option<LocalId>, Span),
    /// A genuine (two-segment) enum-variant pattern. `path` is
    /// `[.., Enum, Variant]`; one-segment bare variants are rewritten to this
    /// form (or to [`TypedPattern::Struct`]) before lowering, exactly as the
    /// untyped pass does.
    EnumVariant {
        path: Vec<String>,
        /// Identity of the matched variant, keyed by `(enum SymbolId, variant
        /// name)`.
        variant_id: Option<VariantId>,
        /// Bound field spellings, each with the id of the variant field it
        /// names (keyed by `(enum SymbolId, "Variant::field")`).
        fields: Vec<(String, Option<FieldId>)>,
        rest: bool,
        span: Span,
    },
    /// A named struct pattern (`Point { x, y }`, `Token { kind, .. }`).
    Struct {
        name: String,
        /// Identity of the matched struct declaration.
        type_id: Option<SymbolId>,
        /// Bound field spellings, each with the id of the struct field it names.
        fields: Vec<(String, Option<FieldId>)>,
        rest: bool,
        span: Span,
    },
    /// A bare, unnamed record pattern (`{ x, y }`) — structural, so its labels
    /// carry no nominal `FieldId` (row labels are `LabelId`, ADR-0054).
    Record {
        fields: Vec<String>,
        rest: bool,
        span: Span,
    },
    Tuple(Vec<TypedPattern>, Span),
    Array {
        elems: Vec<TypedPattern>,
        rest: Option<String>,
        span: Span,
    },
}

/// Mirrors `ast::MatchExpr` with typed expressions.
#[derive(Debug, Clone)]
pub struct TypedMatchExpr {
    pub scrutinee: Box<TypedExpr>,
    pub arms: Vec<TypedMatchArm>,
    pub expr_type: Type, // The type of the entire match expression
    pub span: Span,
}

/// Mirrors `ast::MatchArm` with typed expressions.
#[derive(Debug, Clone)]
pub struct TypedMatchArm {
    /// Resolved-identity pattern (ADR-0054 / #1062): member sites carry their
    /// interned `FieldId` / `VariantId`.
    pub pattern: TypedPattern,
    pub guard: Option<TypedExpr>,
    pub body: TypedBlock,
    #[allow(dead_code)] // kept for future error messages
    pub span: Span,
}

/// Is this typed expression an addressable *place* — something `&`/`&var` can take the
/// address of, and something `*p = v` can write through?
///
/// Purely syntactic on the typed AST, which is why the check belongs in the typechecker
/// (metel-core#280) rather than the evaluator, where it used to live as a runtime
/// `MetelError::internal`. Both still call this, so the two cannot drift.
///
/// `UnaryOp::Deref` is a place per RFC-0110 §6: `&*p` is a reborrow, not a copy.
#[must_use]
pub fn is_lvalue_path(expr: &TypedExpr) -> bool {
    match expr {
        TypedExpr::Ident(..) => true,
        TypedExpr::FieldAccess { object, .. }
        | TypedExpr::TupleAccess { object, .. }
        | TypedExpr::Index { object, .. }
        | TypedExpr::UnaryOp(crate::ast::UnaryOp::Deref, object, _, _) => is_lvalue_path(object),
        _ => false,
    }
}
