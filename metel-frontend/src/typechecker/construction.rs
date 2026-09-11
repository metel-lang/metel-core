use std::collections::HashMap;
use std::collections::HashSet;

use crate::ast::{
    AspectMethod, AssignTarget, BinOp, Block, Decl, Expr, ForInit, FunDecl, ImplBlock, Literal,
    MatchExpr, Param, Pattern, Program, Span, Stmt, TypeExpr, UnaryOp,
};
use crate::error::{MetelError, TypeErrorCode};
use crate::flow_state::FlowState;
use crate::identity::{BindingId, FieldId, FrozenIdentity, VariantId};
use crate::symbols::SymbolId;
use crate::typed_ast::{
    FunBody, MethodDispatch, TypedAspectDecl, TypedBlock, TypedBreakExpr, TypedDecl, TypedEnumDecl,
    TypedExpr, TypedForInStmt, TypedForInit, TypedForStmt, TypedFunDecl, TypedImplBlock,
    TypedLetDecl, TypedMatchArm, TypedMatchExpr, TypedMutDecl, TypedPattern, TypedPlace,
    TypedProgram, TypedReturnExpr, TypedStmt, TypedStructDecl, TypedWhileStmt,
};
use crate::typeinference::{
    self, unify, EnumInfo, GenericBound, InferType, RowConstraint, Substitution,
    TypeDefinitionRegistry, TypeScheme, TypeVar, TypeVarGenerator, VariantInfo,
};
use crate::types::Type;

use super::conversions::{
    infer_type_to_type, resolved_to_type, type_expr_to_infer_with_assoc_ctx,
    type_expr_to_infer_with_generics, type_to_infer, AssocResolveCtx,
};
use super::handoff::ResolvedInferenceFacts;
use super::SchemeEnv;

type ConcreteFields = Vec<(String, Type, Span)>;
type ConcreteStructEnv = HashMap<String, ConcreteFields>;
/// metel-core#736 / RFC-0138: a generic `FunDecl`'s own shape, keyed by name in
/// `ConstructCtx::fn_table`. See that field's doc comment.
type FnDeclShape = (Vec<Param>, Option<TypeExpr>, Block);

/// Build the concrete (fully-resolved `Type`) struct field map from inference results.
/// Generic structs are excluded — they are resolved per-use-site during construction.
pub(super) fn build_concrete_struct_env(
    registry: &TypeDefinitionRegistry,
    subst: &Substitution,
) -> Result<ConcreteStructEnv, MetelError> {
    registry
        .raw_struct_env()
        .iter()
        .filter(|(id, _)| !registry.raw_struct_type_params().contains_key(id))
        .filter_map(|(id, fields)| {
            // A struct with no recorded declared name cannot be keyed into the
            // name-indexed concrete env; skip it rather than invent a key.
            let name = registry.declared_type_name(*id)?;
            let concrete: Result<ConcreteFields, MetelError> = fields
                .iter()
                .map(|field| {
                    Ok((
                        field.name.clone(),
                        infer_type_to_type(&subst.apply(&field.ty), &field.span)?,
                        field.span.clone(),
                    ))
                })
                .collect();
            Some(concrete.map(|c| (name.to_string(), c)))
        })
        .collect()
}

/// Build the concrete method type map from inference results.
/// Methods that still have free `TypeVars` (generic struct params) are skipped here;
/// they are resolved at the call site via `method_scheme_env`.
pub(super) fn build_concrete_method_env(
    registry: &TypeDefinitionRegistry,
    subst: &Substitution,
) -> Result<HashMap<String, HashMap<String, Type>>, MetelError> {
    let dummy = Span::new(0, 0, "");
    registry
        .raw_method_env()
        .iter()
        .map(|(type_name, methods)| {
            let concrete: HashMap<_, _> = methods
                .iter()
                .filter_map(|(mname, mty)| {
                    let resolved = subst.apply(mty);
                    // Skip methods that still have unresolved TypeVars — they belong in scheme env.
                    if !typeinference::free_vars(&resolved).is_empty() {
                        return None;
                    }
                    infer_type_to_type(&resolved, &dummy)
                        .ok()
                        .map(|t| (mname.clone(), t))
                })
                .collect();
            Ok((type_name.clone(), concrete))
        })
        .collect()
}

/// Scope-aware context for Pass 2. Mirrors `InferContext`'s scope management but
/// holds concrete `Type` values; no constraint emission.
struct ConstructCtx<'a> {
    subst: &'a Substitution,
    scheme_env: &'a SchemeEnv,
    env: Vec<HashMap<String, Type>>,
    /// Binding mutability mirrors `env`; capture-list checking needs the declaration-site
    /// fact for `[&var name]`, even though ordinary construction only needs the type.
    mut_env: Vec<HashMap<String, bool>>,
    /// Stack of concrete struct field maps (name → fields with spans), innermost last.
    struct_scopes: Vec<ConcreteStructEnv>,
    /// Unified registry — source of truth for type definitions across all passes. See ADR-0025.
    registry: &'a TypeDefinitionRegistry,
    method_env: HashMap<String, HashMap<String, Type>>,
    /// Shared generator continued from Pass 1; keeps `TypeVar` identities globally unique.
    gen: TypeVarGenerator,
    /// Return type of the innermost enclosing function (None = unit / unknown).
    current_return_ty: Option<Type>,
    /// Break value type of the innermost enclosing `loop` (None = no loop or bare break).
    current_break_ty: Option<Type>,
    loop_depth: usize,
    /// Generic type param name → fresh `TypeVar`; populated during construction-at-call-time
    /// so type annotations like `T[]` in a generic body resolve to concrete types.
    generic_params: HashMap<String, TypeVar>,
    /// Symbol intern table from the name resolver; used to populate `TypedImplBlock::aspect_id`.
    /// `None` for single-module pipelines that don't go through `check_graph`.
    symbols: Option<&'a HashMap<(Vec<String>, String), SymbolId>>,
    /// Free-function overload table for the current module (METEL-180). Used to
    /// identify overloaded declarations and resolve overloaded call sites to
    /// the selected definition's `SymbolId`.
    overloads: &'a crate::typeinference::OverloadTable,
    /// Module path being constructed; used with `symbols` to assign `def_id` to
    /// top-level functions and to resolve constructed struct/enum types to their
    /// type `SymbolId` (METEL-185 / ADR-0041).
    current_module: &'a [String],
    /// Resolved bare-`Ident` reference table (METEL-187 / ADR-0041): reference-site
    /// span → referent `SymbolId`. Used to stamp `Call::callee_id` so direct calls to
    /// top-level functions dispatch by id. `None` for the single-program path.
    references: Option<&'a HashMap<Span, SymbolId>>,
    /// Concrete semantic decisions frozen at the inference/construction boundary.
    resolved_facts: &'a ResolvedInferenceFacts,
    /// Whole-graph member identity table (ADR-0054 / #1051). When present,
    /// construction stamps `TypedExpr::FieldAccess::field_id` and
    /// `TypedExpr::StructLiteral::variant_id` from it, keyed by
    /// `(owning type SymbolId, member name)`. `None` for the move-check and
    /// diagnostic-tool entry points that build no identity context — every
    /// member site then carries `None`, the sanctioned recovery state.
    identity: Option<FrozenIdentity<'a>>,
    /// Concrete target-type name `Self` denotes in the innermost enclosing impl-block
    /// method body (None outside one). #774 (revised): a body-internal `let x:
    /// Self.{ field }`/`Self::AssocType` annotation resolves through this the same
    /// way `construct_impl_method`'s own param/return-type resolution already does,
    /// instead of each call site needing `self_ty_name` threaded in by hand.
    current_self_type_name: Option<String>,
    /// metel-core#736 / RFC-0138: scope-stacked table of generic `FunDecl`s visible
    /// at the current construction point (top-level, hoisted in `construct_program`;
    /// nested, hoisted per-block in `construct_block`, mirroring the local-struct
    /// hoist just above it). Lets a bare `Expr::Ident` reference to a generic
    /// function (`let alias = identity;`) recover `identity`'s own `params`/
    /// `return_type`/`body` to build a `GenericClosure` node from, the same shape
    /// `construct_decl`'s closure-literal special case already builds one from.
    fn_table: Vec<HashMap<String, FnDeclShape>>,
    /// By-value capture names for each enclosing closure body. This is the
    /// temporary RFC-0050 boundary: nested borrowing of one is rejected until
    /// RFC-0122 can model the environment borrow's lifetime.
    closure_owned_captures: Vec<HashSet<String>>,
    /// RFC-0137 slice 2 (metel-core#858): flow-sensitive moved-field tracking for
    /// the function/method body currently being constructed. A partial move of a
    /// non-`Copy` struct/record field narrows the base binding's *type* to a
    /// `Type::Residual` of the same brand; reassigning the field widens it back.
    /// Reset per body in `construct_fun_decl` / `construct_impl_method`; see
    /// `construction/narrowing.rs`.
    flow: FlowState,
}

impl<'a> ConstructCtx<'a> {
    #[allow(clippy::too_many_arguments)]
    fn new(
        subst: &'a Substitution,
        scheme_env: &'a SchemeEnv,
        registry: &'a TypeDefinitionRegistry,
        gen: TypeVarGenerator,
        symbols: Option<&'a HashMap<(Vec<String>, String), SymbolId>>,
        overloads: &'a crate::typeinference::OverloadTable,
        current_module: &'a [String],
        references: Option<&'a HashMap<Span, SymbolId>>,
        resolved_facts: &'a ResolvedInferenceFacts,
        identity: Option<FrozenIdentity<'a>>,
    ) -> Result<Self, MetelError> {
        let concrete_struct_env = build_concrete_struct_env(registry, subst)?;
        let method_env = build_concrete_method_env(registry, subst)?;
        let mut ctx = Self {
            subst,
            scheme_env,
            env: vec![HashMap::new()],
            mut_env: vec![HashMap::new()],
            struct_scopes: vec![concrete_struct_env], // global scope pre-pushed
            registry,
            method_env,
            gen,
            current_return_ty: None,
            current_break_ty: None,
            loop_depth: 0,
            generic_params: HashMap::new(),
            symbols,
            overloads,
            current_module,
            references,
            resolved_facts,
            identity,
            current_self_type_name: None,
            fn_table: vec![HashMap::new()],
            closure_owned_captures: Vec::new(),
            flow: FlowState::default(),
        };
        // Derive concrete types for all monomorphic entries in scheme_env.
        // Both builtins and user functions are populated here — no second registration site.
        let dummy = Span::new(0, 0, "");
        for (name, scheme) in scheme_env {
            if scheme.quantified_vars.is_empty() {
                let resolved = subst.apply(&scheme.ty);
                if let Ok(ty) = infer_type_to_type(&resolved, &dummy) {
                    ctx.env.last_mut().unwrap().insert(name.clone(), ty);
                }
            }
        }
        Ok(ctx)
    }

    fn push_scope(&mut self) {
        self.env.push(HashMap::new());
        self.mut_env.push(HashMap::new());
        self.fn_table.push(HashMap::new());
    }
    fn pop_scope(&mut self) {
        self.env.pop();
        self.mut_env.pop();
        self.fn_table.pop();
    }

    fn push_struct_scope(&mut self) {
        self.struct_scopes.push(HashMap::new());
    }
    fn pop_struct_scope(&mut self) {
        self.struct_scopes.pop();
    }

    fn register_local_struct(&mut self, name: String, fields: Vec<(String, Type, Span)>) {
        self.struct_scopes.last_mut().unwrap().insert(name, fields);
    }

    fn get_type_param_record_kinds(&self, name: &str) -> Option<&Vec<bool>> {
        self.registry
            .type_param_record_kinds_for(self.current_module, name)
    }

    fn get_struct_fields(&self, name: &str) -> Option<&Vec<(String, Type, Span)>> {
        self.struct_scopes.iter().rev().find_map(|s| s.get(name))
    }

    fn has_struct_named(&self, name: &str) -> bool {
        self.get_struct_fields(name).is_some()
            || self
                .registry
                .resolve_type_id(self.current_module, name)
                .is_some_and(|id| self.registry.raw_struct_env().contains_key(&id))
    }

    fn bind(&mut self, name: impl Into<String>, ty: Type) {
        self.bind_with_mutability(name, ty, false);
    }

    fn bind_mut(&mut self, name: impl Into<String>, ty: Type) {
        self.bind_with_mutability(name, ty, true);
    }

    fn bind_with_mutability(&mut self, name: impl Into<String>, ty: Type, is_mutable: bool) {
        let name = name.into();
        // RFC-0137 slice 2: register the binding for move-triggered narrowing
        // before it lands in `env`, so a shadowing rebind resets its move state.
        self.flow_bind(&name, &ty);
        self.env.last_mut().unwrap().insert(name.clone(), ty);
        self.mut_env.last_mut().unwrap().insert(name, is_mutable);
    }

    fn lookup(&self, name: &str) -> Option<&Type> {
        self.env.iter().rev().find_map(|s| s.get(name))
    }

    fn is_mutable(&self, name: &str) -> bool {
        self.mut_env
            .iter()
            .rev()
            .find_map(|scope| scope.get(name))
            .copied()
            .unwrap_or(false)
    }

    fn enter_closure(&mut self, owned_captures: HashSet<String>) {
        self.closure_owned_captures.push(owned_captures);
    }

    fn exit_closure(&mut self) {
        self.closure_owned_captures.pop();
    }

    fn is_enclosing_owned_capture(&self, name: &str) -> bool {
        self.closure_owned_captures
            .iter()
            .rev()
            .any(|captures| captures.contains(name))
    }

    /// metel-core#736 / RFC-0138: register a generic `FunDecl`'s own shape (its
    /// `params`/`return_type`/`body`) in the innermost scope, so a later bare
    /// reference to it (`let alias = name;`) can build a `GenericClosure` from it.
    fn register_fn_decl(
        &mut self,
        name: impl Into<String>,
        params: Vec<Param>,
        return_type: Option<TypeExpr>,
        body: Block,
    ) {
        self.fn_table
            .last_mut()
            .unwrap()
            .insert(name.into(), (params, return_type, body));
    }

    fn lookup_fn_decl(&self, name: &str) -> Option<&FnDeclShape> {
        self.fn_table.iter().rev().find_map(|s| s.get(name))
    }

    /// Resolve the stable `SymbolId` of a direct-call callee, if it refers to a
    /// statically-resolved top-level declaration (METEL-187). A bare `Ident` is
    /// looked up in the resolver's reference table by span; a normalized
    /// `ResolvedPath` carries its id directly. Locals and dynamic callees return
    /// `None` (dispatched by value at runtime). The evaluator tolerates an id that
    /// has no symbol registration (e.g. a top-level `let`-bound value) by falling
    /// back to name lookup, so this may be stamped liberally.
    fn resolved_callee_id(&self, callee: &Expr) -> Option<SymbolId> {
        match callee {
            Expr::Ident(_, span) => self.references.and_then(|r| r.get(span).copied()),
            Expr::ResolvedPath { symbol_id, .. } => *symbol_id,
            _ => None,
        }
    }

    /// Resolve a struct/enum type name to its declaration `SymbolId` (METEL-185).
    /// Uses the registry's declaring-module index, falling back to the current
    /// module for locally-declared types. `None` without resolver context.
    fn type_symbol_id(&self, type_name: &str) -> Option<SymbolId> {
        let symbols = self.symbols?;
        if let Some(module) = self
            .registry
            .struct_declaring_module(self.current_module, type_name)
            .or_else(|| {
                self.registry
                    .enum_declaring_module(self.current_module, type_name)
            })
        {
            return symbols
                .get(&(module.clone(), type_name.to_string()))
                .copied();
        }
        // Builtin types (impl on i64/String/List/…) live in std::core, pre-seeded
        // with their SYM_TYPE_* ids; fall back there, then the current module.
        let std_core = vec!["std".to_string(), "core".to_string()];
        symbols
            .get(&(std_core, type_name.to_string()))
            .or_else(|| symbols.get(&(self.current_module.to_vec(), type_name.to_string())))
            .copied()
    }

    fn can_be_unqualified_variant(&self, name: &str) -> bool {
        self.registry.has_variant_named(name)
    }

    /// Interned identity of the field selected by `object.field` (ADR-0054 /
    /// #1062). `object_ty` is the access base's type; references are peeled and
    /// a nominal owner `SymbolId` resolved through the registry, then looked up
    /// in the whole-graph member table. `None` — no member table, a structural
    /// (record / residual) base with no nominal owner, a block-local struct
    /// (which the name resolver mints no `(module, name)` symbol for), or a
    /// field the table never interned — is the sanctioned recovery state, never
    /// a fabricated id.
    fn field_id_for(&self, object_ty: &Type, field: &str) -> Option<FieldId> {
        let members = self.identity?.members;
        let Type::Named(name, _) = peel_type_references(object_ty) else {
            return None;
        };
        let owner = self.registry.resolve_type_id(self.current_module, name)?;
        members.field(owner, field)
    }

    /// Interned identity of the enum variant an enum-variant `StructLiteral`
    /// constructs (ADR-0054 / #1062). `enum_id` is the literal's
    /// already-resolved enum `type_id`; `variant` is the last path segment.
    /// `None` for a plain struct literal (no `enum_id`), without a member table,
    /// or for a variant the table never interned — never a fabricated id.
    fn variant_id_for(&self, enum_id: Option<SymbolId>, variant: &str) -> Option<VariantId> {
        self.identity?.members.variant(enum_id?, variant)
    }

    /// Interned identity of a struct field named in a pattern (ADR-0054 /
    /// #1062b). `owner` is the struct declaration `SymbolId` resolved from the
    /// pattern's own nominal spelling. `None` without a member table or for an
    /// un-interned member (e.g. a block-local struct) — never fabricated.
    fn member_field_id(&self, owner: Option<SymbolId>, field: &str) -> Option<FieldId> {
        self.identity?.members.field(owner?, field)
    }

    /// Interned identity of an enum-variant field named in a pattern. Variant
    /// fields are interned on the enum owner under the variant-qualified key
    /// `"Variant::field"` so `V.x` and `W.x` stay distinct (see
    /// `identity::collect_members`).
    fn variant_field_id(
        &self,
        enum_id: Option<SymbolId>,
        variant: &str,
        field: &str,
    ) -> Option<FieldId> {
        self.identity?
            .members
            .field(enum_id?, &format!("{variant}::{field}"))
    }

    /// The resolved identity of the value reference at `span` (ADR-0054 /
    /// #1052), from the transient span → `BindingId` bridge. `None` without
    /// identity context, or when the span is not a recorded binding/reference
    /// site (e.g. a construction-synthesised node).
    fn binding_id_at(&self, span: &Span) -> Option<BindingId> {
        self.identity?.binding_spans.get(span)
    }

    /// The lexical identity of the binding *defined* at `span` (a `let` / `mut`
    /// name, a loop binding, a pattern binding). `None` for a module-level
    /// definition (a `SymbolId`, not a `LocalId`), a synthesised node, or
    /// without identity context.
    fn local_binding_at(&self, span: &Span) -> Option<crate::identity::LocalId> {
        self.binding_id_at(span)?.as_local()
    }

    /// Lexical identity of each parameter, parallel to `params` (ADR-0054 /
    /// #1052). Empty without identity context.
    fn param_local_ids(&self, params: &[Param]) -> Vec<Option<crate::identity::LocalId>> {
        if self.identity.is_none() {
            return Vec::new();
        }
        params
            .iter()
            .map(|p| self.local_binding_at(&p.span))
            .collect()
    }

    /// Lexical identity of the enclosing-scope binding each capture names,
    /// parallel to `captures`. The identity walk records a capture-list entry as
    /// a *use* of the outer binding, so it resolves like any reference.
    fn capture_local_ids(
        &self,
        captures: &[crate::ast::CaptureSpec],
    ) -> Vec<Option<crate::identity::LocalId>> {
        use crate::ast::CaptureSpec;
        if self.identity.is_none() {
            return Vec::new();
        }
        captures
            .iter()
            .map(|c| {
                let span = match c {
                    CaptureSpec::Owned { span, .. }
                    | CaptureSpec::SharedRef { span, .. }
                    | CaptureSpec::MutRef { span, .. }
                    | CaptureSpec::Clone { span, .. } => span,
                };
                self.local_binding_at(span)
            })
            .collect()
    }

    fn push_return_type(&mut self, ty: Option<Type>) -> Option<Type> {
        std::mem::replace(&mut self.current_return_ty, ty)
    }
    fn pop_return_type(&mut self, prev: Option<Type>) {
        self.current_return_ty = prev;
    }

    fn push_self_type_name(&mut self, name: Option<String>) -> Option<String> {
        std::mem::replace(&mut self.current_self_type_name, name)
    }
    fn pop_self_type_name(&mut self, prev: Option<String>) {
        self.current_self_type_name = prev;
    }
    fn push_break_type(&mut self, ty: Option<Type>) -> Option<Type> {
        std::mem::replace(&mut self.current_break_ty, ty)
    }
    fn pop_break_type(&mut self, prev: Option<Type>) {
        self.current_break_ty = prev;
    }

    fn enter_loop(&mut self) {
        self.loop_depth += 1;
    }
    fn exit_loop(&mut self) {
        debug_assert!(self.loop_depth > 0, "loop depth underflow");
        self.loop_depth -= 1;
    }
    fn push_loop_depth_reset(&mut self) -> usize {
        std::mem::replace(&mut self.loop_depth, 0)
    }
    fn pop_loop_depth(&mut self, prev: usize) {
        self.loop_depth = prev;
    }
    fn is_in_loop(&self) -> bool {
        self.loop_depth > 0
    }

    /// Convert a type expression to an `InferType`, substituting generic param names
    /// to their `TypeVars` when `self.generic_params` is populated (construction-at-call-time).
    /// `Self` resolves through `current_self_type_name` when set (#774, revised) --
    /// e.g. a body-internal `let x: Self.{ field }` inside an impl-block method.
    fn type_expr_to_infer_ctx(&self, te: &TypeExpr) -> InferType {
        let assoc_ctx = AssocResolveCtx {
            registry: self.registry,
            current_module: self.current_module,
            current_aspect: None,
        };
        type_expr_to_infer_with_assoc_ctx(
            te,
            &self.generic_params,
            self.current_self_type_name.as_deref(),
            &assoc_ctx,
        )
    }
}

fn unqualified_variant_needs_annotation_error(name: &str, span: &Span) -> MetelError {
    MetelError::type_error(
        TypeErrorCode::T0002,
        format!("cannot infer type of `{name}`; add a type annotation"),
        span,
    )
}

fn resolve_expected_enum<'a>(
    expected_ty: Option<&'a Type>,
    span: &Span,
    ctx: &'a ConstructCtx<'_>,
) -> Result<(&'a String, &'a EnumInfo), MetelError> {
    let expected_ty = expected_ty.ok_or_else(|| {
        MetelError::type_error(
            TypeErrorCode::T0002,
            "cannot infer type; add a type annotation",
            span,
        )
    })?;
    match expected_ty {
        Type::Named(enum_name, _) => {
            let enum_info = ctx
                .registry
                .enum_info(ctx.current_module, enum_name)
                .ok_or_else(|| {
                    MetelError::type_error(
                        TypeErrorCode::T0001,
                        format!("expected enum type, found `{expected_ty}`"),
                        span,
                    )
                })?;
            Ok((enum_name, enum_info))
        }
        _ => Err(MetelError::type_error(
            TypeErrorCode::T0001,
            format!("expected enum type, found `{expected_ty}`"),
            span,
        )),
    }
}

fn resolve_unqualified_variant_expr(
    variant_name: &str,
    expected_ty: Option<&Type>,
    span: &Span,
    ctx: &ConstructCtx<'_>,
) -> Result<TypedExpr, MetelError> {
    let expected_ty = expected_ty
        .cloned()
        .ok_or_else(|| unqualified_variant_needs_annotation_error(variant_name, span))?;
    let (enum_name, enum_info) = resolve_expected_enum(Some(&expected_ty), span, ctx)?;
    let enum_name = enum_name.clone();
    let variant = enum_info
        .variants
        .iter()
        .find(|variant| variant.name == variant_name)
        .ok_or_else(|| {
            MetelError::type_error(
                TypeErrorCode::T0001,
                format!("cannot unify `{variant_name}` with `{expected_ty}`"),
                span,
            )
        })?;
    if !variant.fields.is_empty() {
        return Err(MetelError::type_error(
            TypeErrorCode::T0003,
            format!("missing fields for `{enum_name}::{variant_name}`"),
            span,
        ));
    }
    let type_id = ctx.type_symbol_id(&enum_name);
    Ok(TypedExpr::StructLiteral {
        path: vec![enum_name.clone(), variant_name.to_string()],
        fields: vec![],
        ty: expected_ty,
        type_id,
        variant_id: ctx.variant_id_for(type_id, variant_name),
        span: span.clone(),
    })
}

/// Construct a `TypedBlock` for a generic (polymorphic) function body at call time.
///
/// RFC-0053 §4 (metel-core#757): `[T; N]` coerces to `T[]`, never the reverse
/// -- a `T[]` value has no statically-known length, so accepting it where a
/// specific `[T; N]` is expected defeats the type's entire point.
///
/// `construct_expr`'s `expected_ty`/`hint` parameter is advisory, not
/// enforced, for an argument that already has a fully-determined type of its
/// own (a bare identifier, unlike an array literal, which `Expr::Array`'s own
/// branch does shape against the hint) -- nothing else here rejects a `T[]`
/// argument passed where the hint specifically requires a `[T; N]`.
///
/// This is deliberately its own narrow, direction-aware check rather than a
/// change to `unify()`'s general Array/SizedArray matching: `unify()` is
/// shared by many symmetric/structural unification call sites throughout the
/// typechecker that have nothing to do with actual-vs-expected coercion
/// checking, and making it asymmetric there breaks real, legitimate uses of
/// the *valid* `[T; N]` -> `T[]` direction (confirmed directly -- an earlier
/// attempt that changed `unify()` itself passed the two repros in the linked
/// issue but failed 5 existing fixtures elsewhere in the corpus, plus a
/// generic-method case and a match-pattern-exhaustiveness case found by hand
/// that weren't in the corpus at all). Call this explicitly at every place an
/// argument's constructed type needs checking against its expected/declared
/// type instead.
fn reject_dynamic_array_where_sized_expected(
    expected: Option<&Type>,
    actual: &TypedExpr,
) -> Result<(), MetelError> {
    if let (Some(Type::SizedArray(_, n)), Type::Array(_)) =
        (expected, peel_type_references(actual.ty()))
    {
        return Err(MetelError::type_error(
            TypeErrorCode::T0001,
            format!("expected a fixed-size array of {n} element(s), got a dynamically-sized array"),
            actual.span(),
        ));
    }
    Ok(())
}

/// Instantiates `scheme` with fresh type vars, unifies each instantiated parameter
/// type with the corresponding runtime argument type (via `arg_types`), then runs the
/// construction pass on `body` with the resulting substitution.
/// Construct method-call arguments, hinting each with the corresponding non-self
/// parameter type from a concrete method function type so integer/float literals
/// adopt the expected element type (e.g. `List<i32>.push(5)` → `I32`).
fn construct_method_args(
    method_fun_ty: &Type,
    args: &[crate::ast::Expr],
    ctx: &mut ConstructCtx,
) -> Result<Vec<TypedExpr>, crate::error::MetelError> {
    if let Type::Fun(params, ..) = method_fun_ty {
        // params[0] is self/receiver; the rest correspond to args.
        let arg_params: Vec<Option<&Type>> = params
            .iter()
            .skip(1)
            .map(Some)
            .chain(std::iter::repeat(None))
            .take(args.len())
            .collect();
        args.iter()
            .zip(arg_params.iter())
            .map(|(a, hint)| {
                let typed = construct_expr(a, *hint, ctx)?;
                reject_dynamic_array_where_sized_expected(*hint, &typed)?;
                // RFC-0008 §6: same gap, same fix, as `try_generic_method_scheme`
                // below — a concrete (non-generic) method whose param is itself
                // `dyn Aspect` (e.g. `fun bar(&self, x: dyn Display)`).
                match hint {
                    Some(h) => maybe_dyn_coerce(h, typed, a.span(), ctx),
                    None => Ok(typed),
                }
            })
            .collect()
    } else {
        args.iter().map(|a| construct_expr(a, None, ctx)).collect()
    }
}

pub(super) fn symbolic_aspect_method_type(
    registry: &TypeDefinitionRegistry,
    aspect: &str,
    method: &crate::ast::AspectMethod,
    placeholder: &str,
) -> Option<InferType> {
    let mut gen = TypeVarGenerator::with_counter(3_000_000);
    let scheme = symbolic_aspect_method_scheme(registry, aspect, method, placeholder, &mut gen)?;
    let mut subst = Substitution::new();
    for (var, generic) in scheme.quantified_vars.iter().zip(&method.generics) {
        subst.bind(
            *var,
            InferType::Named(
                format!("__metel_move_check_method_generic_{}", generic.name),
                Vec::new(),
            ),
        );
    }
    Some(subst.apply(&scheme.ty))
}

pub(super) fn symbolic_aspect_method_scheme(
    registry: &TypeDefinitionRegistry,
    aspect: &str,
    method: &crate::ast::AspectMethod,
    placeholder: &str,
    gen: &mut TypeVarGenerator,
) -> Option<TypeScheme> {
    let assoc_ctx = super::conversions::AssocResolveCtx {
        registry,
        current_module: &[],
        current_aspect: Some(aspect),
    };
    let generic_map: HashMap<String, TypeVar> = method
        .generics
        .iter()
        .map(|generic| (generic.name.clone(), gen.fresh()))
        .collect();
    let params = method
        .params
        .iter()
        .map(|param| {
            if param.receiver.is_some() || param.name == "self" {
                Some(InferType::Named(placeholder.to_string(), Vec::new()))
            } else {
                param.type_ann.as_ref().map(|ann| {
                    super::conversions::type_expr_to_infer_with_assoc_ctx(
                        ann,
                        &generic_map,
                        Some(placeholder),
                        &assoc_ctx,
                    )
                })
            }
        })
        .collect::<Option<Vec<_>>>()?;
    let ret = method
        .return_type
        .as_ref()
        .map_or_else(InferType::unit, |ret| {
            super::conversions::type_expr_to_infer_with_assoc_ctx(
                ret,
                &generic_map,
                Some(placeholder),
                &assoc_ctx,
            )
        });
    let quantified_vars = method
        .generics
        .iter()
        .filter_map(|generic| generic_map.get(&generic.name).copied())
        .collect();
    Some(TypeScheme {
        quantified_vars,
        param_names: method
            .generics
            .iter()
            .map(|generic| generic.name.clone())
            .collect(),
        bounds: super::registry::collect_type_param_bounds(&method.generics, None),
        neg_bounds: super::registry::collect_negative_type_param_bounds(&method.generics, None),
        record_kinds: super::registry::collect_type_param_record_kinds(&method.generics, None),
        assoc_projections: vec![],
        assoc_eq_constraints: vec![],
        opaque_returns: vec![],
        ty: InferType::fun(params, ret),
    })
}

pub(super) fn symbolic_impl_method_scheme(
    registry: &TypeDefinitionRegistry,
    impl_generics: &[crate::ast::GenericParam],
    method_generics: &[crate::ast::GenericParam],
    target_type: &TypeExpr,
    aspect_name: Option<&str>,
    params: &[crate::ast::Param],
    return_type: Option<&TypeExpr>,
) -> Option<TypeScheme> {
    let mut gen = TypeVarGenerator::with_counter(5_000_000);
    let generics: Vec<_> = impl_generics
        .iter()
        .chain(method_generics)
        .cloned()
        .collect();
    let generic_map: HashMap<String, TypeVar> = generics
        .iter()
        .map(|generic| (generic.name.clone(), gen.fresh()))
        .collect();
    let assoc_ctx = super::conversions::AssocResolveCtx {
        registry,
        current_module: &[],
        current_aspect: aspect_name,
    };
    let self_ty = super::conversions::type_expr_to_infer_with_assoc_ctx(
        target_type,
        &generic_map,
        None,
        &assoc_ctx,
    );
    let param_types = params
        .iter()
        .map(|param| {
            if param.receiver.is_some() || param.name == "self" {
                Some(self_ty.clone())
            } else {
                param.type_ann.as_ref().map(|annotation| {
                    super::conversions::type_expr_to_infer_with_assoc_ctx(
                        annotation,
                        &generic_map,
                        None,
                        &assoc_ctx,
                    )
                })
            }
        })
        .collect::<Option<Vec<_>>>()?;
    let ret = return_type.map_or_else(InferType::unit, |annotation| {
        super::conversions::type_expr_to_infer_with_assoc_ctx(
            annotation,
            &generic_map,
            None,
            &assoc_ctx,
        )
    });
    let quantified_vars = generics
        .iter()
        .filter_map(|generic| generic_map.get(&generic.name).copied())
        .collect();
    Some(TypeScheme {
        quantified_vars,
        param_names: generics
            .iter()
            .map(|generic| generic.name.clone())
            .collect(),
        bounds: super::registry::collect_type_param_bounds(&generics, None),
        neg_bounds: super::registry::collect_negative_type_param_bounds(&generics, None),
        record_kinds: super::registry::collect_type_param_record_kinds(&generics, None),
        assoc_projections: vec![],
        assoc_eq_constraints: vec![],
        opaque_returns: vec![],
        ty: InferType::fun(param_types, ret),
    })
}

pub(super) fn construct_generic_body(
    scheme: &TypeScheme,
    params: &[crate::ast::Param],
    arg_types: &[crate::types::Type],
    body: &crate::ast::Block,
    span: &crate::ast::Span,
    type_ctx: &crate::typeinference::TypeCtx,
    expected_ret: Option<&crate::types::Type>,
) -> Result<crate::typed_ast::TypedBlock, crate::error::MetelError> {
    use super::conversions::{infer_type_to_type, type_to_infer};
    use crate::typeinference::{instantiate_with_renaming, TypeVarGenerator};

    // Use a high starting counter to avoid collisions with registry TypeVars (allocated
    // starting from 0 during build_registry). The substitution built here would otherwise
    // incorrectly resolve registry TypeVars when ConstructCtx::new applies it.
    let mut gen = TypeVarGenerator::with_counter(1_000_000);

    let (instance, renaming) = instantiate_with_renaming(scheme, &mut gen);
    let InferType::Fun(param_infertypes, ret_infertype, ..) = instance else {
        return Err(crate::error::MetelError::internal(
            "construct_generic_body: scheme is not a function type",
        ));
    };

    // Unify instantiated param types with concrete arg types from runtime values.
    // Unification failures are skipped (not errors) — the typechecker already validated
    // the program; here we only need a "good enough" substitution for construction.
    // This handles cases where generic type parameters can't be recovered from runtime
    // values (e.g. `Named("MyResult", [])` vs `Named("MyResult", [T, E])`).
    let mut subst = Substitution::new();
    for (param_it, arg_ty) in param_infertypes.iter().zip(arg_types.iter()) {
        let arg_it = type_to_infer(arg_ty);
        if let Ok(s) = typeinference::unify(&subst.apply(param_it), &arg_it) {
            subst = subst.compose(&s);
        }
    }

    // metel-core#716: a type parameter that appears only in the return position (no
    // argument mentions it — `fun make<V>() -> V[]`, `List::new<T>() -> List<T>`) gets
    // nothing from the loop above. Before falling back to Never (which follows), also try
    // the caller's own expected return type — already correctly resolved at the call site
    // (the same computation `instantiate_scheme_with_expected_ret` does for the outer
    // call's own signature; this is that information's only path into the body's own
    // construction, which arg_types alone can never carry for a no-argument call).
    // Unification failures here are skipped for the same "good enough substitution"
    // reason as the argument loop above.
    if let Some(expected) = expected_ret {
        if let Ok(s) = typeinference::unify(&subst.apply(&ret_infertype), &type_to_infer(expected))
        {
            subst = subst.compose(&s);
        }
    }

    // Fill any still-unresolved type vars with Never (not Unit) so
    // `infer_type_to_type` does not error during construction. `unify` treats
    // `Never` as the bottom type and no-ops instead of binding (see `unify`'s
    // `(Never, _) | (_, Never) => Ok(Substitution::new())` arm), which is
    // exactly why a var can still be unresolved here even after the loop above
    // -- e.g. `value_to_type`'s own placeholder for an empty collection's
    // element type (#271) unifies as a no-op, leaving the element TypeVar
    // unbound. Defaulting to `Unit` here (as opposed to `Never`) would make
    // that placeholder look like a real concrete type to everything
    // downstream, which previously produced spurious construction errors for
    // any dead branch that called a non-Unit method on it; `Never` coerces to
    // any type through the rest of construction (binops, method-call
    // receivers) and defers to the evaluator's runtime dynamic dispatch
    // instead, matching this function's own "evaluation correctness is
    // unaffected -- runtime dispatch goes by value kind" contract.
    let all_free: std::collections::HashSet<_> = param_infertypes
        .iter()
        .chain(std::iter::once(&*ret_infertype))
        .flat_map(typeinference::free_vars)
        .collect();
    for v in all_free {
        if subst.lookup(v).is_none() {
            subst.bind(v, InferType::Never);
        }
    }

    let ret_ty = infer_type_to_type(&subst.apply(&ret_infertype), span).ok();

    // Generic bodies are constructed at call time; overloaded functions are never
    // generic, so there is no overload table to consult here.
    let empty_overloads = crate::typeinference::OverloadTable::new();
    // Generic bodies are reconstructed at runtime; their inner direct calls are
    // re-resolved here without a reference table (callee_id stamping is skipped),
    // and without pass 1's write-through analysis (empty set — same limitation).
    let resolved_facts = ResolvedInferenceFacts::empty();
    // `body` is the exact same `ast::Block` the ahead-of-time identity walk
    // already processed (every function body is walked regardless of whether
    // it turns out generic), so its `binding_spans` entries for spans inside
    // `body` already exist and apply unchanged across every monomorphizing
    // call — a binding's `LocalId`/`FieldId` is a property of its lexical
    // position, not of the concrete type args this call inferred
    // (ADR-0054 / metel-core#1052). `None` only on the move-checker's own
    // reconstruction, which built `type_ctx` without these tables.
    let identity = type_ctx
        .members
        .as_deref()
        .zip(type_ctx.binding_spans.as_deref())
        .map(|(members, binding_spans)| FrozenIdentity {
            members,
            binding_spans,
        });
    let mut ctx = ConstructCtx::new(
        &subst,
        &type_ctx.scheme_env,
        &type_ctx.registry,
        gen,
        None,
        &empty_overloads,
        &[],
        None,
        &resolved_facts,
        identity,
    )?;

    // Build name → fresh TypeVar mapping so type annotations like `T[]` in the body
    // resolve to concrete types. scheme.param_names[i] corresponds to quantified_vars[i],
    // and renaming maps original TypeVar → fresh TypeVar.
    if !scheme.param_names.is_empty() {
        let mut gp: HashMap<String, TypeVar> = HashMap::new();
        for (orig_var, name) in scheme.quantified_vars.iter().zip(scheme.param_names.iter()) {
            if let Some(&fresh_var) = renaming.get(orig_var) {
                gp.insert(name.clone(), fresh_var);
            }
        }
        ctx.generic_params = gp;
    }

    ctx.push_scope();
    let saved_flow = ctx.flow_enter_body();
    for (param, param_it) in params.iter().zip(param_infertypes.iter()) {
        let concrete_ty =
            infer_type_to_type(&subst.apply(param_it), span).unwrap_or(crate::types::Type::Unit);
        ctx.bind(&param.name, concrete_ty);
    }
    let saved_return = ctx.push_return_type(ret_ty.clone());
    let typed_block = construct_block(body, ret_ty.as_ref(), &mut ctx)?;
    ctx.pop_return_type(saved_return);
    ctx.flow_exit_body(saved_flow);
    ctx.pop_scope();

    Ok(typed_block)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn construct_program(
    program: &Program,
    subst: &Substitution,
    scheme_env: &SchemeEnv,
    registry: &TypeDefinitionRegistry,
    gen: TypeVarGenerator,
    symbols: Option<&HashMap<(Vec<String>, String), SymbolId>>,
    overloads: &crate::typeinference::OverloadTable,
    current_module: &[String],
    references: Option<&HashMap<Span, SymbolId>>,
    resolved_facts: &ResolvedInferenceFacts,
    identity: Option<FrozenIdentity<'_>>,
) -> Result<TypedProgram, MetelError> {
    let mut ctx = ConstructCtx::new(
        subst,
        scheme_env,
        registry,
        gen,
        symbols,
        overloads,
        current_module,
        references,
        resolved_facts,
        identity,
    )?;

    // metel-core#736 / RFC-0138: hoist every top-level `FunDecl`'s own shape into
    // `ctx.fn_table` before constructing any declaration, so a bare reference to a
    // generic function (`let alias = identity;`) can find it regardless of
    // declaration order -- mirroring the local-struct hoist in `construct_block`.
    for decl in &program.decls {
        if let Decl::Fun(fd) = decl {
            ctx.register_fn_decl(
                fd.name.clone(),
                fd.params.clone(),
                fd.return_type.clone(),
                fd.body.clone(),
            );
        }
    }

    let mut out = vec![];
    for decl in &program.decls {
        let mut typed = construct_decl(decl, &mut ctx)?;
        // Assign each non-overloaded top-level function its stable identity so the
        // evaluator can register and dispatch it by `SymbolId` (METEL-187). Only
        // genuine top-level declarations are post-processed here; methods and
        // nested/local functions keep `def_id: None`.
        if let TypedDecl::Fun(f) = &mut typed {
            if f.symbol_id.is_none() {
                if let Some(syms) = symbols {
                    f.def_id = syms
                        .get(&(current_module.to_vec(), f.name.clone()))
                        .copied();
                }
            }
        }
        // Same identity assignment for top-level `let`/`mut` (ADR-0042): only
        // module-level bindings reach this loop, so this never touches a block-local
        // or `for`-init binding (those keep `def_id: None` from construction).
        if let TypedDecl::Let(ld) = &mut typed {
            if let Some(syms) = symbols {
                ld.def_id = syms
                    .get(&(current_module.to_vec(), ld.name.clone()))
                    .copied();
            }
        }
        if let TypedDecl::Mut(md) = &mut typed {
            if let Some(syms) = symbols {
                md.def_id = syms
                    .get(&(current_module.to_vec(), md.name.clone()))
                    .copied();
            }
        }
        out.push(typed);
    }
    Ok(out)
}

mod narrowing;

mod declarations;
use declarations::construct_decl;

fn construct_block(
    block: &Block,
    expected_tail_ty: Option<&Type>,
    ctx: &mut ConstructCtx,
) -> Result<TypedBlock, MetelError> {
    ctx.push_scope();
    ctx.push_struct_scope();
    ctx.flow.push_scope();
    // Hoist struct/enum declarations defined in this block so they are available
    // for any expression in the block regardless of declaration order.
    for decl in &block.stmts {
        if let Decl::Struct(sd) = decl {
            let fields = sd
                .fields
                .iter()
                .map(|f| {
                    let ty = resolved_to_type(
                        &ctx.type_expr_to_infer_ctx(&f.type_ann),
                        ctx.subst,
                        &f.span,
                    )?;
                    Ok((f.name.clone(), ty, f.span.clone()))
                })
                .collect::<Result<_, MetelError>>()?;
            ctx.register_local_struct(sd.name.clone(), fields);
        }
    }
    // metel-core#736 / RFC-0138: hoist this block's own nested `FunDecl`s the same
    // way, so a bare reference to a nested generic function works regardless of
    // whether the reference textually precedes or follows the declaration --
    // matching how `hoist_fun_decls` already makes nested mutual recursion work
    // on the inference side.
    for decl in &block.stmts {
        if let Decl::Fun(fd) = decl {
            ctx.register_fn_decl(
                fd.name.clone(),
                fd.params.clone(),
                fd.return_type.clone(),
                fd.body.clone(),
            );
        }
    }
    let mut stmts = vec![];
    for stmt in &block.stmts {
        stmts.push(construct_decl(stmt, ctx)?);
    }
    let tail = match &block.tail {
        Some(e) => {
            let constructed = construct_expr(e, expected_tail_ty, ctx)?;
            let constructed = match expected_tail_ty {
                Some(t) => {
                    let constructed = maybe_read_copy(
                        t,
                        constructed,
                        e.span(),
                        ctx.registry,
                        ctx.current_module,
                    )?;
                    let constructed =
                        maybe_singleton_coerce(t, constructed, e.span(), ctx.registry)?;
                    maybe_dyn_coerce(t, constructed, e.span(), ctx)?
                }
                None => constructed,
            };
            Some(Box::new(constructed))
        }
        None => None,
    };
    ctx.pop_struct_scope();
    ctx.pop_scope();
    // Bindings introduced in this block leave move tracking; a partial move of an
    // *outer* binding made inside the block survives the pop (it is not in this
    // scope's shadow list), which is what an `if` / `match` join then reads.
    ctx.flow.pop_scope();
    Ok(TypedBlock {
        stmts,
        tail,
        span: block.span.clone(),
    })
}

mod expressions;
use expressions::{construct_expr, construct_stmt};

mod patterns;
use patterns::{
    block_result_type, builtin_pattern_method_expr, construct_enum_literal_ty, construct_match,
    enum_variant_type_param_remap, find_loop_break_type, fun_body_diverges, is_variant_uninhabited,
    merge_branch_types,
};
pub(super) use patterns::{resolve_bare_variant, resolve_struct_pattern};

mod calls;
use calls::{
    check_fun_call_assoc_eq, check_fun_call_bounds, check_fun_call_neg_bounds,
    check_scheme_assoc_eq, check_scheme_bounds, check_scheme_neg_bounds,
    check_type_does_not_satisfy_bound, check_type_satisfies_bounds, construct_call,
    dispatch_for_resolved_method, instantiate_scheme_for_call, resolve_aspect_id,
    resolve_generic_method_call,
};

fn construct_literal_type(
    lit: &Literal,
    expected_ty: Option<&Type>,
    span: &Span,
) -> Result<Type, MetelError> {
    use crate::ast::{FloatKind, IntKind};
    match lit {
        Literal::Int(n) => {
            match expected_ty {
                Some(Type::I8) => Ok(Type::I8),
                Some(Type::I16) => Ok(Type::I16),
                Some(Type::I32) => Ok(Type::I32),
                Some(Type::U8) => Ok(Type::U8),
                Some(Type::U16) => Ok(Type::U16),
                Some(Type::U32) => Ok(Type::U32),
                Some(Type::U64) => {
                    if *n < 0 {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0005,
                            format!("integer literal `{n}` is negative and cannot be used as a u64 index"),
                            span,
                        ));
                    }
                    Ok(Type::U64)
                }
                Some(Type::F32) => Ok(Type::F32),
                Some(Type::F64) => Ok(Type::F64),
                _ => Ok(Type::I64),
            }
        }
        Literal::Float(_) => match expected_ty {
            Some(Type::F32) => Ok(Type::F32),
            _ => Ok(Type::F64),
        },
        Literal::SizedInt { kind, .. } => Ok(match kind {
            IntKind::I8 => Type::I8,
            IntKind::I16 => Type::I16,
            IntKind::I32 => Type::I32,
            IntKind::I64 => Type::I64,
            IntKind::U8 => Type::U8,
            IntKind::U16 => Type::U16,
            IntKind::U32 => Type::U32,
            IntKind::U64 => Type::U64,
        }),
        Literal::SizedFloat { kind, .. } => Ok(match kind {
            FloatKind::F32 => Type::F32,
            FloatKind::F64 => Type::F64,
        }),
        Literal::Char(_) => Ok(Type::Char),
        Literal::Boolean(_) => Ok(Type::Boolean),
        Literal::Str(_) => Ok(Type::Str),
        Literal::Unit => Ok(Type::Unit),
    }
}

fn construct_binop(
    lhs: &Expr,
    op: &BinOp,
    rhs: &Expr,
    span: &Span,
    ctx: &mut ConstructCtx,
) -> Result<TypedExpr, MetelError> {
    let lhs_built = construct_expr(lhs, None, ctx)?;
    let rhs_built = construct_expr(rhs, None, ctx)?;
    // If one operand is a polymorphic literal that defaulted to i64/f64, and the other
    // has a more specific numeric type, re-build the literal with the concrete type.
    let lt = lhs_built.ty().clone();
    let rt = rhs_built.ty().clone();
    let (lhs, rhs) = if (lt == Type::I64 || lt == Type::F64) && rt.is_numeric() && rt != lt {
        (construct_expr(lhs, Some(&rt), ctx)?, rhs_built)
    } else if (rt == Type::I64 || rt == Type::F64) && lt.is_numeric() && lt != rt {
        (lhs_built, construct_expr(rhs, Some(&lt), ctx)?)
    } else {
        (lhs_built, rhs_built)
    };
    let ty = match op {
        BinOp::Add => {
            let t = lhs.ty();
            if !matches!(t, Type::Str | Type::Never) && !t.is_numeric() {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0005,
                    format!("`+` requires a numeric type or String operands, got `{t}`"),
                    span,
                ));
            }
            t.clone()
        }
        BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
            let t = lhs.ty();
            if !matches!(t, Type::Never) && !t.is_numeric() {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0005,
                    format!("arithmetic operator requires a numeric type operand, got `{t}`"),
                    span,
                ));
            }
            t.clone()
        }
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            let t = lhs.ty();
            if !matches!(t, Type::Str | Type::Char | Type::Never) && !t.is_numeric() {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0005,
                    format!(
                        "ordering comparison requires a numeric type or String operands, got `{t}`"
                    ),
                    span,
                ));
            }
            Type::Boolean
        }
        BinOp::Eq | BinOp::Ne => {
            // metel-core#279: this arm previously returned `Type::Boolean` with no
            // operand check at all, sitting right beside the ordering arm above that
            // does check. Pass 1 only constrains the two operands to unify *with each
            // other*, so mixed types were caught by unification while same-type-on-both
            // -sides reached an evaluator that only has `==` arms for the primitive
            // scalars — producing an I0001 internal error at run time for references,
            // structs, enums (including `Perhaps`), arrays, tuples and unit.
            //
            // Deliberately *rejects* rather than peeling references: peeling would
            // silently commit the language to referent-equality semantics, and whether
            // two references should compare referents (Rust) or identity (Go) is an open
            // design question (metel-core#263). Rejecting is direction-neutral, and
            // status-quo-preserving since these already failed, just badly.
            //
            // The real fix is routing `==` through the `Eq` aspect (metel-core#263 /
            // RFC-0062); this guard relaxes as that lands.
            let t = lhs.ty();
            if !matches!(t, Type::Str | Type::Char | Type::Boolean | Type::Never) && !t.is_numeric()
            {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0005,
                    format!(
                        "equality comparison requires a primitive operand (numeric, \
                         boolean, String, or char), got `{t}`; `==` does not yet dispatch \
                         through the `Eq` aspect — use `.eq(..)` on a type that implements it"
                    ),
                    span,
                ));
            }
            Type::Boolean
        }
        BinOp::And | BinOp::Or => Type::Boolean,
        BinOp::Range | BinOp::RangeInclusive => Type::Named("Range".to_string(), vec![Type::I64]),
    };
    Ok(TypedExpr::BinOp(
        Box::new(lhs),
        op.clone(),
        Box::new(rhs),
        ty,
        span.clone(),
    ))
}

fn type_to_type_expr(ty: &Type) -> TypeExpr {
    let named = |s: &str| TypeExpr::Named(s.to_string(), vec![]);
    match ty {
        Type::I64 => named("i64"),
        Type::F64 => named("f64"),
        Type::Boolean => named("boolean"),
        Type::Char => named("Char"),
        Type::Str => named("String"),
        Type::Unit => TypeExpr::Unit,
        Type::Never => named("!"),
        Type::I8 => named("i8"),
        Type::I16 => named("i16"),
        Type::I32 => named("i32"),
        Type::U8 => named("u8"),
        Type::U16 => named("u16"),
        Type::U32 => named("u32"),
        Type::U64 => named("u64"),
        Type::F32 => named("f32"),
        Type::Tuple(items) => TypeExpr::Tuple(items.iter().map(type_to_type_expr).collect()),
        Type::Record(fields) => TypeExpr::Record(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), type_to_type_expr(ty)))
                .collect(),
        ),
        Type::Array(item) => TypeExpr::Array(Box::new(type_to_type_expr(item))),
        Type::SizedArray(item, n) => TypeExpr::SizedArray(Box::new(type_to_type_expr(item)), *n),
        Type::Reference(item) => TypeExpr::Reference(Box::new(type_to_type_expr(item))),
        Type::MutReference(item) => TypeExpr::MutReference(Box::new(type_to_type_expr(item))),
        Type::Fun(params, ret, call_multiplicity, _use_multiplicity, call_mutation) => {
            TypeExpr::Fun {
                params: params.iter().map(type_to_type_expr).collect(),
                return_type: Some(Box::new(type_to_type_expr(ret))),
                call_multiplicity: *call_multiplicity,
                call_mutation: *call_mutation,
            }
        }
        Type::Named(name, args) => {
            TypeExpr::Named(name.clone(), args.iter().map(type_to_type_expr).collect())
        }
        Type::Residual { brand, fields } => TypeExpr::RecordProjection {
            path: vec![brand.clone()],
            fields: fields.iter().map(|(name, _)| name.clone()).collect(),
            span: Span::new(0, 0, ""),
        },
        Type::Dyn { aspect, type_args } => TypeExpr::DynAspect {
            bound: Box::new(TypeExpr::Named(
                aspect.clone(),
                type_args.iter().map(type_to_type_expr).collect(),
            )),
            span: Span::new(0, 0, ""),
        },
    }
}

/// A synthetic single-field `Result::<variant>` pattern for the `?` desugar,
/// carrying the interned variant / field identities (ADR-0054 / #1062b).
fn result_variant_pattern(
    ctx: &ConstructCtx,
    variant: &str,
    field: &str,
    span: &Span,
) -> TypedPattern {
    let result_id = Some(crate::symbols::SYM_TYPE_RESULT);
    TypedPattern::EnumVariant {
        path: vec!["Result".to_string(), variant.to_string()],
        variant_id: ctx.variant_id_for(result_id, variant),
        // Synthetic `?`-desugar binding — no source span, so no `LocalId`; the
        // desugar's match stays name-keyed (isolated construct).
        fields: vec![(
            field.to_string(),
            ctx.variant_field_id(result_id, variant, field),
            None,
        )],
        rest: false,
        span: span.clone(),
    }
}

fn construct_propagate_error(
    expr: &Expr,
    span: &Span,
    ctx: &mut ConstructCtx,
) -> Result<TypedExpr, MetelError> {
    let scrutinee = construct_expr(expr, None, ctx)?;
    let (ok_ty, source_err_ty) = match scrutinee.ty() {
        Type::Named(name, args) if name == "Result" && args.len() == 2 => {
            (args[0].clone(), args[1].clone())
        }
        other => {
            return Err(MetelError::type_error(
                TypeErrorCode::T0005,
                format!("`?` requires a Result<T, E> expression, got `{other}`"),
                span,
            ));
        }
    };

    let return_ty = ctx.current_return_ty.clone().ok_or_else(|| {
        MetelError::type_error(
            TypeErrorCode::T0005,
            "`?` can only be used inside a function or closure that returns Result<T, E>",
            span,
        )
    })?;
    let target_err_ty = match &return_ty {
        Type::Named(name, args) if name == "Result" && args.len() == 2 => args[1].clone(),
        other => {
            return Err(MetelError::type_error(
                TypeErrorCode::T0005,
                format!(
                    "`?` requires the enclosing function to return Result<T, E>, got `{other}`"
                ),
                span,
            ));
        }
    };

    let ok_arm = TypedMatchArm {
        pattern: result_variant_pattern(ctx, "Ok", "value", span),
        guard: None,
        body: TypedBlock {
            stmts: vec![],
            tail: Some(Box::new(TypedExpr::Ident(
                "value".to_string(),
                None,
                ok_ty.clone(),
                span.clone(),
            ))),
            span: span.clone(),
        },
        span: span.clone(),
    };

    let err_value = if source_err_ty == target_err_ty {
        TypedExpr::Ident("error".to_string(), None, source_err_ty, span.clone())
    } else {
        TypedExpr::Cast {
            expr: Box::new(TypedExpr::Ident(
                "error".to_string(),
                None,
                source_err_ty,
                span.clone(),
            )),
            target_type: type_to_type_expr(&target_err_ty),
            ty: target_err_ty,
            span: span.clone(),
        }
    };
    let err_arm = TypedMatchArm {
        pattern: result_variant_pattern(ctx, "Err", "error", span),
        guard: None,
        body: TypedBlock {
            stmts: vec![TypedDecl::Stmt(Box::new(TypedStmt::Expr(
                TypedExpr::Return(TypedReturnExpr {
                    value: Some(Box::new(TypedExpr::StructLiteral {
                        path: vec!["Result".to_string(), "Err".to_string()],
                        fields: vec![("error".to_string(), err_value)],
                        ty: return_ty,
                        type_id: Some(crate::symbols::SYM_TYPE_RESULT),
                        variant_id: ctx
                            .variant_id_for(Some(crate::symbols::SYM_TYPE_RESULT), "Err"),
                        span: span.clone(),
                    })),
                    span: span.clone(),
                }),
            )))],
            tail: None,
            span: span.clone(),
        },
        span: span.clone(),
    };

    Ok(TypedExpr::Match(TypedMatchExpr {
        scrutinee: Box::new(scrutinee),
        arms: vec![ok_arm, err_arm],
        expr_type: ok_ty,
        span: span.clone(),
    }))
}

/// The first shared-reference type encountered walking an lvalue path towards its root,
/// if any. Mirrors `typed_ast::is_lvalue_path`'s shape deliberately: the two must agree on
/// what a path *is*, or one admits a form the other rejects (see #313).
fn shared_reference_root_in_lvalue_path(expr: &TypedExpr) -> Option<&Type> {
    match expr {
        TypedExpr::FieldAccess { object, .. }
        | TypedExpr::TupleAccess { object, .. }
        | TypedExpr::Index { object, .. }
        | TypedExpr::UnaryOp(UnaryOp::Deref, object, _, _) => {
            if let Type::Reference(inner) = object.ty() {
                Some(inner.as_ref())
            } else {
                shared_reference_root_in_lvalue_path(object)
            }
        }
        _ => None,
    }
}

fn construct_unaryop(
    op: &UnaryOp,
    operand: &Expr,
    span: &Span,
    expected_ty: Option<&Type>,
    ctx: &mut ConstructCtx,
) -> Result<TypedExpr, MetelError> {
    let operand = construct_expr(operand, expected_ty, ctx)?;
    let ty = match op {
        UnaryOp::Neg => {
            let t = operand.ty();
            if !matches!(t, Type::Never) && !t.is_numeric() {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0005,
                    format!("unary negation requires a numeric type operand, got `{t}`"),
                    span,
                ));
            }
            t.clone()
        }
        UnaryOp::Not => Type::Boolean,
        // metel-core#280: addressability is checked here, not at run time. The rule is
        // purely syntactic on the typed AST, so it was always static-determinable; the
        // evaluator used to decide it with the same predicate and raise
        // `MetelError::internal` on failure — an internal error for a documented,
        // user-reachable rejection (RFC-0044 §9), raised only after any side effects in
        // the surrounding statement had already run.
        UnaryOp::Ref | UnaryOp::RefMut => {
            if !crate::typed_ast::is_lvalue_path(&operand) {
                // `&<rvalue>` / `&var <rvalue>` is temporary lifetime extension
                // (matching Rust/C++: `foo(&Vec::new())`, `foo(&mut Vec::new())`):
                // materialize the value into a fresh, independent storage cell
                // instead of requiring the caller to bind it to a name first. Sound
                // for both forms — nothing outside this expression can ever alias the
                // cell, so a mutable reference to it can never conflict with anything.
                let mutable = matches!(op, UnaryOp::RefMut);
                let inner_ty = operand.ty().clone();
                let ty = if mutable {
                    Type::MutReference(Box::new(inner_ty))
                } else {
                    Type::Reference(Box::new(inner_ty))
                };
                return Ok(TypedExpr::RefTemp {
                    init: Box::new(operand),
                    mutable,
                    ty,
                    span: span.clone(),
                });
            }
            if matches!(op, UnaryOp::RefMut) {
                // `&var` cannot manufacture exclusive access out of any shared
                // reference encountered along the lvalue path, whether spelled
                // explicitly (`&var *r`) or through selectors (`&var r.field`).
                if let Some(shared_inner) = shared_reference_root_in_lvalue_path(&operand) {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0006,
                        format!(
                            "cannot take `&var` through a shared reference `&{shared_inner}`; \
                             a shared reference never grants write access"
                        ),
                        span,
                    ));
                }
            }
            if matches!(op, UnaryOp::RefMut) {
                Type::MutReference(Box::new(operand.ty().clone()))
            } else {
                Type::Reference(Box::new(operand.ty().clone()))
            }
        }
        UnaryOp::Deref => match operand.ty() {
            Type::Reference(inner) | Type::MutReference(inner) => *inner.clone(),
            t => {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0002,
                    format!("cannot dereference non-pointer type `{t}`"),
                    span,
                ));
            }
        },
    };
    Ok(TypedExpr::UnaryOp(
        op.clone(),
        Box::new(operand),
        ty,
        span.clone(),
    ))
}

/// Peels every reference layer of a chain down to the first non-reference type
/// (RFC-0067a §3's auto-deref chain guarantee — `&&T` derefs through both levels —
/// applies uniformly to field access, method dispatch, and read-copy; a single-level
/// peel leaves a receiver like `&&mut Counter` still wrapped after one step).
fn peel_type_references(ty: &Type) -> &Type {
    match ty {
        Type::Reference(inner) | Type::MutReference(inner) => peel_type_references(inner),
        other => other,
    }
}

fn type_chain_provides_mut_access(ty: &Type) -> bool {
    match ty {
        Type::MutReference(_) => true,
        Type::Reference(inner) => type_chain_provides_mut_access(inner),
        _ => false,
    }
}

/// RFC-0067a §3a: if `actual`'s type is a reference to exactly `expected`, synthesize
/// the internal deref-copy node so the value is copied out of the reference. The parser
/// never produces `UnaryOp::Deref` any more (§3 removed explicit `*p`); this is the only
/// place it's constructed post-RFC-0067a. Only called from sites that have a genuine
/// declared/expected type in hand (`construct_block`'s tail, `Stmt::Return`/`Break`,
/// `Decl::Let`/`Mut`, `Expr::Ascribe`) — never from `construct_expr`'s or
/// `construct_unaryop`'s generic dispatch, which call-argument construction also goes
/// through and must not gain this coercion.
/// Peels *every* reference layer needed to reach `expected`, not just one — RFC-0067a
/// §3's auto-deref chain guarantee (`&&T` derefs through both levels) applies to
/// read-copy the same as ordinary auto-deref: `let x: i64 = rr;` where `rr: &&i64`
/// synthesizes two nested internal `Deref` nodes, one per layer, matching how the
/// evaluator already unwraps one `Value::Reference`/`MutReference` per node.
///
/// #649: this is a *copy* — the referent is duplicated, not moved, and the reference
/// keeps pointing at a still-valid original — so it's only sound when the fully
/// peeled referent type is `Copy` (RFC-0067a §3a's own words: "a non-`Copy` `T`
/// cannot be produced this way"). Checked once against the final, fully-dereferenced
/// type, not each intermediate reference layer: a `&T`/`&var T` layer being read
/// *through* isn't itself what's being duplicated, only the payload at the end of
/// the chain is.
fn maybe_read_copy(
    expected: &Type,
    actual: TypedExpr,
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
) -> Result<TypedExpr, MetelError> {
    // If `expected` is itself a reference type, this isn't read-copy at all — it's the
    // ordinary `&mut T` -> `&T` widening coercion (unify() already accepts it; nothing
    // to synthesize here). Peeling anyway would over-run past the intended coercion
    // down to the fully-dereferenced value, which is wrong.
    if matches!(expected, Type::Reference(_) | Type::MutReference(_)) {
        return Ok(actual);
    }
    let mut current = actual;
    let mut peeled_any = false;
    while current.ty() != expected {
        let inner = match current.ty() {
            Type::Reference(inner) | Type::MutReference(inner) => (**inner).clone(),
            _ => break,
        };
        peeled_any = true;
        current = TypedExpr::UnaryOp(UnaryOp::Deref, Box::new(current), inner, span.clone());
    }
    if peeled_any && !registry.type_satisfies_aspect(current_module, current.ty(), "Copy") {
        let ty = current.ty();
        return Err(MetelError::type_error(
            TypeErrorCode::T0024,
            format!(
                "cannot copy `{ty}` out of a reference: `{ty}` does not implement `Copy`\n\
                 \x20      hint: use `.clone()` if `{ty}` implements `Clone`, or restructure to take ownership instead"
            ),
            span,
        ));
    }
    Ok(current)
}

/// RFC-0078 §3.3: the inhabited-singleton coercion. If `actual`'s type is a named
/// enum with more than one variant, exactly one of which is inhabited (by the same
/// rule `check_match_exhaustiveness` uses) with exactly one field, and that field's
/// (substituted) type equals `expected`, wrap `actual` in `SingletonCoerce`.
/// Otherwise return `actual` unchanged. Mirrors `maybe_read_copy`'s shape and
/// call-site pattern — called from the same handful of sites that have a genuine
/// expected type in hand.
fn maybe_singleton_coerce(
    expected: &Type,
    actual: TypedExpr,
    span: &Span,
    registry: &TypeDefinitionRegistry,
) -> Result<TypedExpr, MetelError> {
    let actual_ty = actual.ty().clone();
    if &actual_ty == expected {
        return Ok(actual);
    }
    let Type::Named(name, type_args) = &actual_ty else {
        return Ok(actual);
    };
    let Some(enum_info) = registry.enum_info_by_decl_name(name) else {
        return Ok(actual);
    };
    if enum_info.variants.len() <= 1 {
        return Ok(actual);
    }
    let remap = enum_variant_type_param_remap(enum_info, type_args);
    let mut inhabited: Option<&VariantInfo> = None;
    for v in &enum_info.variants {
        if is_variant_uninhabited(v, &remap, span) {
            continue;
        }
        if v.fields.len() != 1 || inhabited.is_some() {
            // Zero/multi-field sole-inhabited variant, or more than one inhabited
            // variant: the conditions for the rule don't hold (RFC-0078 §3.3).
            return Ok(actual);
        }
        inhabited = Some(v);
    }
    let Some(variant) = inhabited else {
        return Ok(actual);
    };
    let field = &variant.fields[0];
    let field_ty = infer_type_to_type(&remap.apply(&field.ty), &field.span)?;
    if &field_ty != expected {
        return Ok(actual);
    }
    Ok(TypedExpr::SingletonCoerce {
        inner: Box::new(actual),
        variant: variant.name.clone(),
        field: field.name.clone(),
        ty: field_ty,
        span: span.clone(),
    })
}

/// RFC-0008 §6: implicit coercion of a concrete value to an aspect object (`dyn
/// Aspect`). Mirrors `maybe_read_copy`/`maybe_singleton_coerce`'s shape and
/// call-site pattern — called from the same handful of sites that have a genuine
/// expected type in hand, plus the monomorphic argument-construction site (which
/// those two don't reach; argument-passing is checked by direct `Type` equality,
/// not through these coercion hooks).
///
/// Object safety is not re-checked here: `expected` being `Type::Dyn` at all
/// already passed `ty_at`'s `TypeExpr::DynAspect` arm (`projections.rs`), which
/// runs in a separate, earlier whole-program pass before Pass 1 inference even
/// starts — by construction, every `Type::Dyn` this function ever sees names an
/// object-safe aspect.
fn maybe_dyn_coerce(
    expected: &Type,
    actual: TypedExpr,
    span: &Span,
    ctx: &ConstructCtx,
) -> Result<TypedExpr, MetelError> {
    // `&dyn Aspect`/`&var dyn Aspect`: no runtime wrapping is needed here --
    // an ordinary reference to the concrete value, dispatched by its own
    // erased static type (RFC-0008 §1) -- a binding's/param's later uses
    // always resolve through its own *declared* type, never the RHS
    // expression's constructed type, so nothing downstream needs `actual`
    // itself retyped. But the aspect-satisfaction check still has to run
    // here: Pass 1's `unify` is deliberately permissive for *any* `Dyn`
    // pairing, reference-wrapped or not, precisely because it defers this
    // check to this function -- so without this branch, coercion behind a
    // reference was never actually checked anywhere, at any site.
    if let (
        Type::Reference(exp_inner) | Type::MutReference(exp_inner),
        Type::Reference(act_inner) | Type::MutReference(act_inner),
    ) = (expected, actual.ty())
    {
        if let Type::Dyn { aspect, .. } = exp_inner.as_ref() {
            if !matches!(act_inner.as_ref(), Type::Dyn { .. })
                && !ctx
                    .registry
                    .type_satisfies_aspect(ctx.current_module, act_inner, aspect)
            {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0012,
                    format!(
                        "`{act_inner}` does not implement `{aspect}` (required to coerce to `&dyn {aspect}`)"
                    ),
                    span,
                ));
            }
            return Ok(actual);
        }
    }
    let Type::Dyn { aspect, .. } = expected else {
        return Ok(actual);
    };
    let actual_ty = actual.ty().clone();
    if &actual_ty == expected {
        return Ok(actual);
    }
    // Already `dyn`-typed but under a different aspect (or the same aspect with
    // different type args): a real mismatch Pass 1's `unify` already rejects
    // (the `Dyn` unify arm only matches an identical `Dyn`) — nothing here to
    // coerce, so don't mask that error by falling through to the aspect check
    // below, which asks a different question (concrete-type membership) that a
    // `dyn`-typed `actual` can't meaningfully answer the same way.
    if matches!(actual_ty, Type::Dyn { .. }) {
        return Ok(actual);
    }
    if !ctx
        .registry
        .type_satisfies_aspect(ctx.current_module, &actual_ty, aspect)
    {
        return Err(MetelError::type_error(
            TypeErrorCode::T0012,
            format!(
                "`{actual_ty}` does not implement `{aspect}` (required to coerce to `dyn {aspect}`)"
            ),
            span,
        ));
    }
    let aspect_id = resolve_aspect_id(ctx, aspect).ok_or_else(|| {
        MetelError::internal(format!(
            "dyn Aspect coercion: `{aspect}` passed object-safety and aspect-satisfaction \
             checks but has no resolvable SymbolId"
        ))
    })?;
    Ok(TypedExpr::DynCoerce {
        inner: Box::new(actual),
        aspect_id,
        ty: expected.clone(),
        span: span.clone(),
    })
}

/// RFC-0166: a written function type `|T| -> U` is move-only. When a `let` / `var`
/// binding (or a `for`-init binding) is annotated with a function type, the
/// binding takes that written type — not the value's own. A function value the
/// compiler proved copyable (a named function, a capture-free closure) is
/// accepted into the slot by moving; its `Copy`-ness is dropped at the boundary
/// and not re-derived downstream. Re-stamping the RHS node's stated type here is
/// what makes the move checker (which reads `let_decl.value.ty()`) see the
/// binding as move-only.
///
/// Only the outer use-multiplicity axis can differ at this point — Pass 1's
/// `unify` already accepted the first-order `Copy → Move` direction and rejected
/// every genuine mismatch, so this never masks an error. `expected` not being a
/// function type, or `actual` already carrying it, is the no-op path.
fn maybe_fn_move_coerce(expected: &Type, actual: TypedExpr) -> TypedExpr {
    if !matches!(expected, Type::Fun(..)) || actual.ty() == expected {
        return actual;
    }
    if matches!(actual.ty(), Type::Fun(..)) {
        return actual.with_ty(expected.clone());
    }
    actual
}

// ── Typed place construction ──────────────────────────────────────────────────

fn assign_target_to_typed_place(
    target: &AssignTarget,
    ctx: &mut ConstructCtx<'_>,
) -> Result<TypedPlace, MetelError> {
    match target {
        AssignTarget::Ident(name, span) => Ok(TypedPlace::Ident(
            name.clone(),
            ctx.binding_id_at(span),
            span.clone(),
        )),
        AssignTarget::FieldAccess {
            object,
            field,
            span,
        } => Ok(TypedPlace::Field {
            object: Box::new(expr_to_typed_place(object, ctx)?),
            field: field.clone(),
            span: span.clone(),
        }),
        AssignTarget::TupleAccess {
            object,
            index,
            span,
        } => {
            let typed_object = expr_to_typed_place(object, ctx)?;
            let raw_object_ty = typed_place_ty(&typed_object, ctx, span)?;
            // Reach through a reference at the root, matching field/index paths.
            let object_ty = peel_type_references(&raw_object_ty).clone();
            match object_ty {
                Type::Tuple(elems) => {
                    if *index >= elems.len() {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0003,
                            format!(
                                "tuple index {index} out of bounds (tuple has {} elements)",
                                elems.len()
                            ),
                            span,
                        ));
                    }
                    Ok(TypedPlace::Tuple {
                        object: Box::new(typed_object),
                        index: *index,
                        span: span.clone(),
                    })
                }
                _ => Err(MetelError::type_error(
                    TypeErrorCode::T0002,
                    "cannot infer tuple type for assignment; add a type annotation",
                    span,
                )),
            }
        }
        AssignTarget::Index {
            object,
            index,
            span,
        } => {
            let typed_idx = construct_expr(index, Some(&Type::U64), ctx)?;
            if typed_idx.ty() != &Type::U64 {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0001,
                    format!(
                        "array index must be u64, got {}; use `expr as u64`",
                        typed_idx.ty()
                    ),
                    span,
                ));
            }
            Ok(TypedPlace::Index {
                object: Box::new(expr_to_typed_place(object, ctx)?),
                index: Box::new(typed_idx),
                span: span.clone(),
            })
        }
        // RFC-0110: `*p = v`. `*` must name a `&var T` — writing through a shared `&T`
        // is not permitted, matching `&`'s read-only contract.
        AssignTarget::Deref { object, span } => {
            let typed_object = construct_expr(object, None, ctx)?;
            match typed_object.ty() {
                Type::MutReference(_) => Ok(TypedPlace::Deref {
                    object: Box::new(typed_object),
                    span: span.clone(),
                }),
                t => Err(MetelError::type_error(
                    TypeErrorCode::T0002,
                    format!("cannot write through `{t}`; `&var T` required"),
                    span,
                )),
            }
        }
    }
}

fn expr_to_typed_place(expr: &Expr, ctx: &mut ConstructCtx<'_>) -> Result<TypedPlace, MetelError> {
    match expr {
        Expr::Ident(name, span) => Ok(TypedPlace::Ident(
            name.clone(),
            ctx.binding_id_at(span),
            span.clone(),
        )),
        Expr::FieldAccess {
            object,
            field,
            span,
        } => Ok(TypedPlace::Field {
            object: Box::new(expr_to_typed_place(object, ctx)?),
            field: field.clone(),
            span: span.clone(),
        }),
        Expr::TupleAccess {
            object,
            index,
            span,
        } => {
            let typed_object = expr_to_typed_place(object, ctx)?;
            let raw_object_ty = typed_place_ty(&typed_object, ctx, span)?;
            // Reach through a reference at the root, matching field/index paths.
            let object_ty = peel_type_references(&raw_object_ty).clone();
            match object_ty {
                Type::Tuple(elems) => {
                    if *index >= elems.len() {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0003,
                            format!(
                                "tuple index {index} out of bounds (tuple has {} elements)",
                                elems.len()
                            ),
                            span,
                        ));
                    }
                    Ok(TypedPlace::Tuple {
                        object: Box::new(typed_object),
                        index: *index,
                        span: span.clone(),
                    })
                }
                _ => Err(MetelError::type_error(
                    TypeErrorCode::T0002,
                    "cannot infer tuple type for assignment; add a type annotation",
                    span,
                )),
            }
        }
        Expr::Index {
            object,
            index,
            span,
        } => {
            let typed_idx = construct_expr(index, Some(&Type::U64), ctx)?;
            if typed_idx.ty() != &Type::U64 {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0001,
                    format!(
                        "array index must be u64, got {}; use `expr as u64`",
                        typed_idx.ty()
                    ),
                    span,
                ));
            }
            Ok(TypedPlace::Index {
                object: Box::new(expr_to_typed_place(object, ctx)?),
                index: Box::new(typed_idx),
                span: span.clone(),
            })
        }
        Expr::UnaryOp(UnaryOp::Deref, inner, span) => Ok(TypedPlace::Deref {
            object: Box::new(construct_expr(inner, None, ctx)?),
            span: span.clone(),
        }),
        _ => Err(MetelError::internal(
            "invalid sub-expression in assignment target",
        )),
    }
}

fn typed_place_ty(
    place: &TypedPlace,
    ctx: &mut ConstructCtx<'_>,
    span: &Span,
) -> Result<Type, MetelError> {
    match place {
        TypedPlace::Ident(name, _, ident_span) => ctx.lookup(name).cloned().ok_or_else(|| {
            MetelError::type_error(
                TypeErrorCode::T0003,
                format!("use of undeclared variable `{name}`"),
                ident_span,
            )
        }),
        TypedPlace::Deref { object, .. } => match object.ty() {
            Type::MutReference(inner) => Ok((**inner).clone()),
            t => Err(MetelError::type_error(
                TypeErrorCode::T0002,
                format!("cannot write through `{t}`; `&var T` required"),
                span,
            )),
        },
        TypedPlace::Field {
            object,
            field,
            span: field_span,
        } => {
            // Reach through a reference at any step of the path, not just the root:
            // `s.t.0 = v` for `s: &var S` resolves `s.t` through this arm.
            let object_ty = peel_type_references(&typed_place_ty(object, ctx, field_span)?).clone();
            typed_place_field_ty(&object_ty, field, field_span, ctx)
        }
        TypedPlace::Tuple {
            object,
            index,
            span,
        } => {
            let object_ty = peel_type_references(&typed_place_ty(object, ctx, span)?).clone();
            match object_ty {
                Type::Tuple(elems) => elems.get(*index).cloned().ok_or_else(|| {
                    MetelError::type_error(
                        TypeErrorCode::T0003,
                        format!(
                            "tuple index {index} out of bounds (tuple has {} elements)",
                            elems.len()
                        ),
                        span,
                    )
                }),
                _ => Err(MetelError::type_error(
                    TypeErrorCode::T0002,
                    "cannot infer tuple type for assignment; add a type annotation",
                    span,
                )),
            }
        }
        TypedPlace::Index { object, .. } => {
            let object_ty = peel_type_references(&typed_place_ty(object, ctx, span)?).clone();
            match object_ty {
                Type::SizedArray(elem, _) => Ok((*elem).clone()),
                // Not T0002 (#633): the element type is already known here --
                // `values: i64[]` is fully annotated -- and no annotation
                // could fix this. `T[]` views are unconditionally immutable
                // through an index (RFC-0126), independent of whether the
                // binding itself is `var`; that's a different failure shape
                // than T0006's three forms (all of which name a `let`
                // binding that a `var` would fix).
                Type::Array(_) => Err(MetelError::type_error(
                    TypeErrorCode::T0023,
                    "cannot assign through `T[]`: array views are immutable; use `[T; N]` or `List<T>`",
                    span,
                )),
                _ => Err(MetelError::type_error(
                    TypeErrorCode::T0002,
                    "cannot infer array type for assignment; add a type annotation",
                    span,
                )),
            }
        }
    }
}

fn typed_place_field_ty(
    object_ty: &Type,
    field: &str,
    field_span: &Span,
    ctx: &mut ConstructCtx<'_>,
) -> Result<Type, MetelError> {
    match object_ty {
        Type::Record(fields) => fields
            .iter()
            .find(|(name, _)| name == field)
            .map(|(_, ty)| ty.clone())
            .ok_or_else(|| {
                MetelError::type_error(
                    TypeErrorCode::T0003,
                    format!("no field `{field}` on record"),
                    field_span,
                )
            }),
        Type::Named(struct_name, type_args) => {
            let struct_id = ctx
                .registry
                .resolve_type_id(ctx.current_module, struct_name);
            if let Some(type_params) =
                struct_id.and_then(|id| ctx.registry.raw_struct_type_params().get(&id))
            {
                let raw_fields = struct_id
                    .and_then(|id| ctx.registry.raw_struct_env().get(&id))
                    .ok_or_else(|| {
                        MetelError::type_error(
                            TypeErrorCode::T0003,
                            format!("unknown type `{struct_name}`"),
                            field_span,
                        )
                    })?;
                let raw_ty = raw_fields
                    .iter()
                    .find(|entry| entry.name == field)
                    .map(|entry| entry.ty.clone())
                    .ok_or_else(|| {
                        MetelError::type_error(
                            TypeErrorCode::T0003,
                            format!("no field `{field}` on `{struct_name}`"),
                            field_span,
                        )
                    })?;
                let mut remap = Substitution::new();
                for (&tp, arg) in type_params.iter().zip(type_args.iter()) {
                    remap.bind(tp, type_to_infer(arg));
                }
                infer_type_to_type(&remap.apply(&raw_ty), field_span)
            } else {
                let fields = ctx.get_struct_fields(struct_name).ok_or_else(|| {
                    MetelError::type_error(
                        TypeErrorCode::T0003,
                        format!("unknown type `{struct_name}`"),
                        field_span,
                    )
                })?;
                let field_entry =
                    fields
                        .iter()
                        .find(|entry| entry.0 == field)
                        .ok_or_else(|| {
                            MetelError::type_error(
                                TypeErrorCode::T0003,
                                format!("no field `{field}` on `{struct_name}`"),
                                field_span,
                            )
                        })?;
                Ok(field_entry.1.clone())
            }
        }
        _ => Err(MetelError::type_error(
            TypeErrorCode::T0002,
            "cannot infer struct type for field assignment; add a type annotation",
            field_span,
        )),
    }
}
