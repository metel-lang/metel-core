use std::collections::HashMap;

use crate::ast::{
    AspectMethod, AssignOp, AssignTarget, BinOp, Block, Bound, BoundHead, Decl, Expr, ForInit,
    FunDecl, GenericParam, ImplBlock, Literal, MatchExpr, Param, Pattern, Polarity, Program, Span,
    Stmt, TypeExpr, UnaryOp, Visibility,
};
use crate::error::{MetelError, TypeErrorCode};
use crate::typeinference::{
    free_vars, generalize, AspectAssumptions, EnumInfo, FieldEntry, GenericBound, InferContext,
    InferType, Substitution, TypeScheme, TypeVar, VariantInfo,
};
use crate::types::Type;

use super::conversions::{
    infer_type_to_type, type_expr_to_infer, type_expr_to_infer_with_assoc_ctx,
    type_expr_to_infer_with_generics, type_expr_to_infer_with_generics_and_self,
    type_expr_to_infer_with_self, type_to_infer, AssocResolveCtx,
};
use super::FunGeneralization;

fn type_expr_to_infer_with_ctx(
    te: &TypeExpr,
    generics: &HashMap<String, TypeVar>,
    ctx: &InferContext,
) -> InferType {
    let assoc_ctx = AssocResolveCtx {
        registry: ctx.registry(),
        current_module: ctx.current_module_path(),
        current_aspect: None,
    };
    type_expr_to_infer_with_assoc_ctx(te, generics, None, &assoc_ctx)
}

/// Build the per-quantified-var `assoc_projections` map from the body's recorded
/// projection log and the post-solve substitution. Each entry
/// `(base_tv, aspect, assoc, placeholder)` is resolved through `subst`; if
/// `base_tv` is still a free `Var` after resolution, it's a quantified var in
/// the scheme and gets its projection info attached.
fn build_assoc_projection_map(
    body_assoc_log: &[(TypeVar, String, String, TypeVar)],
    subst: &crate::typeinference::Substitution,
    scheme: &crate::typeinference::TypeScheme,
) -> std::collections::HashMap<TypeVar, (usize, String, String, TypeVar)> {
    use std::collections::HashMap;
    let mut map: HashMap<TypeVar, (usize, String, String, TypeVar)> = HashMap::new();
    for (base_tv, aspect, assoc, placeholder) in body_assoc_log {
        let InferType::Var(resolved) = subst.apply(&InferType::Var(*base_tv)) else {
            continue;
        };
        if let Some(pos) = scheme.quantified_vars.iter().position(|&v| v == resolved) {
            map.entry(resolved)
                .or_insert_with(|| (pos, aspect.clone(), assoc.clone(), *placeholder));
        }
    }
    map
}

/// Resolve a type annotation, substituting any name that matches the current
/// function's generic type params with the corresponding `TypeVar` rather than
/// producing a Named type.  Must be used for all annotations inside function
/// bodies; bare `type_expr_to_infer` ignores the param map.
///
/// Takes `&mut InferContext` (not `&`) so the abstract-case branch below can mint a
/// real `fresh_assoc_projection_var` directly, the same one `infer_fun_decl`'s and
/// `infer_impl_method`'s own signature-resolution closures already mint for a
/// `T::AssocType` (or, since #740/#774's revision, `Self::AssocType`) appearing in a
/// param or return-type position. Every call site already holds `&mut ctx` for other
/// reasons (`infer_expr`, `ctx.solve()`, `ctx.bind_mono`, ...), so this doesn't
/// restrict any of them -- it used to return an inert `Named` placeholder here
/// instead, correct only where *something else* backfilled it afterward, which is
/// true of the two signature call sites but not of a body-internal `let x:
/// T::AssocType = ...;`/`mut`/`Expr::Ascribe`/`Expr::Cast`/closure-param annotation,
/// none of which have any such backfill step. The type var minted here needs no
/// backfill of its own: unlike the *scheme's* `assoc_projections` map (resolved at
/// a later call site, once the caller's concrete argument pins the base type), this
/// is resolved by ordinary unification against whatever the body already
/// constrains that base type variable to, within the same inference pass.
fn ann_to_infer(te: &TypeExpr, ctx: &mut InferContext) -> InferType {
    // Check for abstract-case projection first.
    if let TypeExpr::Projection {
        base,
        ref assoc_name,
        ..
    } = te
    {
        if let TypeExpr::Named(ref n, _) = **base {
            if let Some(base_tv) = ctx.type_params().get(n.as_str()).copied() {
                let mut matching_aspect = None;
                if let Some(bounds) = ctx.bounds_for_type_var(base_tv) {
                    for aspect in bounds.iter().filter_map(GenericBound::aspect_name) {
                        if let Some(decls) = ctx.aspect_assoc_type_decls(aspect) {
                            if decls.iter().any(|d| d.name == *assoc_name) {
                                matching_aspect = Some(aspect.to_string());
                                break;
                            }
                        }
                    }
                }
                if let Some(aspect) = matching_aspect {
                    return InferType::Var(
                        ctx.fresh_assoc_projection_var(base_tv, &aspect, assoc_name),
                    );
                }
            }
        }
    }
    // #774 (revised): a record projection whose one-segment path names a type param
    // already bound to a concrete `Named` type (`Self`, always; an ordinary generic
    // only incidentally, if something upstream already pinned it) -- resolve it by
    // asking the solver what that type param currently stands for, rather than
    // needing a `self_ty_name` threaded in from a caller that (here, in body
    // position) has no such name to give. `type_expr_to_infer_with_ctx`'s own
    // `AssocResolveCtx` always carries `self_ty_name: None`, which is right for a
    // context with no enclosing `Self` at all -- this only fires when there
    // demonstrably is one.
    if let TypeExpr::RecordProjection { path, .. } = te {
        if let [name] = path.as_slice() {
            if let Some(base_tv) = ctx.type_params().get(name.as_str()).copied() {
                // Speculative: `solve()` now mutates `cached_subst` in place, so
                // checkpoint and roll back if this probe fails to solve.
                let checkpoint = ctx.solve_checkpoint();
                let solved = ctx.solve();
                if solved.is_err() {
                    ctx.solve_restore(checkpoint);
                }
                if let Ok(solved) = solved {
                    if let InferType::Named(concrete_name, ..)
                    | InferType::Concrete(Type::Named(concrete_name, ..)) =
                        solved.apply(&InferType::Var(base_tv))
                    {
                        let assoc_ctx = AssocResolveCtx {
                            registry: ctx.registry(),
                            current_module: ctx.current_module_path(),
                            current_aspect: None,
                        };
                        return type_expr_to_infer_with_assoc_ctx(
                            te,
                            &HashMap::new(),
                            Some(&concrete_name),
                            &assoc_ctx,
                        );
                    }
                }
            }
        }
    }
    let params = ctx.type_params().clone();
    type_expr_to_infer_with_ctx(te, &params, ctx)
}

/// RFC-0008 §6 / metel-core#876: `ann` names an array (`T[]`) or sized-array
/// (`[T; N]`) whose element type is written as `dyn Aspect` — returns that
/// element bound. Purely syntactic on the *unconverted* annotation, no
/// `ctx` involved, so calling it costs nothing and allocates no fresh var,
/// unlike converting the whole annotation via `ann_to_infer`.
fn dyn_array_elem_ann(ann: &TypeExpr) -> Option<&TypeExpr> {
    let elem = match ann {
        TypeExpr::Array(elem) | TypeExpr::SizedArray(elem, _) => elem.as_ref(),
        _ => return None,
    };
    matches!(elem, TypeExpr::DynAspect { .. }).then_some(elem)
}

/// RFC-0008 §6 / metel-core#876: infer a `dyn Aspect`-annotated array
/// literal's elements against the *known* declared element type directly,
/// instead of `infer_expr`'s ordinary `Expr::Array` handling, which unifies
/// every element against the first element's own inferred type — that would
/// reject two different concrete types in one literal outright, before
/// either ever gets a chance to coerce to the aspect, defeating the entire
/// point of a heterogeneous `dyn Aspect` array (`List<dyn Aspect>` covers
/// the same use case via `push`, one element at a time, so this is the
/// array-literal-specific gap).
///
/// Constraining each element against `elem_ty` (rather than unifying them
/// against each other) reuses the ordinary `ctx.add_constraint` mechanism —
/// nothing new: the already-existing permissive `Dyn`-vs-concrete `unify`
/// arm (RFC-0008 slice 2) already accepts any concrete element against a
/// `Dyn` element type, deferring the real aspect-satisfaction check to
/// `maybe_dyn_coerce` in Pass 2 construction, same as every other coercion
/// site.
///
/// Scoped narrowly to the two call sites that already have a genuine
/// annotation in hand (`Decl::Let`/`Decl::Mut`) — a heterogeneous array
/// literal used directly as a function argument or struct field, with no
/// annotated binding in between, is unaffected (Pass 1 doesn't thread an
/// expected type into any other sub-expression); bind it to a `let`/`var`
/// first if that's ever needed.
fn infer_dyn_array_literal(
    elems: &[Expr],
    elem_ty: &InferType,
    span: &Span,
    ctx: &mut InferContext,
    fun_generalizations: &mut Vec<FunGeneralization>,
) -> Result<InferType, MetelError> {
    for elem in elems {
        let ty = infer_expr(elem, ctx, fun_generalizations)?;
        ctx.add_constraint(ty, elem_ty.clone(), span.clone());
    }
    Ok(InferType::Array(Box::new(elem_ty.clone())))
}

/// Register the names of all direct `FunDecl`s in `decls` with fresh type
/// variables so that forward references and mutual recursion work.
/// The function type of a `native` declaration, built from its annotations,
/// plus the aspect bounds of its generic params keyed by their `TypeVars` (so
/// the caller can attach them to the generalized scheme).
struct NativeFunTyResult {
    fun_ty: InferType,
    bounds: HashMap<TypeVar, Vec<GenericBound>>,
    neg_bounds: HashMap<TypeVar, Vec<GenericBound>>,
    record_kinds: HashMap<TypeVar, bool>,
    assoc_eq: HashMap<TypeVar, Vec<(String, String, InferType)>>,
}

fn native_fun_ty(fun: &FunDecl, ctx: &mut InferContext) -> Result<NativeFunTyResult, MetelError> {
    // Generic native functions (e.g. `print<T: Display>`) map each type
    // parameter to a fresh TypeVar; the caller generalizes the result into a
    // polymorphic scheme carrying the bounds.
    let generic_map = fun_generic_map(fun, ctx);
    let bounds_by_var = collect_fun_type_var_bounds(fun, &generic_map);
    let neg_bounds_by_var = collect_negative_fun_type_var_bounds(fun, &generic_map);
    let record_kinds_by_var = collect_fun_type_var_record_kinds(fun, &generic_map);
    let assoc_eq_by_var = collect_fun_assoc_eq_constraints(fun, &generic_map);
    let te_to_infer =
        |te: &TypeExpr| -> InferType { type_expr_to_infer_with_ctx(te, &generic_map, ctx) };
    let mut param_types = Vec::with_capacity(fun.params.len());
    for p in &fun.params {
        let ann = p.type_ann.as_ref().ok_or_else(|| {
            MetelError::type_error(
                TypeErrorCode::T0002,
                format!(
                    "native function `{}` requires a type annotation on every parameter",
                    fun.name
                ),
                &p.span,
            )
        })?;
        param_types.push(te_to_infer(ann));
    }
    let ret_ty = match &fun.return_type {
        Some(te) => te_to_infer(te),
        None => InferType::unit(),
    };
    Ok(NativeFunTyResult {
        fun_ty: InferType::fun(param_types, ret_ty),
        bounds: bounds_by_var,
        neg_bounds: neg_bounds_by_var,
        record_kinds: record_kinds_by_var,
        assoc_eq: assoc_eq_by_var,
    })
}

/// A binding of one of an impl's own generic parameters: the type variable
/// that stands for it structurally, and the name it was written with.
///
/// Both are needed and they serve different jobs. The variable is what the
/// aspect query reasons about — a parameter is not a named type, so it must
/// not be *representable* as one. The name is only ever used to render a
/// diagnostic, which is a presentation concern and deliberately kept out of
/// the representation.
struct ImplParam {
    var: TypeVar,
    name: String,
}

/// Fresh variables for an impl's own generic parameters, paired with the
/// aspects each may be assumed to satisfy.
///
/// Every parameter gets an entry, including unbounded ones: an empty
/// assumption set says "abstract, and guarantees nothing", which is what makes
/// an unbounded `<T>` fail a `Copy` check rather than pass it.
fn impl_params(ib: &ImplBlock, ctx: &mut InferContext) -> (Vec<ImplParam>, AspectAssumptions) {
    let mut params = Vec::new();
    let mut assumptions = AspectAssumptions::new();
    for param in &ib.generics {
        let InferType::Var(var) = ctx.fresh_var() else {
            continue;
        };
        params.push(ImplParam {
            var,
            name: param.name.clone(),
        });
        let entry = assumptions.entry(var).or_default();
        for bound in &param.bounds {
            if bound.polarity == Polarity::Positive {
                if let Some(aspect) = bound.aspect_name() {
                    entry.insert(aspect.to_string());
                }
            }
        }
    }
    if let Some(where_clause) = &ib.where_clause {
        for constraint in &where_clause.constraints {
            // A `where` subject that is not one of the impl's own parameters
            // constrains something else entirely; it says nothing about what
            // this impl may assume.
            let Some(param) = params.iter().find(|p| p.name == constraint.name) else {
                continue;
            };
            let entry = assumptions.entry(param.var).or_default();
            for bound in &constraint.bounds {
                if bound.polarity == Polarity::Positive {
                    if let Some(aspect) = bound.aspect_name() {
                        entry.insert(aspect.to_string());
                    }
                }
            }
        }
    }
    (params, assumptions)
}

fn infer_type_to_concrete_if_closed(ty: &InferType) -> Option<Type> {
    match ty {
        InferType::Concrete(concrete) => Some(concrete.clone()),
        InferType::Tuple(items) => items
            .iter()
            .map(infer_type_to_concrete_if_closed)
            .collect::<Option<Vec<_>>>()
            .map(Type::Tuple),
        InferType::Array(item) => {
            infer_type_to_concrete_if_closed(item).map(|item| Type::Array(Box::new(item)))
        }
        InferType::SizedArray(item, size) => infer_type_to_concrete_if_closed(item)
            .map(|item| Type::SizedArray(Box::new(item), *size)),
        InferType::Reference(item) => {
            infer_type_to_concrete_if_closed(item).map(|item| Type::Reference(Box::new(item)))
        }
        InferType::MutReference(item) => {
            infer_type_to_concrete_if_closed(item).map(|item| Type::MutReference(Box::new(item)))
        }
        InferType::Named(name, args, ..) => args
            .iter()
            .map(infer_type_to_concrete_if_closed)
            .collect::<Option<Vec<_>>>()
            .map(|args| Type::Named(name.clone(), args, crate::types::NominalId::NONE)),
        InferType::Dyn { aspect, type_args } => type_args
            .iter()
            .map(infer_type_to_concrete_if_closed)
            .collect::<Option<Vec<_>>>()
            .map(|type_args| Type::Dyn {
                aspect: aspect.clone(),
                type_args,
            }),
        InferType::Never
        | InferType::Var(_)
        | InferType::Fun(..)
        | InferType::Record(_)
        | InferType::Residual { .. } => None,
    }
}

/// Whether `ty` mentions any of `params` anywhere inside it.
fn mentions_type_param(ty: &TypeExpr, params: &std::collections::HashSet<&str>) -> bool {
    let go = |t: &TypeExpr| mentions_type_param(t, params);
    match ty {
        TypeExpr::Named(name, args) => params.contains(name.as_str()) || args.iter().any(go),
        TypeExpr::Tuple(items) => items.iter().any(go),
        TypeExpr::Record(fields) => fields.iter().any(|(_, t)| go(t)),
        TypeExpr::Array(inner)
        | TypeExpr::SizedArray(inner, _)
        | TypeExpr::Reference(inner)
        | TypeExpr::MutReference(inner) => go(inner),
        TypeExpr::Fun {
            params: ps,
            return_type: ret,
            ..
        } => ps.iter().any(go) || ret.as_deref().is_some_and(go),
        TypeExpr::Projection { base, .. } => go(base),
        TypeExpr::DynAspect { bound, .. } => go(bound),
        TypeExpr::Unit | TypeExpr::ImplAspect { .. } | TypeExpr::RecordProjection { .. } => false,
    }
}

/// An impl's target type as a concrete `Type`, but only when the target is
/// *closed*: a nominal type mentioning none of the impl's own generic
/// parameters.
///
/// Closedness has to be tested against `ib.generics` explicitly rather than
/// left to `infer_type_to_concrete_if_closed`, which cannot see it. Given
/// `extend<T: !Copy> Foo<T>: Drop`, that function reduces `Foo<T>` to a
/// perfectly concrete `Foo` applied to a nominal type *literally named* `T` —
/// closed as far as it can tell. The RFC-0071 §4 checks below would then ask
/// whether that type implements the other aspect, and `type_satisfies_aspect`
/// would match any conditional impl of it while ignoring the bounds that
/// cannot be evaluated against a placeholder — rejecting valid pairs like
/// `extend<T: Copy> Foo<T>: Copy` alongside `extend<T: !Copy> Foo<T>: Drop`,
/// where no instantiation can satisfy both.
///
/// Open targets are not unchecked: `coherence`'s cross-aspect overlap check
/// handles them precisely, comparing the two impls' bounds instead of
/// discarding them (issue #302).
fn closed_nominal_target(ib: &ImplBlock, target_name: &str) -> Option<Type> {
    if !matches!(&ib.target_type, TypeExpr::Named(_, _)) {
        return None;
    }
    let params: std::collections::HashSet<&str> =
        ib.generics.iter().map(|g| g.name.as_str()).collect();
    if mentions_type_param(&ib.target_type, &params) {
        return None;
    }
    infer_type_to_concrete_if_closed(&type_expr_to_infer_with_self(&ib.target_type, target_name))
}

/// `ty` with the struct's or enum's own type variables replaced by the
/// corresponding arguments of the impl's target type.
///
/// An argument that *is* one of the impl's own generic parameters becomes that
/// parameter's type variable — structurally a variable, never a named type.
/// That is the whole distinction: a field type written in the struct's scope
/// keeps whatever that scope meant by it, while a position filled from the
/// impl's target takes the impl's meaning, so a parameter correctly shadows a
/// same-named type in exactly the positions where it should and nowhere else.
fn substitute_impl_params(
    ty: &InferType,
    type_param_args: &HashMap<TypeVar, &TypeExpr>,
    params: &[ImplParam],
) -> InferType {
    let go = |t: &InferType| substitute_impl_params(t, type_param_args, params);
    match ty {
        InferType::Var(var) => type_param_args
            .get(var)
            .map_or_else(|| ty.clone(), |arg| type_expr_as_infer(arg, params)),
        InferType::Tuple(items) => InferType::Tuple(items.iter().map(go).collect()),
        InferType::Record(fields) => InferType::Record(
            fields
                .iter()
                .map(|(label, field_ty)| (label.clone(), go(field_ty)))
                .collect(),
        ),
        InferType::Array(item) => InferType::Array(Box::new(go(item))),
        InferType::SizedArray(item, size) => InferType::SizedArray(Box::new(go(item)), *size),
        InferType::Reference(item) => InferType::Reference(Box::new(go(item))),
        InferType::MutReference(item) => InferType::MutReference(Box::new(go(item))),
        InferType::Named(name, args, ..) => InferType::Named(
            name.clone(),
            args.iter().map(go).collect(),
            crate::types::NominalId::NONE,
        ),
        InferType::Fun(ps, ret, call_mult, use_mult, call_mutation) => InferType::Fun(
            ps.iter().map(go).collect(),
            Box::new(go(ret)),
            *call_mult,
            *use_mult,
            *call_mutation,
        ),
        InferType::Residual { brand, fields } => InferType::Residual {
            brand: brand.clone(),
            fields: fields
                .iter()
                .map(|(label, field_ty)| (label.clone(), go(field_ty)))
                .collect(),
        },
        InferType::Dyn { aspect, type_args } => InferType::Dyn {
            aspect: aspect.clone(),
            type_args: type_args.iter().map(go).collect(),
        },
        InferType::Concrete(_) | InferType::Never => ty.clone(),
    }
}

/// An impl target argument as an `InferType`, with any mention of the impl's
/// own generic parameters resolved to their type variables.
fn type_expr_as_infer(ty: &TypeExpr, params: &[ImplParam]) -> InferType {
    if let TypeExpr::Named(name, args) = ty {
        if args.is_empty() {
            if let Some(param) = params.iter().find(|p| &p.name == name) {
                return InferType::Var(param.var);
            }
        }
    }
    let go = |t: &TypeExpr| type_expr_as_infer(t, params);
    match ty {
        TypeExpr::Named(name, args) => InferType::Named(
            name.clone(),
            args.iter().map(go).collect(),
            crate::types::NominalId::NONE,
        ),
        TypeExpr::Tuple(items) => InferType::Tuple(items.iter().map(go).collect()),
        TypeExpr::Record(fields) => InferType::Record(
            fields
                .iter()
                .map(|(label, field_ty)| (label.clone(), go(field_ty)))
                .collect(),
        ),
        TypeExpr::Array(inner) => InferType::Array(Box::new(go(inner))),
        TypeExpr::SizedArray(inner, size) => InferType::SizedArray(Box::new(go(inner)), *size),
        TypeExpr::Reference(inner) => InferType::Reference(Box::new(go(inner))),
        TypeExpr::MutReference(inner) => InferType::MutReference(Box::new(go(inner))),
        // Anything without a parameter to resolve keeps the ordinary lowering.
        _ => type_expr_to_infer(ty),
    }
}

/// A substituted type rendered the way it was written, with each parameter's
/// variable shown under its own name.
///
/// The names live here rather than in the type because they are a
/// presentation concern: printing `Inner<?t16>` was the diagnostic half of
/// issue #303, and the fix is to render variables properly, not to make the
/// representation carry a name it should not have.
fn display_type(ty: &InferType, params: &[ImplParam]) -> String {
    match ty {
        InferType::Var(var) => params
            .iter()
            .find(|p| p.var == *var)
            .map_or_else(|| ty.to_string(), |p| p.name.clone()),
        InferType::Named(name, args, ..) if !args.is_empty() => {
            let rendered: Vec<String> = args.iter().map(|a| display_type(a, params)).collect();
            format!("{name}<{}>", rendered.join(", "))
        }
        InferType::Tuple(items) => {
            let rendered: Vec<String> = items.iter().map(|i| display_type(i, params)).collect();
            format!("({})", rendered.join(", "))
        }
        InferType::Array(item) => format!("{}[]", display_type(item, params)),
        InferType::SizedArray(item, size) => format!("[{}; {size}]", display_type(item, params)),
        InferType::Reference(item) => format!("&{}", display_type(item, params)),
        InferType::MutReference(item) => format!("&var {}", display_type(item, params)),
        _ => ty.to_string(),
    }
}

/// Whether a field or payload type, already substituted by
/// `substitute_impl_params`, is `Copy` under the impl's own bounds.
///
/// Defers entirely to the registry's query rather than walking the type. It
/// used to walk it, in two mutually recursive functions that re-stated the
/// `Copy` rules for tuples, fixed arrays and references — a third copy of
/// rules that already live in the query, and the copy that had drifted: it
/// answered `false` for any named type with an unresolved argument, which is
/// issue #303's wrong rejection.
fn substituted_type_is_copy(
    ty: &InferType,
    assumptions: &AspectAssumptions,
    registry: &crate::typeinference::TypeDefinitionRegistry,
    current_module: &[String],
) -> bool {
    registry.infer_type_satisfies_aspect(current_module, ty, "Copy", assumptions)
}

fn check_copy_impl_eligibility(
    ib: &ImplBlock,
    target_name: &str,
    ctx: &mut InferContext,
) -> Result<(), MetelError> {
    let (params, assumptions) = impl_params(ib, ctx);
    let mut type_param_args: HashMap<TypeVar, &TypeExpr> = HashMap::new();
    if let TypeExpr::Named(_, target_args) = &ib.target_type {
        let target_id = ctx
            .registry()
            .resolve_type_id(ctx.current_module_path(), target_name);
        if let Some(struct_params) =
            target_id.and_then(|id| ctx.registry().raw_struct_type_params().get(&id))
        {
            for (param, arg) in struct_params.iter().zip(target_args.iter()) {
                type_param_args.insert(*param, arg);
            }
        } else if let Some(enum_info) = ctx
            .registry()
            .enum_info(ctx.current_module_path(), target_name)
        {
            for (param, arg) in enum_info.type_params.iter().zip(target_args.iter()) {
                type_param_args.insert(*param, arg);
            }
        }
    }

    if let Some(fields) = ctx.get_struct_fields(target_name) {
        for field in fields {
            let field_ty = substitute_impl_params(&field.ty, &type_param_args, &params);
            if !substituted_type_is_copy(
                &field_ty,
                &assumptions,
                ctx.registry(),
                ctx.current_module_path(),
            ) {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0001,
                    format!(
                        "cannot implement `Copy` for `{target_name}`: field `{}` has type `{}` which is not `Copy`",
                        field.name,
                        display_type(&field_ty, &params)
                    ),
                    &field.span,
                ));
            }
        }
    } else if let Some(enum_info) = ctx.get_enum(target_name) {
        for variant in &enum_info.variants {
            for field in &variant.fields {
                let field_ty = substitute_impl_params(&field.ty, &type_param_args, &params);
                if !substituted_type_is_copy(
                    &field_ty,
                    &assumptions,
                    ctx.registry(),
                    ctx.current_module_path(),
                ) {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0001,
                        format!(
                            "cannot implement `Copy` for `{target_name}`: payload `{}` of variant `{}::{}` has type `{}` which is not `Copy`",
                            field.name,
                            target_name,
                            variant.name,
                            display_type(&field_ty, &params)
                        ),
                        &field.span,
                    ));
                }
            }
        }
    }

    if let Some(concrete_target) = closed_nominal_target(ib, target_name) {
        if ctx
            .registry()
            .type_satisfies_aspect(ctx.current_module_path(), &concrete_target, "Drop")
        {
            return Err(MetelError::type_error(
                TypeErrorCode::T0001,
                format!("`{target_name}` cannot implement both `Copy` and `Drop`"),
                &ib.span,
            ));
        }
    }

    Ok(())
}

#[allow(clippy::too_many_lines)]
pub(super) fn hoist_fun_decls(decls: &[Decl], ctx: &mut InferContext) {
    for decl in decls {
        if let Decl::Fun(fun) = decl {
            // Overloaded names are not bound to a single shared type — each
            // definition is checked independently and dispatched by SymbolId
            // (METEL-180). Binding here would unify their distinct signatures.
            // This applies to native overloads too (std::core's assert pair).
            if ctx.is_overloaded(&fun.name) {
                continue;
            }
            // Native functions have a concrete annotated signature and no body;
            // bind it eagerly so forward references resolve. Errors here surface
            // again (deterministically) in infer_fun_decl.
            if fun.native.is_some() {
                if let Ok(result) = native_fun_ty(fun, ctx) {
                    let env_fvs = ctx.env_free_vars();
                    ctx.bind_poly(
                        &fun.name,
                        generalize(result.fun_ty, &env_fvs)
                            .with_bounds(&result.bounds)
                            .with_neg_bounds(&result.neg_bounds)
                            .with_assoc_eq_constraints(&result.assoc_eq),
                    );
                }
                continue;
            }
            if fun.generics.is_empty() {
                let fresh = ctx.fresh_var();
                ctx.bind_mono(&fun.name, fresh.clone(), false);
                // Also bind in poly_env so user declarations shadow any imported binding
                // (poly_env lookup takes precedence over mono_env regardless of scope level).
                ctx.bind_poly(&fun.name, TypeScheme::mono(fresh));
            } else {
                let generic_map = fun_generic_map(fun, ctx);
                let type_var_bounds = collect_fun_type_var_bounds(fun, &generic_map);
                let neg_type_var_bounds = collect_negative_fun_type_var_bounds(fun, &generic_map);
                if !type_var_bounds.is_empty() {
                    ctx.register_fun_bounds(fun.name.clone(), type_var_bounds.clone());
                }
                if !neg_type_var_bounds.is_empty() {
                    ctx.register_neg_fun_bounds(fun.name.clone(), neg_type_var_bounds.clone());
                }
                let assoc_eq_by_var = collect_fun_assoc_eq_constraints(fun, &generic_map);
                if !assoc_eq_by_var.is_empty() {
                    ctx.register_fun_assoc_eq_constraints(fun.name.clone(), assoc_eq_by_var);
                }

                let te_to_infer = |te: &TypeExpr, ctx: &mut InferContext| -> InferType {
                    if let TypeExpr::Projection {
                        base,
                        ref assoc_name,
                        ..
                    } = te
                    {
                        if let TypeExpr::Named(ref n, _) = **base {
                            if let Some(&base_tv) = generic_map.get(n.as_str()) {
                                // NOTE: use the locally-computed `type_var_bounds` map, not
                                // `ctx.bounds_for_type_var` -- that reads `current_type_param_bounds`,
                                // which is only populated by `swap_type_param_bounds` during body
                                // inference (`infer_fun_decl`), which hasn't run yet at hoist time.
                                // Using it here always finds no bounds and silently produces a
                                // stale, unresolved `Named("T::Item", [])` that then fails to unify
                                // with the correctly-resolved type computed later.
                                if let Some(bounds) = type_var_bounds.get(&base_tv) {
                                    for aspect in
                                        bounds.iter().filter_map(GenericBound::aspect_name)
                                    {
                                        if let Some(decls) = ctx.aspect_assoc_type_decls(aspect) {
                                            if decls.iter().any(|d| d.name == *assoc_name) {
                                                return InferType::Var(
                                                    ctx.fresh_assoc_projection_var(
                                                        base_tv, aspect, assoc_name,
                                                    ),
                                                );
                                            }
                                        }
                                    }
                                }
                                return InferType::Named(
                                    format!("{n}::{assoc_name}"),
                                    vec![],
                                    crate::types::NominalId::NONE,
                                );
                            }
                        }
                    }
                    type_expr_to_infer_with_generics(te, &generic_map)
                };

                let param_types: Vec<InferType> = fun
                    .params
                    .iter()
                    .map(|p| {
                        if let Some(ann) = &p.type_ann {
                            te_to_infer(ann, ctx)
                        } else {
                            ctx.fresh_var()
                        }
                    })
                    .collect();

                let ret_ty = if let Some(ann) = &fun.return_type {
                    if type_expr_contains_impl_aspect(ann) {
                        // RFC-0037: use fresh marker vars for `impl Aspect`
                        // return positions in the provisional (hoist-time)
                        // scheme too, so forward references don't leak the
                        // aspect name as a concrete nominal type into the
                        // pre-registration constraint.
                        let mut rw_counter = 0usize;
                        let mut replacements: Vec<(String, String)> = Vec::new();
                        let rewritten =
                            rewrite_impl_aspect_returns(ann, &mut rw_counter, &mut replacements);
                        let mut extended_map = generic_map.clone();
                        for (placeholder, _) in &replacements {
                            let tv = ctx.fresh_type_var_raw();
                            extended_map.insert(placeholder.clone(), tv);
                        }
                        type_expr_to_infer_with_generics(&rewritten, &extended_map)
                    } else {
                        te_to_infer(ann, ctx)
                    }
                } else {
                    ctx.fresh_var()
                };

                let env_fvs = ctx.env_free_vars();
                let provisional_fun_ty = InferType::fun(param_types, ret_ty);
                let provisional_scheme = generalize(provisional_fun_ty, &env_fvs);
                ctx.bind_poly(&fun.name, provisional_scheme);
            }
        }
    }
}

fn fun_generic_map(fun: &FunDecl, ctx: &mut InferContext) -> HashMap<String, TypeVar> {
    fun.generics
        .iter()
        .map(|g| (g.name.clone(), ctx.fresh_type_var_raw()))
        .collect()
}

pub(super) fn collect_fun_type_var_bounds(
    fun: &FunDecl,
    generic_map: &HashMap<String, TypeVar>,
) -> HashMap<TypeVar, Vec<GenericBound>> {
    let mut map: HashMap<TypeVar, Vec<GenericBound>> = HashMap::new();
    for gp in &fun.generics {
        if let Some(&tv) = generic_map.get(&gp.name) {
            let names: Vec<GenericBound> = gp
                .bounds
                .iter()
                .filter_map(|b| {
                    // Negative bounds (`T: !Drop`) are dropped from this positive
                    // aspect-name list for now — their satisfaction checking is
                    // issue #243's job, not this one's.
                    if b.polarity != crate::ast::Polarity::Positive {
                        return None;
                    }
                    GenericBound::from_ast(b)
                })
                .collect();
            if !names.is_empty() {
                map.entry(tv).or_default().extend(names);
            }
        }
    }
    if let Some(wc) = &fun.where_clause {
        for constraint in &wc.constraints {
            if let Some(&tv) = generic_map.get(constraint.name.as_str()) {
                let names: Vec<GenericBound> = constraint
                    .bounds
                    .iter()
                    .filter(|b| b.polarity == Polarity::Positive)
                    .filter_map(GenericBound::from_ast)
                    .collect();
                for name in names {
                    let entry = map.entry(tv).or_default();
                    if !entry.iter().any(|existing| matches!((existing, &name), (GenericBound::Aspect(a), GenericBound::Aspect(b)) if a == b)) {
                        entry.push(name);
                    }
                }
            }
        }
    }
    map
}

/// Collect **negative** aspect-name bounds per generic type variable (RFC-0072,
/// issue #243). Mirrors `collect_fun_type_var_bounds` but filters for
/// `Polarity::Negative`.
pub(super) fn collect_negative_fun_type_var_bounds(
    fun: &FunDecl,
    generic_map: &HashMap<String, TypeVar>,
) -> HashMap<TypeVar, Vec<GenericBound>> {
    let mut map: HashMap<TypeVar, Vec<GenericBound>> = HashMap::new();
    for gp in &fun.generics {
        if let Some(&tv) = generic_map.get(&gp.name) {
            let names: Vec<GenericBound> = gp
                .bounds
                .iter()
                .filter_map(|b| {
                    if b.polarity != crate::ast::Polarity::Negative {
                        return None;
                    }
                    GenericBound::from_ast(b)
                })
                .collect();
            if !names.is_empty() {
                map.entry(tv).or_default().extend(names);
            }
        }
    }
    if let Some(wc) = &fun.where_clause {
        for constraint in &wc.constraints {
            if let Some(&tv) = generic_map.get(constraint.name.as_str()) {
                let names: Vec<GenericBound> = constraint
                    .bounds
                    .iter()
                    .filter(|b| b.polarity == Polarity::Negative)
                    .filter_map(GenericBound::from_ast)
                    .collect();
                for name in names {
                    let entry = map.entry(tv).or_default();
                    if !entry.iter().any(|existing| matches!((existing, &name), (GenericBound::Aspect(a), GenericBound::Aspect(b)) if a == b)) {
                        entry.push(name);
                    }
                }
            }
        }
    }
    map
}

pub(super) fn collect_fun_type_var_record_kinds(
    fun: &FunDecl,
    generic_map: &HashMap<String, TypeVar>,
) -> HashMap<TypeVar, bool> {
    let mut map: HashMap<TypeVar, bool> = HashMap::new();
    for gp in &fun.generics {
        if gp.is_record {
            if let Some(&tv) = generic_map.get(&gp.name) {
                map.insert(tv, true);
            }
        }
    }
    if let Some(wc) = &fun.where_clause {
        for constraint in &wc.constraints {
            if constraint.is_record {
                if let Some(&tv) = generic_map.get(constraint.name.as_str()) {
                    map.insert(tv, true);
                }
            }
        }
    }
    map
}

/// Collect equality constraints (`Aspect<AssocType = ConcreteType>`, RFC-0082 §4)
/// per generic type variable. Mirrors `collect_fun_type_var_bounds`'s shape, but
/// reads `Bound.assoc_bindings` instead of just the bound's aspect name. Each
/// entry is `(aspect_name, assoc_name, expected_infer_type)` — `expected_infer_type`
/// is converted via `type_expr_to_infer_with_generics` so a sibling type param
/// (the `U` in `Deref<Target = U>`, RFC-0082 §3a's escape hatch) stays a `TypeVar`
/// rather than becoming a dangling `Named("U", [])`.
pub(super) fn collect_fun_assoc_eq_constraints(
    fun: &FunDecl,
    generic_map: &HashMap<String, TypeVar>,
) -> HashMap<TypeVar, Vec<(String, String, InferType)>> {
    let mut map: HashMap<TypeVar, Vec<(String, String, InferType)>> = HashMap::new();
    let mut collect_from_bounds = |tv: TypeVar, bounds: &[Bound]| {
        for b in bounds {
            if b.polarity != Polarity::Positive || b.assoc_bindings.is_empty() {
                continue;
            }
            let Some(aspect_name) = b.aspect_name() else {
                continue;
            };
            for (assoc_name, assoc_ty) in &b.assoc_bindings {
                let expected = type_expr_to_infer_with_generics(assoc_ty, generic_map);
                map.entry(tv).or_default().push((
                    aspect_name.to_string(),
                    assoc_name.clone(),
                    expected,
                ));
            }
        }
    };
    for gp in &fun.generics {
        if let Some(&tv) = generic_map.get(&gp.name) {
            collect_from_bounds(tv, &gp.bounds);
        }
    }
    if let Some(wc) = &fun.where_clause {
        for constraint in &wc.constraints {
            if let Some(&tv) = generic_map.get(constraint.name.as_str()) {
                collect_from_bounds(tv, &constraint.bounds);
            }
        }
    }
    map
}

pub(super) fn infer_program(
    program: &Program,
    ctx: &mut InferContext,
    fun_generalizations: &mut Vec<FunGeneralization>,
) -> Result<(), MetelError> {
    for decl in &program.decls {
        infer_decl(decl, ctx, fun_generalizations)?;
    }
    Ok(())
}

struct SignatureEnv {
    generic_vars: HashMap<String, TypeVar>,
    alias_types: HashMap<String, InferType>,
    self_ty: InferType,
}

fn signature_type_expr_to_infer(te: &TypeExpr, env: &SignatureEnv) -> InferType {
    let go = |ty: &TypeExpr| signature_type_expr_to_infer(ty, env);
    match te {
        TypeExpr::Named(name, args) if args.is_empty() => {
            if let Some(&var) = env.generic_vars.get(name) {
                InferType::Var(var)
            } else if let Some(ty) = env.alias_types.get(name) {
                ty.clone()
            } else if name == "Self" {
                env.self_ty.clone()
            } else if let Some(prim) = primitive_type_from_name(name) {
                InferType::Concrete(prim)
            } else {
                InferType::Named(name.clone(), vec![], crate::types::NominalId::NONE)
            }
        }
        TypeExpr::Named(name, args) => InferType::Named(
            name.clone(),
            args.iter().map(go).collect(),
            crate::types::NominalId::NONE,
        ),
        TypeExpr::Unit => InferType::unit(),
        TypeExpr::Tuple(items) => InferType::Tuple(items.iter().map(go).collect()),
        TypeExpr::Record(fields) => InferType::Record(
            fields
                .iter()
                .map(|(label, ty)| (label.clone(), go(ty)))
                .collect(),
        ),
        TypeExpr::Array(inner) => InferType::Array(Box::new(go(inner))),
        TypeExpr::SizedArray(inner, size) => InferType::SizedArray(Box::new(go(inner)), *size),
        TypeExpr::Reference(inner) => InferType::Reference(Box::new(go(inner))),
        TypeExpr::MutReference(inner) => InferType::MutReference(Box::new(go(inner))),
        TypeExpr::Fun {
            params,
            return_type: ret,
            call_multiplicity,
            call_mutation,
        } => InferType::Fun(
            params.iter().map(go).collect(),
            Box::new(ret.as_deref().map_or_else(InferType::unit, go)),
            *call_multiplicity,
            crate::types::UseMultiplicity::Move,
            *call_mutation,
        ),
        TypeExpr::ImplAspect { bound, .. } => go(bound),
        TypeExpr::Projection {
            base, assoc_name, ..
        } => {
            if let TypeExpr::Named(base_name, args) = base.as_ref() {
                if base_name == "Self" && args.is_empty() {
                    if let Some(ty) = env.alias_types.get(assoc_name) {
                        return ty.clone();
                    }
                }
            }
            let base_ty = go(base);
            InferType::Named(
                format!("{base_ty:?}::{assoc_name}"),
                vec![],
                crate::types::NominalId::NONE,
            )
        }
        TypeExpr::RecordProjection { path, fields, .. } => InferType::Named(
            format!("{}.{{ {} }}", path.join("::"), fields.join(", ")),
            vec![],
            crate::types::NominalId::NONE,
        ),
        TypeExpr::DynAspect { bound, .. } => {
            let TypeExpr::Named(aspect, args) = bound.as_ref() else {
                unreachable!("dyn_type grammar only ever produces a named_type bound")
            };
            InferType::Dyn {
                aspect: aspect.clone(),
                type_args: args.iter().map(go).collect(),
            }
        }
    }
}

fn signature_param_type(param: &Param, env: &SignatureEnv) -> InferType {
    if param.name == "self" {
        env.self_ty.clone()
    } else {
        param
            .type_ann
            .as_ref()
            .map_or_else(InferType::unit, |ty| signature_type_expr_to_infer(ty, env))
    }
}

fn impl_signature_self_type(ib: &ImplBlock, params: &[ImplParam], target_name: &str) -> InferType {
    if matches!(&ib.target_type, TypeExpr::Named(name, args) if args.is_empty() && name == target_name)
    {
        if let Some(prim) = primitive_type_from_name(target_name) {
            return InferType::Concrete(prim);
        }
    }
    type_expr_as_infer(&ib.target_type, params)
}

fn next_signature_type_var(next_id: &mut u32) -> TypeVar {
    let var = TypeVar(*next_id);
    *next_id += 1;
    var
}

fn impl_signature_params(ib: &ImplBlock, next_type_var_id: &mut u32) -> Vec<ImplParam> {
    ib.generics
        .iter()
        .map(|param| ImplParam {
            var: next_signature_type_var(next_type_var_id),
            name: param.name.clone(),
        })
        .collect()
}

fn aspect_impl_method_signature_matches(
    method: &FunDecl,
    declared: &AspectMethod,
    ib: &ImplBlock,
    aspect_name: &str,
    target_name: &str,
    ctx: &InferContext,
) -> bool {
    if method.generics.len() != declared.generics.len()
        || method.params.len() != declared.params.len()
    {
        return false;
    }

    let Some(aspect_generics) = ctx.aspect_generics(aspect_name).cloned() else {
        return false;
    };
    if aspect_generics.len() != ib.aspect_type_args.len() {
        return false;
    }

    let mut next_type_var_id = 0;
    let impl_params = impl_signature_params(ib, &mut next_type_var_id);
    let self_ty = impl_signature_self_type(ib, &impl_params, target_name);
    let impl_generic_vars: HashMap<String, TypeVar> = impl_params
        .iter()
        .map(|param| (param.name.clone(), param.var))
        .collect();
    let method_generic_pairs: Vec<(&str, &str, TypeVar)> = method
        .generics
        .iter()
        .zip(&declared.generics)
        .map(|(actual, expected)| {
            (
                actual.name.as_str(),
                expected.name.as_str(),
                next_signature_type_var(&mut next_type_var_id),
            )
        })
        .collect();
    let actual_generic_vars: HashMap<String, TypeVar> = impl_generic_vars
        .iter()
        .map(|(name, var)| (name.clone(), *var))
        .chain(
            method_generic_pairs
                .iter()
                .map(|(actual_name, _, var)| ((*actual_name).to_string(), *var)),
        )
        .collect();
    // Resolving `aspect_type_args`/`assoc_type_defs`' own type exprs (the values on
    // the right of `type Item = i64;`) never itself needs an alias-type lookup, so
    // this pass can run with an empty map.
    let alias_resolve_env = SignatureEnv {
        generic_vars: actual_generic_vars.clone(),
        alias_types: HashMap::new(),
        self_ty: self_ty.clone(),
    };
    let mut alias_types: HashMap<String, InferType> = aspect_generics
        .iter()
        .zip(&ib.aspect_type_args)
        .map(|(name, arg)| {
            (
                name.clone(),
                signature_type_expr_to_infer(arg, &alias_resolve_env),
            )
        })
        .collect();
    for assoc_type in &ib.assoc_type_defs {
        alias_types.insert(
            assoc_type.name.clone(),
            signature_type_expr_to_infer(&assoc_type.ty, &alias_resolve_env),
        );
    }
    // #740 part A: the *actual* (impl) method's own signature can spell its
    // associated type as `Self::Item` just as legitimately as the aspect's declared
    // signature can spell it as bare `Item` (§1.2 sugar) -- both need the same
    // `alias_types` to resolve, or `fun get(&self) -> Self::Item { ... }` gets
    // compared against `fun get(&self) -> Item;` using two different resolutions of
    // the same associated type and fails this check as a false mismatch.
    let actual_env = SignatureEnv {
        alias_types: alias_types.clone(),
        ..alias_resolve_env
    };
    let declared_generic_vars: HashMap<String, TypeVar> = declared
        .generics
        .iter()
        .zip(&method_generic_pairs)
        .map(|(param, (_, _, var))| (param.name.clone(), *var))
        .collect();
    let expected_env = SignatureEnv {
        generic_vars: declared_generic_vars,
        alias_types,
        self_ty,
    };

    // RFC-0129 legality-13: the impl method's generic constraints must be
    // structurally equal to the aspect method's after normalization.
    if !generic_constraints_match(method, declared, &actual_env, &expected_env) {
        return false;
    }

    method
        .params
        .iter()
        .zip(&declared.params)
        .all(|(actual, expected)| {
            actual.receiver.as_ref().map(std::mem::discriminant)
                == expected.receiver.as_ref().map(std::mem::discriminant)
                && signature_param_type(actual, &actual_env)
                    == signature_param_type(expected, &expected_env)
        })
        && method
            .return_type
            .as_ref()
            .map_or_else(InferType::unit, |ty| {
                signature_type_expr_to_infer(ty, &actual_env)
            })
            == declared
                .return_type
                .as_ref()
                .map_or_else(InferType::unit, |ty| {
                    signature_type_expr_to_infer(ty, &expected_env)
                })
}

/// RFC-0129 legality-13: whether the impl method's generic constraints are
/// structurally equal to the aspect method's after normalization. An aspect-method
/// declaration carries every constraint inline on `declared.generics` -- it has no
/// `where` clause (metel-core#896) -- while the impl method may split its own
/// between the generic binder and a `where` clause, so fold the two together
/// first. `actual_env`/`expected_env` map a generic parameter to a shared
/// per-position type variable, so parameter names compare alpha-equivalently and
/// `Self` / aspect arguments / associated types resolve to the same identity on
/// both sides. Bound order and duplicates do not matter; neither weakening nor
/// strengthening a constraint conforms.
fn generic_constraints_match(
    method: &FunDecl,
    declared: &AspectMethod,
    actual_env: &SignatureEnv,
    expected_env: &SignatureEnv,
) -> bool {
    method
        .generics
        .iter()
        .zip(&declared.generics)
        .all(|(actual_gp, declared_gp)| {
            let actual_where = method
                .where_clause
                .as_ref()
                .and_then(|wc| wc.constraint_for(&actual_gp.name));
            let actual_is_record =
                actual_gp.is_record || actual_where.is_some_and(|constraint| constraint.is_record);
            if actual_is_record != declared_gp.is_record {
                return false;
            }
            let mut actual_bounds: Vec<String> = actual_gp
                .bounds
                .iter()
                .chain(actual_where.into_iter().flat_map(|c| c.bounds.iter()))
                .map(|bound| canonical_generic_bound(bound, actual_env))
                .collect();
            let mut declared_bounds: Vec<String> = declared_gp
                .bounds
                .iter()
                .map(|bound| canonical_generic_bound(bound, expected_env))
                .collect();
            for bounds in [&mut actual_bounds, &mut declared_bounds] {
                bounds.sort();
                bounds.dedup();
            }
            actual_bounds == declared_bounds
        })
}

/// A source-spelling-independent key for one generic-parameter [`Bound`], used by
/// [`generic_constraints_match`] to compare an impl method's generic constraints
/// against the aspect method's (RFC-0129 legality-13). Constituent type
/// expressions are resolved through `env` so `Self`, aspect arguments, associated
/// types, and generic parameters compare by identity rather than spelling; row
/// fields and associated-type bindings are sorted so field/binding order does not
/// matter.
fn canonical_generic_bound(bound: &Bound, env: &SignatureEnv) -> String {
    let polarity = match bound.polarity {
        Polarity::Positive => "",
        Polarity::Negative => "!",
    };
    let head = match &bound.head {
        BoundHead::Aspect(te) => format!("{:?}", signature_type_expr_to_infer(te, env)),
        BoundHead::Row(row) => {
            let mut fields: Vec<String> = row
                .fields
                .iter()
                .map(|field| {
                    let ty = field.ty.as_ref().map_or_else(
                        || "_".to_string(),
                        |t| format!("{:?}", signature_type_expr_to_infer(t, env)),
                    );
                    format!("{}:{ty}", field.label)
                })
                .collect();
            fields.sort();
            format!("row(open={},{})", row.open, fields.join(","))
        }
    };
    let mut assoc: Vec<String> = bound
        .assoc_bindings
        .iter()
        .map(|(label, te)| format!("{label}={:?}", signature_type_expr_to_infer(te, env)))
        .collect();
    assoc.sort();
    format!("{polarity}{head}[{}]", assoc.join(","))
}

mod declarations;
use declarations::{infer_decl, rewrite_impl_aspect_returns, type_expr_contains_impl_aspect};

mod narrowing;

fn infer_block(
    block: &Block,
    ctx: &mut InferContext,
    fun_generalizations: &mut Vec<FunGeneralization>,
) -> Result<InferType, MetelError> {
    ctx.push_scope();
    ctx.push_struct_scope();
    // Hoist struct/enum declarations defined in this block before inferring any stmt,
    // so they can be referenced anywhere within the block regardless of order.
    for decl in &block.stmts {
        match decl {
            Decl::Struct(sd) => {
                let fields = sd
                    .fields
                    .iter()
                    .map(|f| FieldEntry {
                        name: f.name.clone(),
                        ty: type_expr_to_infer(&f.type_ann),
                        span: f.span.clone(),
                        visibility: f.visibility.clone(),
                        id: None,
                    })
                    .collect();
                ctx.register_struct_fields(sd.name.clone(), fields, sd.visibility.clone());
            }
            Decl::Enum(ed) => {
                let variants = ed
                    .variants
                    .iter()
                    .map(|v| VariantInfo {
                        name: v.name.clone(),
                        fields: v
                            .fields
                            .iter()
                            .map(|f| FieldEntry {
                                name: f.name.clone(),
                                ty: type_expr_to_infer(&f.type_ann),
                                span: f.span.clone(),
                                visibility: f.visibility.clone(),
                                id: None,
                            })
                            .collect(),
                        id: None,
                    })
                    .collect();
                ctx.register_enum(
                    ed.name.clone(),
                    EnumInfo {
                        type_params: vec![],
                        variants,
                    },
                );
            }
            _ => {}
        }
    }
    hoist_fun_decls(&block.stmts, ctx);
    let mut last_stmt_ty = InferType::unit();
    for stmt in &block.stmts {
        last_stmt_ty = infer_decl(stmt, ctx, fun_generalizations)?;
    }
    let ty = match &block.tail {
        Some(tail) => infer_expr(tail, ctx, fun_generalizations)?,
        None => last_stmt_ty,
    };
    ctx.pop_struct_scope();
    ctx.pop_scope();
    Ok(ty)
}

mod expressions;
use expressions::{infer_expr, infer_stmt};

mod patterns;
use patterns::{
    builtin_pattern_method_type, chain_provides_mut_access, infer_match, is_shared_reference_chain,
    named_type_name, peel_all_references, record_projection_base_expr, resolve_row_bound_field,
};
pub(super) use patterns::{primitive_type_from_name, primitive_type_name};

fn infer_literal(lit: &Literal, ctx: &mut InferContext) -> InferType {
    use crate::ast::{FloatKind, IntKind};
    match lit {
        Literal::Int(_) => ctx.fresh_integer_literal_var(),
        Literal::Float(_) => ctx.fresh_float_literal_var(),
        Literal::SizedInt { kind, .. } => InferType::Concrete(match kind {
            IntKind::I8 => Type::I8,
            IntKind::I16 => Type::I16,
            IntKind::I32 => Type::I32,
            IntKind::I64 => Type::I64,
            IntKind::U8 => Type::U8,
            IntKind::U16 => Type::U16,
            IntKind::U32 => Type::U32,
            IntKind::U64 => Type::U64,
        }),
        Literal::SizedFloat { kind, .. } => InferType::Concrete(match kind {
            FloatKind::F32 => Type::F32,
            FloatKind::F64 => Type::F64,
        }),
        Literal::Char(_) => InferType::Concrete(Type::Char),
        Literal::Boolean(_) => InferType::bool(),
        Literal::Str(_) => InferType::str(),
        Literal::Unit => InferType::unit(),
    }
}

fn infer_binop(
    lhs: &Expr,
    op: &BinOp,
    rhs: &Expr,
    span: &Span,
    ctx: &mut InferContext,
    fun_generalizations: &mut Vec<FunGeneralization>,
) -> Result<InferType, MetelError> {
    let lhs_ty = infer_expr(lhs, ctx, fun_generalizations)?;
    let rhs_ty = infer_expr(rhs, ctx, fun_generalizations)?;
    match op {
        BinOp::Add => {
            let subst = ctx.solve()?;
            let lhs_resolved = subst.apply(&lhs_ty);
            let rhs_resolved = subst.apply(&rhs_ty);
            if matches!(lhs_resolved, InferType::Concrete(Type::Str))
                || matches!(rhs_resolved, InferType::Concrete(Type::Str))
            {
                match (&lhs_resolved, &rhs_resolved) {
                    (InferType::Concrete(Type::Str), InferType::Concrete(Type::Str)) => {
                        return Ok(InferType::str());
                    }
                    (InferType::Concrete(Type::Str), InferType::Var(v))
                    | (InferType::Var(v), InferType::Concrete(Type::Str)) => {
                        // Numeric literal TypeVars cannot be String — reject with
                        // T0005. Walk through `default_literal_vars` rather than a
                        // bare `is_integer_literal_var`/`is_float_literal_var`
                        // check (same fix as #236's method-dispatch case, above):
                        // `v` may not be the literal's own TypeVar but one merely
                        // unified with it, e.g. a generic struct field recovered
                        // from an int literal — a direct containment check misses
                        // that and would fall through to a confusing `cannot
                        // unify` (T0001) instead of this dedicated T0005 message.
                        let defaulted = ctx.default_literal_vars(&subst);
                        let resolved_numeric = defaulted.apply(&InferType::Var(*v));
                        if matches!(resolved_numeric, InferType::Concrete(Type::I64 | Type::F64)) {
                            // Report the concrete type this var just defaulted to,
                            // not its raw `?tN` name — we've already proven it's
                            // i64/f64, so the diagnostic should say so instead of
                            // leaking an internal TypeVar identifier.
                            let (lhs_display, rhs_display) = match &lhs_resolved {
                                InferType::Var(_) => {
                                    (resolved_numeric.to_string(), rhs_resolved.to_string())
                                }
                                _ => (lhs_resolved.to_string(), resolved_numeric.to_string()),
                            };
                            return Err(MetelError::type_error(
                                TypeErrorCode::T0005,
                                format!("`+` requires i64, f64, or String operands, got `{lhs_display}` and `{rhs_display}`"),
                                span,
                            ));
                        }
                        ctx.add_constraint(lhs_ty, InferType::str(), span.clone());
                        ctx.add_constraint(rhs_ty, InferType::str(), span.clone());
                        return Ok(InferType::str());
                    }
                    _ => {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0005,
                            format!(
                                "`+` requires i64, f64, or String operands, got `{lhs_resolved}` and `{rhs_resolved}`"
                            ),
                            span,
                        ));
                    }
                }
            }
            let result = ctx.fresh_var();
            ctx.add_operand_constraint(lhs_ty, result.clone(), span.clone(), op.symbol());
            ctx.add_operand_constraint(rhs_ty, result.clone(), span.clone(), op.symbol());
            Ok(result)
        }
        BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
            let result = ctx.fresh_var();
            ctx.add_operand_constraint(lhs_ty, result.clone(), span.clone(), op.symbol());
            ctx.add_operand_constraint(rhs_ty, result.clone(), span.clone(), op.symbol());
            Ok(result)
        }
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            // Tagged with the operator so a mismatch names it (`operator `==` cannot be
            // applied to `i64` and `String``) instead of the bare `cannot unify`, which
            // never mentioned that a comparison was what required the two to agree.
            ctx.add_operand_constraint(lhs_ty, rhs_ty, span.clone(), op.symbol());
            Ok(InferType::bool())
        }
        BinOp::And | BinOp::Or => {
            ctx.add_constraint(lhs_ty, InferType::bool(), span.clone());
            ctx.add_constraint(rhs_ty, InferType::bool(), span.clone());
            Ok(InferType::bool())
        }
        BinOp::Range | BinOp::RangeInclusive => {
            ctx.add_constraint(lhs_ty, InferType::int(), span.clone());
            ctx.add_constraint(rhs_ty, InferType::int(), span.clone());
            Ok(InferType::Named(
                "Range".to_string(),
                vec![InferType::int()],
                crate::types::NominalId::NONE,
            ))
        }
    }
}

fn infer_propagate_error(
    expr: &Expr,
    span: &Span,
    ctx: &mut InferContext,
    fun_generalizations: &mut Vec<FunGeneralization>,
) -> Result<InferType, MetelError> {
    let ok_ty = ctx.fresh_var();
    let source_err_ty = ctx.fresh_var();
    let inner_ty = infer_expr(expr, ctx, fun_generalizations)?;
    ctx.add_constraint(
        inner_ty,
        InferType::Named(
            "Result".to_string(),
            vec![ok_ty.clone(), source_err_ty.clone()],
            crate::types::NominalId::NONE,
        ),
        span.clone(),
    );

    let expected_return = ctx.current_return_type().cloned().ok_or_else(|| {
        MetelError::type_error(
            TypeErrorCode::T0005,
            "`?` can only be used inside a function or closure that returns Result<T, E>",
            span,
        )
    })?;

    let target_ok_ty = ctx.fresh_var();
    let target_err_ty = ctx.fresh_var();
    ctx.add_constraint(
        expected_return,
        InferType::Named(
            "Result".to_string(),
            vec![target_ok_ty, target_err_ty.clone()],
            crate::types::NominalId::NONE,
        ),
        span.clone(),
    );

    let subst = ctx.solve()?;
    let source_resolved = subst.apply(&source_err_ty);
    let target_resolved = subst.apply(&target_err_ty);
    if source_resolved != target_resolved {
        let source_concrete = infer_to_type_for_from(&source_resolved);
        let target_name = infer_type_name(&target_resolved);
        if let (Some(src_t), Some(tgt)) = (source_concrete.as_ref(), target_name) {
            if !ctx.has_from_impl(tgt, src_t) {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0007,
                    format!(
                        "cannot propagate `{source_resolved}` as `{target_resolved}` — no `impl From<{source_resolved}> for {target_resolved}` found"
                    ),
                    span,
                ));
            }
        }
    }

    Ok(ok_ty)
}

fn infer_unaryop(
    op: &UnaryOp,
    operand: &Expr,
    span: &Span,
    ctx: &mut InferContext,
    fun_generalizations: &mut Vec<FunGeneralization>,
) -> Result<InferType, MetelError> {
    let ty = infer_expr(operand, ctx, fun_generalizations)?;
    match op {
        UnaryOp::Neg => Ok(ty),
        UnaryOp::Not => {
            ctx.add_constraint(ty, InferType::bool(), span.clone());
            Ok(InferType::bool())
        }
        UnaryOp::Ref => Ok(InferType::Reference(Box::new(ty))),
        UnaryOp::RefMut => {
            if let Expr::Ident(name, ident_span) = operand {
                let _ = ctx.lookup_for_write(name, ident_span)?;
            }
            Ok(InferType::MutReference(Box::new(ty)))
        }
        UnaryOp::Deref => match ctx.solve()?.apply(&ty) {
            InferType::Reference(inner) | InferType::MutReference(inner) => Ok(*inner),
            other => Err(MetelError::type_error(
                TypeErrorCode::T0002,
                format!("cannot dereference non-pointer type `{other}`"),
                span,
            )),
        },
    }
}

/// RFC-0067a §3a: constrain `actual` against `declared`, except when `actual` is
/// *syntactically* a reference and `declared` isn't — then constrain the *referent*
/// against `declared` instead (a type-directed copy out of the reference). Only
/// applies where a literal declared type is known (`let`/`mut`, ascription, `return`,
/// `break`, and a function/method/closure body against its declared return type) —
/// never inside `unify()` itself, which stays a strict match everywhere else (call
/// arguments included).
///
/// Deliberately does **not** resolve `actual` through `ctx.solve()` first: `solve()` is
/// incremental and stateful (it advances `solved_constraint_count` and commits
/// `cached_subst`), so calling it eagerly at every annotated `let`/`return`/etc. across
/// a whole program — rather than only once, at the end, as before this rule existed —
/// changed constraint-processing order for unrelated code and broke an unrelated,
/// pre-existing test (a sized-array pattern arity mismatch started reporting a raw
/// unify failure, T0001, instead of the intended non-exhaustive-match diagnostic,
/// T0008). Matching on `actual` directly instead is sufficient for every real case:
/// `&expr`/`&mut expr` (`infer_unaryop`'s `Ref`/`RefMut` arms) produce `InferType::
/// Reference`/`MutReference` directly with no `Var` indirection, and reading an
/// existing reference-typed binding (`ctx.lookup`) returns its stored `InferType`
/// as-is, not a variable standing in for it.
///
/// `declared` being an unresolved `InferType::Var` means there is no real declared
/// type at this site (e.g. a function/closure with no return-type annotation, where
/// `ret_ty` is just a fresh var to be solved from the body) — that case must fall
/// through to plain unification so the body's own reference-ness flows out normally,
/// not be mistaken for "declared as a non-reference."
///
/// Returns `declared` only when read-copy actually fires; otherwise returns `actual`
/// unchanged, matching what every call site did before this rule existed. This isn't
/// cosmetic: binding a `let` to a freshly-reconstructed `declared` (from `ann_to_infer`)
/// instead of the value's own `actual` — even though the two are constrained equal —
/// swaps in a structurally-equal but not type-variable-identical `InferType`. That
/// broke an unrelated test (a sized-array pattern arity mismatch started reporting a
/// raw unify failure, T0001, instead of the intended non-exhaustive-match diagnostic,
/// T0008), caught only by running the full suite, not by reasoning about the rule
/// in isolation.
///
/// Peels *every* reference layer, not just one: RFC-0067a §3 guarantees auto-deref
/// chains through arbitrary depth (`&&T` derefs through both levels), and read-copy
/// is specified as the same auto-deref/copy story applied at a declared-type boundary
/// rather than a separate, shallower mechanism — `let x: i64 = rr;` where
/// `rr: &&i64` must copy through both layers, not stop after one and fail to unify
/// `&i64` against `i64`.
fn constrain_with_read_copy(
    ctx: &mut InferContext,
    actual: InferType,
    declared: InferType,
    span: Span,
) -> InferType {
    // Note the `Var(_)` arm here is deliberately left inspecting the *raw* `declared`.
    // Substituting it was tried and fixed nothing: where `declared` is still a variable
    // — the closure's own return type while its body's tail is being constrained — the
    // constraint that would resolve it has not been generated yet, so applying the
    // current substitution is a no-op. That is an ordering limitation, not a missing
    // `apply`, and it is out of scope here. See RFC-0112 §1.0.
    if matches!(
        declared,
        InferType::Reference(_) | InferType::MutReference(_) | InferType::Var(_)
    ) {
        ctx.add_constraint(actual.clone(), declared, span);
        return actual;
    }
    // Decide whether to peel against the *substituted* type, not the raw one. Without
    // this, the decision is made before the information needed to make it exists: a call
    // returning `&T` yields a fresh `InferType::Var` here, which matches no reference
    // pattern below, so the peel is silently skipped and the later unification of that
    // var against the declared referent type fails with T0001. `let n: i64 = g();` for
    // `fun g() -> &i64` failed where the equivalent `let n: i64 = r;` succeeded — a
    // distinction no user could predict.
    //
    // Same shape as `infer_match`'s scrutinee peel (RFC-0108) and `Expr::Call`'s
    // auto-deref, both of which already solve-and-apply before inspecting. A solve
    // failure here is not fatal: constraints can be transiently inconsistent mid-pass,
    // and the real error surfaces from the final solve, so fall back to the raw type
    // and let this call behave exactly as it did before.
    let resolved_actual = ctx
        .solve()
        .map_or_else(|_| actual.clone(), |subst| subst.apply(&actual));
    let mut peeled = resolved_actual;
    let mut any_peel = false;
    while let InferType::Reference(inner) | InferType::MutReference(inner) = peeled {
        peeled = *inner;
        any_peel = true;
    }
    if any_peel {
        ctx.add_constraint(peeled, declared.clone(), span);
        return declared;
    }
    // RFC-0078 §3.3: if `actual` is (plausibly) a singleton-coercible enum, bind
    // the environment to `declared` rather than the raw enum type — otherwise a
    // later use of this binding (e.g. `x + y` where `y`'s binding is still the raw
    // `Result<i64, !>`) would compare the wrong, uncoerced type. The constraint
    // recorded here still carries the raw `actual`; `InferContext::solve`'s
    // registry-aware retry (`apply_constraint_with_coercion`) is what actually
    // verifies (or rejects) the coercion once types are fully resolved — this is
    // only an optimistic environment-binding choice, not the enforcement point.
    if crate::typeinference::singleton_coerce_field_ty(ctx.registry(), &actual).is_some() {
        ctx.add_constraint(actual, declared.clone(), span);
        return declared;
    }
    // RFC-0166: a written function type `|T| -> U` is move-only. At a declared-type
    // boundary (`let` / `mut` / ascription / return) bind to the *written* type,
    // not the value's own — a function value the compiler proved copyable is
    // accepted into the slot by moving, and its copyability is neither carried by
    // the written type nor recovered downstream. The `add_constraint` still runs
    // the ordinary `unify` check (first-order Copy→Move is legal there), so this
    // only changes which of two constrained-equal types names the binding.
    if matches!(declared, InferType::Fun(..)) {
        ctx.add_constraint(actual, declared.clone(), span);
        return declared;
    }
    ctx.add_constraint(actual.clone(), declared, span);
    actual
}

fn is_same_declaring_module(
    current_module_path: &[String],
    declaring_module: Option<&Vec<String>>,
) -> bool {
    declaring_module.is_some_and(|module| module.as_slice() == current_module_path)
}

fn check_field_visibility(
    field: &FieldEntry,
    type_name: &str,
    current_module_path: &[String],
    declaring_module: Option<&Vec<String>>,
    container_visibility: Option<&Visibility>,
    span: &Span,
    action: &str,
) -> Result<(), MetelError> {
    if is_same_declaring_module(current_module_path, declaring_module) {
        return Ok(());
    }
    // RFC-0032 §7 / #776: a `public` field grant is conditional on the
    // enclosing type's own visibility, not an independent grant -- a public
    // field on a private struct must stay unreachable across a module
    // boundary even once a value of that type is obtained some other way
    // (e.g. via a public constructor function that never names the type).
    let container_is_private = container_visibility == Some(&Visibility::Private);
    if field.visibility == Visibility::Public && !container_is_private {
        return Ok(());
    }
    if container_is_private && field.visibility == Visibility::Public {
        return Err(MetelError::type_error(
            TypeErrorCode::T0009,
            format!(
                "visibility error: cannot {action} field `{}` of `{type_name}` from outside its declaring module: `{type_name}` itself is private, so its public field is not reachable",
                field.name
            ),
            span,
        ));
    }
    Err(MetelError::type_error(
        TypeErrorCode::T0009,
        format!("visibility error: cannot {action} private field `{}` of `{type_name}` from outside its declaring module", field.name),
        span,
    ))
}

fn infer_enum_variant_literal(
    enum_name: &str,
    variant_name: &str,
    fields: &[(String, Expr)],
    span: &Span,
    ctx: &mut InferContext,
    fun_generalizations: &mut Vec<FunGeneralization>,
) -> Result<InferType, MetelError> {
    let enum_decl_module = ctx
        .registry()
        .enum_declaring_module(ctx.current_module_path(), enum_name)
        .cloned();
    let enum_info = ctx
        .get_enum(enum_name)
        .ok_or_else(|| {
            MetelError::type_error(
                TypeErrorCode::T0003,
                format!("unknown enum `{enum_name}`"),
                span,
            )
        })?
        .clone();
    let variant = enum_info
        .variants
        .iter()
        .find(|v| v.name == variant_name)
        .ok_or_else(|| {
            MetelError::type_error(
                TypeErrorCode::T0003,
                format!("no variant `{variant_name}` on enum `{enum_name}`"),
                span,
            )
        })?
        .clone();
    let mut remap: HashMap<TypeVar, InferType> = HashMap::new();
    // #266: tag each fresh var with the declared generic parameter it stands
    // in for (e.g. `E<T>`'s `T`), so a diagnostic mentioning this value's type
    // can show `T` instead of an anonymous placeholder. `struct_generic_names_for`
    // covers enums too (registered under the enum's own name, same order as
    // `type_params`) — see `registry.rs`'s enum-registration path.
    let declared_names = ctx
        .struct_generic_names_for(enum_name)
        .cloned()
        .unwrap_or_default();
    for (i, &tp) in enum_info.type_params.iter().enumerate() {
        let fresh = ctx.fresh_var();
        if let InferType::Var(fresh_tv) = fresh {
            if let Some(name) = declared_names.get(i) {
                ctx.tag_declared_var_name(fresh_tv, name.clone());
            }
        }
        remap.insert(tp, fresh);
    }
    for (fname, expr) in fields {
        let field = variant
            .fields
            .iter()
            .find(|field| field.name == *fname)
            .ok_or_else(|| {
                MetelError::type_error(
                    TypeErrorCode::T0003,
                    format!("no field `{fname}` on `{enum_name}::{variant_name}`"),
                    span,
                )
            })?;
        check_field_visibility(
            field,
            &format!("{enum_name}::{variant_name}"),
            ctx.current_module_path(),
            enum_decl_module.as_ref(),
            None,
            span,
            "construct",
        )?;
        let decl_ty = match &field.ty {
            InferType::Var(v) => remap.get(v).cloned().unwrap_or_else(|| field.ty.clone()),
            other => other.clone(),
        };
        let expr_ty = infer_expr(expr, ctx, fun_generalizations)?;
        ctx.add_constraint(expr_ty, decl_ty, span.clone());
    }
    let type_args: Vec<InferType> = enum_info
        .type_params
        .iter()
        .map(|tp| remap[tp].clone())
        .collect();
    // metel-core#1137: same reasoning as `infer_struct_literal`'s matching fix
    // -- `enum_name` is written right here in this module's own source.
    let type_id = ctx
        .registry()
        .resolve_type_id(ctx.current_module_path(), enum_name);
    Ok(InferType::Named(
        enum_name.to_string(),
        type_args,
        crate::types::NominalId(type_id),
    ))
}

fn infer_struct_literal(
    struct_name: String,
    fields: &[(String, Expr)],
    span: &Span,
    ctx: &mut InferContext,
    fun_generalizations: &mut Vec<FunGeneralization>,
) -> Result<InferType, MetelError> {
    let struct_decl_module = ctx
        .registry()
        .struct_declaring_module(ctx.current_module_path(), &struct_name)
        .cloned();
    let expected_fields = ctx
        .get_struct_fields(&struct_name)
        .ok_or_else(|| {
            MetelError::type_error(
                TypeErrorCode::T0003,
                format!("unknown struct `{struct_name}`"),
                span,
            )
        })?
        .clone();
    // For generic structs, create fresh type vars and remap declared TypeVars.
    let type_params = ctx.get_struct_type_params(&struct_name).cloned();
    let mut remap: HashMap<TypeVar, InferType> = HashMap::new();
    if let Some(ref params) = type_params {
        // #266: tag each fresh var with the declared generic parameter it
        // stands in for (e.g. `Pair<A, B>`'s `A`), so a diagnostic mentioning
        // this value's type can show `A` instead of an anonymous placeholder.
        let declared_names = ctx
            .struct_generic_names_for(&struct_name)
            .cloned()
            .unwrap_or_default();
        for (i, &tp) in params.iter().enumerate() {
            let fresh = ctx.fresh_var();
            if let InferType::Var(fresh_tv) = fresh {
                if let Some(name) = declared_names.get(i) {
                    ctx.tag_declared_var_name(fresh_tv, name.clone());
                }
            }
            remap.insert(tp, fresh);
        }
    }
    let apply_remap = |ty: &InferType| -> InferType {
        if remap.is_empty() {
            return ty.clone();
        }
        match ty {
            InferType::Var(v) => remap.get(v).cloned().unwrap_or_else(|| ty.clone()),
            other => other.clone(),
        }
    };
    for (name, expr) in fields {
        let field = expected_fields
            .iter()
            .find(|field| field.name == *name)
            .ok_or_else(|| {
                MetelError::type_error(
                    TypeErrorCode::T0003,
                    format!("no field `{name}` on `{struct_name}`"),
                    span,
                )
            })?;
        check_field_visibility(
            field,
            &struct_name,
            ctx.current_module_path(),
            struct_decl_module.as_ref(),
            ctx.registry()
                .struct_visibility_for(ctx.current_module_path(), &struct_name),
            span,
            "construct",
        )?;
        let decl_ty = apply_remap(&field.ty);
        let expr_ty = infer_expr(expr, ctx, fun_generalizations)?;
        ctx.add_constraint(expr_ty, decl_ty, span.clone());
    }
    for field in &expected_fields {
        if !fields.iter().any(|(n, _)| n == &field.name) {
            return Err(MetelError::type_error(
                TypeErrorCode::T0003,
                format!("missing field `{}` in `{struct_name}`", field.name),
                span,
            ));
        }
    }
    let type_args: Vec<InferType> = type_params
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .map(|tp| remap[tp].clone())
        .collect();
    // metel-core#1137: `struct_name` is the literal spelling of a struct literal
    // written right here in this module's own source, always resolvable from
    // this module's own scope -- the same reasoning #1129 uses for a written
    // type annotation. Carrying this through is what lets a value later
    // constructed from this literal (including through a `-> extends Aspect`
    // opaque-return reveal) dispatch its methods by identity instead of by a
    // bare name that can collide across modules.
    let type_id = ctx
        .registry()
        .resolve_type_id(ctx.current_module_path(), &struct_name);
    Ok(InferType::Named(
        struct_name,
        type_args,
        crate::types::NominalId(type_id),
    ))
}

/// Walk an lvalue chain to the root identifier for mutability checking.
/// Returns `None` when the chain passes through a pointer dereference,
/// meaning write access is conferred by the pointer rather than the binding.
fn root_binding_for_write(expr: &Expr) -> Option<(&str, &Span)> {
    match expr {
        Expr::Ident(name, span) => Some((name.as_str(), span)),
        Expr::FieldAccess { object, .. }
        | Expr::TupleAccess { object, .. }
        | Expr::Index { object, .. } => root_binding_for_write(object),
        _ => None,
    }
}

fn infer_field_assign_type(
    object: &Expr,
    field: &str,
    target_span: &Span,
    ctx: &mut InferContext,
    fun_generalizations: &mut Vec<FunGeneralization>,
) -> Result<InferType, MetelError> {
    let obj_ty = infer_expr(object, ctx, fun_generalizations)?;
    let obj_ty = ctx.solve()?.apply(&obj_ty);
    // Auto-deref through &mut T: writing via a mutable reference doesn't require
    // the reference binding itself to be mutable — only the referent is being written.
    // This must also cover a *chain* rooted in a reference (`optr.inner.x = 42` where
    // `optr: &mut Outer`): `obj_ty` here is `optr.inner`'s own type (`Point`), which no
    // longer shows any reference at all — auto-deref already stripped it one level up.
    // So the check isn't just "is `obj_ty` itself a reference," it's "is the write
    // access for this whole chain conferred by a reference anywhere along it" — which
    // reduces to asking whether the chain's *root* binding is reference-typed, since a
    // reference confers write access to everything reachable through it regardless of
    // projection depth.
    let is_through_mut_ptr = matches!(&obj_ty, InferType::MutReference(_))
        || matches!(
            root_binding_for_write(object).and_then(|(name, _)| ctx.lookup_mono_raw(name)),
            Some(InferType::MutReference(_))
        );
    if !is_through_mut_ptr {
        if let Some((name, span)) = root_binding_for_write(object) {
            let _ = ctx.lookup_for_write(name, span)?;
        }
    }
    let peeled = peel_all_references(&obj_ty);
    if let InferType::Record(fields) = &peeled {
        return fields
            .iter()
            .find(|(name, _)| name == field)
            .map(|(_, ty)| ty.clone())
            .ok_or_else(|| {
                MetelError::type_error(
                    TypeErrorCode::T0003,
                    format!("no field `{field}` on {peeled}"),
                    target_span,
                )
            });
    }
    // Mirror of Expr::FieldAccess's row-bound branch above, so `p.x = value` works
    // symmetrically wherever `p.x` does. `fresh_row_field_var` is memoized by
    // (tv, field), so an untyped field's read and write sides agree on a type.
    if let InferType::Var(tv) = &peeled {
        if let Some(result) = resolve_row_bound_field(ctx, *tv, field, target_span) {
            return result;
        }
    }
    // RFC-0137 slice 2 (metel-core#858): assigning a field to a narrowed residual
    // is a *widening* write — the field may be one currently absent from the
    // residual's row, so it is resolved against the brand's full declared row.
    // `Expr::Assign` calls `note_reassigned_infer` right after this to widen the
    // binding's type back.
    if let InferType::Residual { brand, .. } = &peeled {
        if let Some(entry) = ctx
            .get_struct_fields(brand)
            .and_then(|fields| fields.iter().find(|e| e.name == field).cloned())
        {
            return Ok(entry.ty);
        }
        return Err(MetelError::type_error(
            TypeErrorCode::T0003,
            format!("no field `{field}` on `{brand}`"),
            target_span,
        ));
    }
    let struct_name = named_type_name(&obj_ty).ok_or_else(|| {
        MetelError::type_error(
            TypeErrorCode::T0002,
            "cannot infer struct type for field assignment; add a type annotation",
            target_span,
        )
    })?;
    let type_args = match &obj_ty {
        InferType::Named(_, args, ..) => args.clone(),
        InferType::Reference(inner) | InferType::MutReference(inner) => match inner.as_ref() {
            InferType::Named(_, args, ..) => args.clone(),
            _ => vec![],
        },
        _ => vec![],
    };
    let fields = ctx
        .get_struct_fields(&struct_name)
        .ok_or_else(|| {
            MetelError::type_error(
                TypeErrorCode::T0003,
                format!("unknown type `{struct_name}`"),
                target_span,
            )
        })?
        .clone();
    let field_entry = fields
        .iter()
        .find(|entry| entry.name == field)
        .ok_or_else(|| {
            MetelError::type_error(
                TypeErrorCode::T0003,
                format!("no field `{field}` on `{struct_name}`"),
                target_span,
            )
        })?;
    check_field_visibility(
        field_entry,
        &struct_name,
        ctx.current_module_path(),
        ctx.registry()
            .struct_declaring_module(ctx.current_module_path(), &struct_name),
        ctx.registry()
            .struct_visibility_for(ctx.current_module_path(), &struct_name),
        target_span,
        "assign to",
    )?;
    let raw_ty = field_entry.ty.clone();
    if let Some(type_params) = ctx.get_struct_type_params(&struct_name).cloned() {
        let mut remap = Substitution::new();
        for (&tp, arg) in type_params.iter().zip(type_args.iter()) {
            remap.bind(tp, arg.clone());
        }
        Ok(remap.apply(&raw_ty))
    } else {
        Ok(raw_ty)
    }
}

fn infer_tuple_assign_type(
    object: &Expr,
    index: usize,
    target_span: &Span,
    ctx: &mut InferContext,
    fun_generalizations: &mut Vec<FunGeneralization>,
) -> Result<InferType, MetelError> {
    let obj_ty = infer_expr(object, ctx, fun_generalizations)?;
    let obj_ty = ctx.solve()?.apply(&obj_ty);
    let is_through_mut_ptr = matches!(&obj_ty, InferType::MutReference(_))
        || matches!(
            root_binding_for_write(object).and_then(|(name, _)| ctx.lookup_mono_raw(name)),
            Some(InferType::MutReference(_))
        );
    if !is_through_mut_ptr {
        if let Some((name, span)) = root_binding_for_write(object) {
            let _ = ctx.lookup_for_write(name, span)?;
        }
    }
    // Reach through a reference at the root, the way field- and index-path assignment
    // already do (`s.x = v` and `xs[0] = v` both work for a `&var` receiver). Peeled
    // *after* the `is_through_mut_ptr` check above, which needs the unpeeled shape.
    match peel_all_references(&obj_ty) {
        InferType::Tuple(elems) => elems.get(index).cloned().ok_or_else(|| {
            MetelError::type_error(
                TypeErrorCode::T0003,
                format!(
                    "tuple index {index} out of bounds (tuple has {} elements)",
                    elems.len()
                ),
                target_span,
            )
        }),
        _ => Err(MetelError::type_error(
            TypeErrorCode::T0002,
            "cannot infer tuple type for assignment; add a type annotation",
            target_span,
        )),
    }
}

fn infer_enum_variant_pattern(
    enum_name: &str,
    variant_name: &str,
    fields: &[String],
    scrutinee_ty: &InferType,
    pat_span: &Span,
    ctx: &mut InferContext,
) -> Result<(), MetelError> {
    let enum_decl_module = ctx
        .registry()
        .enum_declaring_module(ctx.current_module_path(), enum_name)
        .cloned();
    let enum_info = ctx
        .get_enum(enum_name)
        .ok_or_else(|| {
            MetelError::type_error(
                TypeErrorCode::T0003,
                format!("unknown enum `{enum_name}` in pattern"),
                pat_span,
            )
        })?
        .clone();
    let variant = enum_info
        .variants
        .iter()
        .find(|v| v.name == variant_name)
        .ok_or_else(|| {
            MetelError::type_error(
                TypeErrorCode::T0003,
                format!("no variant `{variant_name}` on `{enum_name}`"),
                pat_span,
            )
        })?
        .clone();
    let mut remap: HashMap<TypeVar, InferType> = HashMap::new();
    for &tp in &enum_info.type_params {
        remap.insert(tp, ctx.fresh_var());
    }
    let type_args: Vec<InferType> = enum_info
        .type_params
        .iter()
        .map(|tp| remap[tp].clone())
        .collect();
    ctx.add_constraint(
        scrutinee_ty.clone(),
        InferType::Named(
            enum_name.to_string(),
            type_args,
            crate::types::NominalId::NONE,
        ),
        pat_span.clone(),
    );
    for field_name in fields {
        let field = variant
            .fields
            .iter()
            .find(|field| field.name == *field_name)
            .ok_or_else(|| {
                MetelError::type_error(
                    TypeErrorCode::T0003,
                    format!("no field `{field_name}` on `{enum_name}::{variant_name}`"),
                    pat_span,
                )
            })?;
        check_field_visibility(
            field,
            &format!("{enum_name}::{variant_name}"),
            ctx.current_module_path(),
            enum_decl_module.as_ref(),
            None,
            pat_span,
            "pattern-match on",
        )?;
        let field_ty = match &field.ty {
            InferType::Var(v) => remap.get(v).cloned().unwrap_or_else(|| field.ty.clone()),
            other => other.clone(),
        };
        ctx.bind_mono(field_name, field_ty, false);
    }
    Ok(())
}

/// RFC-0032 §4/§5, RFC-0034 §5: a named-struct pattern (`Point { x, y }`,
/// `Token { kind, span, .. }`), already rewritten from a one-segment `EnumVariant`
/// by `resolve_struct_pattern` -- this is the struct counterpart of
/// `infer_enum_variant_pattern` above, same field-visibility check included, plus
/// the exhaustiveness requirement enum-variant patterns don't have: a struct
/// pattern must name every field unless it ends in `..` (RFC-0032 §5).
fn infer_struct_pattern(
    struct_name: &str,
    fields: &[String],
    rest: bool,
    scrutinee_ty: &InferType,
    pat_span: &Span,
    ctx: &mut InferContext,
) -> Result<(), MetelError> {
    let struct_decl_module = ctx
        .registry()
        .struct_declaring_module(ctx.current_module_path(), struct_name)
        .cloned();
    let struct_fields = ctx
        .get_struct_fields(struct_name)
        .ok_or_else(|| {
            MetelError::type_error(
                TypeErrorCode::T0003,
                format!("unknown struct `{struct_name}` in pattern"),
                pat_span,
            )
        })?
        .clone();
    let type_params = ctx
        .get_struct_type_params(struct_name)
        .cloned()
        .unwrap_or_default();
    let mut remap: HashMap<TypeVar, InferType> = HashMap::new();
    for &tp in &type_params {
        remap.insert(tp, ctx.fresh_var());
    }
    let type_args: Vec<InferType> = type_params.iter().map(|tp| remap[tp].clone()).collect();
    ctx.add_constraint(
        scrutinee_ty.clone(),
        InferType::Named(
            struct_name.to_string(),
            type_args,
            crate::types::NominalId::NONE,
        ),
        pat_span.clone(),
    );
    for field_name in fields {
        let field = struct_fields
            .iter()
            .find(|f| f.name == *field_name)
            .ok_or_else(|| {
                MetelError::type_error(
                    TypeErrorCode::T0003,
                    format!("no field `{field_name}` on `{struct_name}`"),
                    pat_span,
                )
            })?;
        check_field_visibility(
            field,
            struct_name,
            ctx.current_module_path(),
            struct_decl_module.as_ref(),
            ctx.registry()
                .struct_visibility_for(ctx.current_module_path(), struct_name),
            pat_span,
            "pattern-match on",
        )?;
        let field_ty = match &field.ty {
            InferType::Var(v) => remap.get(v).cloned().unwrap_or_else(|| field.ty.clone()),
            other => other.clone(),
        };
        ctx.bind_mono(field_name, field_ty, false);
    }
    if !rest && fields.len() != struct_fields.len() {
        let missing: Vec<&str> = struct_fields
            .iter()
            .map(|f| f.name.as_str())
            .filter(|name| !fields.iter().any(|f| f == name))
            .collect();
        return Err(MetelError::type_error(
            TypeErrorCode::T0001,
            format!(
                "pattern for `{struct_name}` does not name field(s) {} -- name them or add `..`",
                missing.join(", ")
            ),
            pat_span,
        ));
    }
    Ok(())
}

// ── Helpers for From/Iterable dispatch ───────────────────────────────────────

/// Extract a concrete `Type` from an `InferType` for use in From-impl lookups.
fn infer_to_type_for_from(ty: &InferType) -> Option<Type> {
    match ty {
        InferType::Concrete(t) => Some(t.clone()),
        InferType::Named(name, ..) => Some(Type::Named(
            name.clone(),
            vec![],
            crate::types::NominalId::NONE,
        )),
        _ => None,
    }
}

/// Extract the type name string from an `InferType` for registry lookups.
fn infer_type_name(ty: &InferType) -> Option<&str> {
    match ty {
        InferType::Concrete(Type::I64) => Some("i64"),
        InferType::Concrete(Type::F64) => Some("f64"),
        InferType::Concrete(Type::Boolean) => Some("boolean"),
        InferType::Concrete(Type::Char) => Some("Char"),
        InferType::Concrete(Type::Str) => Some("String"),
        InferType::Concrete(Type::I8) => Some("i8"),
        InferType::Concrete(Type::I16) => Some("i16"),
        InferType::Concrete(Type::I32) => Some("i32"),
        InferType::Concrete(Type::U8) => Some("u8"),
        InferType::Concrete(Type::U16) => Some("u16"),
        InferType::Concrete(Type::U32) => Some("u32"),
        InferType::Concrete(Type::U64) => Some("u64"),
        InferType::Concrete(Type::F32) => Some("f32"),
        InferType::Named(name, ..) => Some(name.as_str()),
        _ => None,
    }
}

// ── impl Aspect lowering pass ─────────────────────────────────────────────────

/// Lower `impl Aspect` type expressions in function parameter positions to fresh
/// anonymous generic type parameters before inference runs. This pass rewrites
/// the `FunDecl` AST in-place (via a returned owned copy).
///
/// `fun foo(x: impl Display)` becomes `fun foo<_T0: Display>(x: _T0)`.
///
/// Each `impl Aspect` occurrence generates a fresh, independent type parameter.
/// The source spelling ("impl Display") is stored in the param name as a hint
/// for error messages (the typechecker uses GenericParam.bounds for enforcement).
mod lowering;

pub(super) use lowering::{lower_impl_aspects_in_program, lower_projections_in_program};
