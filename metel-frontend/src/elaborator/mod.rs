/// The elaboration pass: walks the typed AST and resolves `MethodDispatch` for every
/// `TypedExpr::MethodCall`. After elaboration the caller holds an `ElaboratedModuleGraph`,
/// a proof that this pass has run.
///
/// For the tree-walk interpreter, elaboration pre-resolves whether each method call goes
/// through an aspect (and which one) or is a direct inherent call, so the evaluator can
/// skip the runtime aspect-registry lookup for statically-known sites.
use std::collections::HashMap;

use crate::ast::TypeExpr;
use crate::error::{MetelError, TypeErrorCode};
use crate::name_resolver::ResolvedNames;
use crate::symbols::SymbolId;
use crate::typed_ast::{
    FunBody, MethodDispatch, TypedBlock, TypedDecl, TypedExpr, TypedForInit, TypedImplBlock,
    TypedMatchArm, TypedMatchExpr, TypedModuleGraph, TypedPlace, TypedStmt,
};
use crate::types::Type;

/// Proof that the elaboration pass has run over a `TypedModuleGraph`.
///
/// ## Environment responsibilities after elaboration
///
/// | Artifact | Owner | Responsibility |
/// |---|---|---|
/// | `TypeDefinitionRegistry` | `TypedModuleGraph::type_registry` | Type/aspect/method definitions; the elaboration-facing `aspect_declaring_module` lookup |
/// | `ResolvedNames::symbols` | Caller-supplied to `elaborate` | Stable `SymbolId` intern table; elaboration reads but does not write it |
/// | `MethodDispatch` per call site | `TypedExpr::MethodCall::dispatch` | Resolved during elaboration; evaluator reads, does not re-derive |
/// | `TypedImplBlock::aspect_id` | `TypedImplBlock` | Set during typechecker construction pass (Pass 2) using the same symbol table |
///
/// After `elaborate` returns, `MethodDispatch::Dynamic` sites are those whose receiver type
/// had no aspect-method registration in the registry (e.g. calls on `fn` or tuple types).
/// All others are `Inherent` or `Aspect { aspect_id }`.
pub struct ElaboratedModuleGraph(pub TypedModuleGraph);

/// Run elaboration over `graph` and return an `ElaboratedModuleGraph`.
///
/// Each `MethodCall::dispatch` field starts as `Dynamic`; this pass upgrades it to
/// `Aspect { aspect_id }` or `Inherent` where the target can be statically determined.
///
/// # Errors
/// Returns an error if two different aspects provide the same method name for the
/// same type, making dispatch ambiguous (T0013).
pub fn elaborate(
    mut graph: TypedModuleGraph,
    names: &ResolvedNames,
) -> Result<ElaboratedModuleGraph, MetelError> {
    let methods = build_aspect_method_map(&graph, names)?;
    let aspect_ids = build_aspect_id_map(&graph, names);

    // Disjoint field borrows: `type_registry` is read-only for the whole walk while
    // `modules` is mutated. Splitting the struct into locals lets the borrow checker
    // see they don't overlap.
    let TypedModuleGraph {
        modules,
        type_registry,
        ..
    } = &mut graph;
    let dispatch_map = DispatchMap {
        methods,
        aspect_ids,
        registry: type_registry,
    };
    for module in modules.iter_mut() {
        let current_module = module.module_path.clone();
        let cx = ElabCtx {
            map: &dispatch_map,
            current_module: &current_module,
        };
        for decl in &mut module.decls {
            elaborate_decl(decl, &cx);
        }
    }

    Ok(ElaboratedModuleGraph(graph))
}

/// Maps `(declaring_module, aspect_name) → SymbolId` — used by `dyn Aspect`
/// method-call dispatch (RFC-0008 slice 2). Keyed by the *declaring* module, not the
/// bare name, so two same-named aspects from different modules don't collide
/// (metel-core#989); the dyn arm resolves the bare name to its declaring module first.
fn build_aspect_id_map(
    graph: &TypedModuleGraph,
    names: &ResolvedNames,
) -> HashMap<(Vec<String>, String), SymbolId> {
    let mut map = HashMap::new();
    for module in &graph.modules {
        for decl in &module.decls {
            if let TypedDecl::Aspect(a) = decl {
                if let Some(&id) = names
                    .symbols
                    .get(&(module.module_path.clone(), a.name.clone()))
                {
                    map.insert((module.module_path.clone(), a.name.clone()), id);
                }
            }
        }
    }
    map
}

// ── Dispatch map ─────────────────────────────────────────────────────────────

/// Maps `(concrete_type_name, method_name)` → `SymbolId` of the aspect that owns
/// that method for that type. Keying by receiver type avoids false matches when two
/// unrelated aspects from different modules both declare a method with the same name.
///
/// If two distinct aspects define the same method name on the same receiver type,
/// elaboration rejects the program with T0013 rather than silently picking one.
fn build_aspect_method_map(
    graph: &TypedModuleGraph,
    names: &ResolvedNames,
) -> Result<HashMap<(String, String), AspectDispatchOwner>, MetelError> {
    let mut map: HashMap<(String, String), AspectDispatchOwner> = HashMap::new();
    let registry = &graph.type_registry;

    for module in &graph.modules {
        for decl in &module.decls {
            if let TypedDecl::Impl(block) = decl {
                let Some(aspect_name) = &block.aspect_name else {
                    continue;
                };
                let Some(type_name) = type_expr_outer_name(&block.target_type) else {
                    continue;
                };
                // Resolve the aspect's SymbolId via its declaring module, scoped to the
                // module this impl block lives in so two same-named aspects from
                // different modules don't collide (metel-core#989).
                let Some(declaring_module) =
                    registry.aspect_declaring_module_in(&module.module_path, aspect_name)
                else {
                    continue;
                };
                let Some(&id) = names
                    .symbols
                    .get(&(declaring_module.clone(), aspect_name.clone()))
                else {
                    continue;
                };
                let Some(declared_methods) =
                    registry.aspect_method_defs_in(&module.module_path, aspect_name)
                else {
                    continue;
                };
                let is_generic = !block.generics.is_empty();
                for method in block.methods.iter().filter(|method| {
                    declared_methods
                        .iter()
                        .any(|declared| declared.name == method.name)
                }) {
                    let key = (type_name.clone(), method.name.clone());
                    let owner = AspectDispatchOwner {
                        aspect_id: id,
                        aspect_name: aspect_name.clone(),
                        is_generic,
                    };
                    if let Some(existing_owner) = map.get(&key) {
                        if existing_owner.aspect_id != id {
                            // A conditional/generic impl on either side of this pair
                            // was already vetted by `coherence::check`, which runs
                            // earlier in the pipeline and -- unlike this map, a plain
                            // "same (type, method) seen twice" check with no bound
                            // awareness -- actually knows whether the two impls'
                            // bounds can overlap (issue #272). Any such pair that
                            // reached construction/elaboration at all is therefore
                            // already proven non-overlapping; only a pair of
                            // concrete, unconditional impls (which have no bounds to
                            // ever be disjoint on, so always genuinely conflict) is
                            // still an error here.
                            if !is_generic && !existing_owner.is_generic {
                                return Err(MetelError::type_error(
                                    TypeErrorCode::T0013,
                                    format!(
                                        "ambiguous aspect method `{}` on type `{}`: both `{}` and `{}` provide this method; use distinct method names or remove one impl",
                                        method.name,
                                        type_name,
                                        aspect_name,
                                        existing_owner.aspect_name,
                                    ),
                                    &method.span,
                                ));
                            }
                        }
                    } else {
                        map.insert(key, owner);
                    }
                }
            }
        }
    }

    Ok(map)
}

/// Extract the outermost named type from a `TypeExpr` — the part used as the registry key.
/// `List<i32>` → `"List"`, `Foo` → `"Foo"`, everything else → `None`.
fn type_expr_outer_name(te: &TypeExpr) -> Option<String> {
    match te {
        TypeExpr::Named(name, _) => Some(name.clone()),
        _ => None,
    }
}

/// Peel every `&`/`&var` layer off `ty`. Used before checking for `Type::Dyn`
/// specifically — `receiver_type_name` peels internally too, but that check
/// runs *before* it, so it needs its own peel to see through `&dyn Aspect`/
/// `&var dyn Aspect` (RFC-0008 §1).
fn peel_reference(ty: &Type) -> &Type {
    match ty {
        Type::Reference(inner) | Type::MutReference(inner) => peel_reference(inner),
        other => other,
    }
}

/// Map a resolved `Type` to the string used in the runtime registry.
/// Mirrors `runtime_type_name` in the evaluator.  Returns `None` for types
/// (arrays, tuples, fn pointers) that don't have a named registry entry.
fn receiver_type_name(ty: &Type) -> Option<String> {
    match ty {
        Type::Named(name, _) => Some(name.clone()),
        Type::Boolean => Some("boolean".to_string()),
        Type::Str => Some("String".to_string()),
        Type::Char => Some("Char".to_string()),
        Type::I8 => Some("i8".to_string()),
        Type::I16 => Some("i16".to_string()),
        Type::I32 => Some("i32".to_string()),
        Type::I64 => Some("i64".to_string()),
        Type::U8 => Some("u8".to_string()),
        Type::U16 => Some("u16".to_string()),
        Type::U32 => Some("u32".to_string()),
        Type::U64 => Some("u64".to_string()),
        Type::F32 => Some("f32".to_string()),
        Type::F64 => Some("f64".to_string()),
        // References: dispatch through the referent type (deref_value unwraps them at runtime).
        Type::Reference(inner) | Type::MutReference(inner) => receiver_type_name(inner),
        _ => None,
    }
}

// ── Recursive elaboration ─────────────────────────────────────────────────────

#[derive(Clone)]
struct AspectDispatchOwner {
    aspect_id: SymbolId,
    aspect_name: String,
    /// Whether the impl that registered this owner has its own generics
    /// (RFC-0036 conditional impl). See the comment at the conflict check
    /// below for why this changes whether a same-method-name collision is an
    /// error here.
    is_generic: bool,
}

struct DispatchMap<'a> {
    /// `(concrete_type_name, method_name) → owning aspect`, for ordinary
    /// per-concrete-type dispatch.
    methods: HashMap<(String, String), AspectDispatchOwner>,
    /// `(declaring_module, aspect_name) → SymbolId`, for `dyn Aspect` dispatch
    /// (RFC-0008 slice 2) — aspect-based by construction, so it never consults
    /// `methods`. Keyed by declaring module so same-named aspects don't collide
    /// (metel-core#989).
    aspect_ids: HashMap<(Vec<String>, String), SymbolId>,
    /// Read-only, for resolving a `dyn Aspect`'s bare name to its declaring module
    /// in the scope of the module the call appears in.
    registry: &'a crate::typeinference::TypeDefinitionRegistry,
}

/// The walk's per-module context: the shared dispatch map plus which module's scope a
/// bare `dyn Aspect` name should resolve in.
struct ElabCtx<'a> {
    map: &'a DispatchMap<'a>,
    current_module: &'a [String],
}

fn elaborate_decl(decl: &mut TypedDecl, cx: &ElabCtx<'_>) {
    match decl {
        TypedDecl::Fun(f) => elaborate_fun_body(&mut f.body, cx),
        TypedDecl::Let(l) => elaborate_expr(&mut l.value, cx),
        TypedDecl::Mut(m) => elaborate_expr(&mut m.value, cx),
        TypedDecl::Impl(block) => elaborate_impl_block(block, cx),
        // Struct / Enum / Aspect carry no executable bodies.
        TypedDecl::Struct(_) | TypedDecl::Enum(_) | TypedDecl::Aspect(_) => {}
        TypedDecl::Stmt(stmt) => elaborate_stmt(stmt, cx),
    }
}

fn elaborate_fun_body(body: &mut FunBody, cx: &ElabCtx<'_>) {
    if let FunBody::Typed(block) = body {
        elaborate_block(block, cx);
    }
    // FunBody::Generic bodies are re-evaluated at call sites; skip here.
}

fn elaborate_impl_block(block: &mut TypedImplBlock, cx: &ElabCtx<'_>) {
    for method in &mut block.methods {
        elaborate_fun_body(&mut method.body, cx);
    }
}

fn elaborate_block(block: &mut TypedBlock, cx: &ElabCtx<'_>) {
    for decl in &mut block.stmts {
        elaborate_decl(decl, cx);
    }
    if let Some(tail) = &mut block.tail {
        elaborate_expr(tail, cx);
    }
}

fn elaborate_stmt(stmt: &mut TypedStmt, cx: &ElabCtx<'_>) {
    match stmt {
        TypedStmt::Expr(e) => elaborate_expr(e, cx),
        TypedStmt::While(w) => {
            elaborate_expr(&mut w.condition, cx);
            elaborate_block(&mut w.body, cx);
        }
        TypedStmt::For(f) => {
            if let Some(init) = &mut f.init {
                match init {
                    TypedForInit::Let(l) => elaborate_expr(&mut l.value, cx),
                    TypedForInit::Mut(m) => elaborate_expr(&mut m.value, cx),
                    TypedForInit::Expr(e) => elaborate_expr(e, cx),
                }
            }
            if let Some(cond) = &mut f.condition {
                elaborate_expr(cond, cx);
            }
            if let Some(step) = &mut f.step {
                elaborate_expr(step, cx);
            }
            elaborate_block(&mut f.body, cx);
        }
        TypedStmt::ForIn(fi) => {
            elaborate_expr(&mut fi.iterable, cx);
            elaborate_block(&mut fi.body, cx);
        }
    }
}

fn elaborate_place(place: &mut TypedPlace, cx: &ElabCtx<'_>) {
    match place {
        TypedPlace::Ident(..) => {}
        TypedPlace::Deref { object, .. } => elaborate_expr(object, cx),
        TypedPlace::Field { object, .. } | TypedPlace::Tuple { object, .. } => {
            elaborate_place(object, cx);
        }
        TypedPlace::Index { object, index, .. } => {
            elaborate_place(object, cx);
            elaborate_expr(index, cx);
        }
    }
}

fn elaborate_expr(expr: &mut TypedExpr, cx: &ElabCtx<'_>) {
    match expr {
        TypedExpr::MethodCall {
            method,
            dispatch,
            receiver,
            args,
            ..
        } => {
            if *dispatch == MethodDispatch::Dynamic {
                *dispatch = match peel_reference(receiver.ty()) {
                    // `dyn Aspect` dispatch is aspect-based by construction — the
                    // aspect is already known statically from the receiver's own
                    // type (peeled through `&`/`&var`, RFC-0008 §1's borrowed
                    // forms), so this bypasses the per-concrete-type `methods`
                    // map entirely (RFC-0008 slice 2; the concrete type behind
                    // the fat pointer isn't known until the receiver value
                    // exists at runtime, so there's nothing here to look up by
                    // type name).
                    Type::Dyn { aspect, .. } => resolve_dyn_dispatch(cx, aspect),
                    ty => {
                        let recv_type = receiver_type_name(ty);
                        resolve_dispatch(recv_type.as_deref(), method, &cx.map.methods)
                    }
                };
            }
            elaborate_expr(receiver, cx);
            for arg in args.iter_mut() {
                elaborate_expr(arg, cx);
            }
        }
        TypedExpr::Call { callee, args, .. } => {
            elaborate_expr(callee, cx);
            for arg in args.iter_mut() {
                elaborate_expr(arg, cx);
            }
        }
        TypedExpr::BinOp(lhs, _, rhs, ..) => {
            elaborate_expr(lhs, cx);
            elaborate_expr(rhs, cx);
        }
        TypedExpr::UnaryOp(_, operand, ..) => elaborate_expr(operand, cx),
        TypedExpr::RefTemp { init, .. } => elaborate_expr(init, cx),
        TypedExpr::Tuple(elems, ..) | TypedExpr::Array(elems, ..) => {
            for e in elems.iter_mut() {
                elaborate_expr(e, cx);
            }
        }
        TypedExpr::RepeatArray(elem, ..) => elaborate_expr(elem, cx),
        TypedExpr::Assign { target, value, .. } => {
            elaborate_place(target, cx);
            elaborate_expr(value, cx);
        }
        TypedExpr::FieldAccess { object, .. } | TypedExpr::TupleAccess { object, .. } => {
            elaborate_expr(object, cx);
        }
        TypedExpr::Index { object, index, .. } => {
            elaborate_expr(object, cx);
            elaborate_expr(index, cx);
        }
        TypedExpr::Cast { expr: inner, .. }
        | TypedExpr::SingletonCoerce { inner, .. }
        | TypedExpr::DynCoerce { inner, .. } => {
            elaborate_expr(inner, cx);
        }
        TypedExpr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            elaborate_expr(condition, cx);
            elaborate_block(then_branch, cx);
            if let Some(b) = else_branch {
                elaborate_block(b, cx);
            }
        }
        TypedExpr::Loop { body, .. } | TypedExpr::Closure { body, .. } => {
            elaborate_block(body, cx);
        }
        TypedExpr::Match(m) => elaborate_match(m, cx),
        TypedExpr::StructLiteral { fields, .. } | TypedExpr::RecordLiteral { fields, .. } => {
            for (_, e) in fields.iter_mut() {
                elaborate_expr(e, cx);
            }
        }
        TypedExpr::Return(r) => {
            if let Some(v) = &mut r.value {
                elaborate_expr(v, cx);
            }
        }
        TypedExpr::Break(b) => {
            if let Some(v) = &mut b.value {
                elaborate_expr(v, cx);
            }
        }
        TypedExpr::GenericClosure { .. }
        | TypedExpr::Continue(_)
        | TypedExpr::Literal(..)
        | TypedExpr::Ident(..)
        | TypedExpr::Path { .. } => {}
    }
}

fn elaborate_match(m: &mut TypedMatchExpr, cx: &ElabCtx<'_>) {
    elaborate_expr(&mut m.scrutinee, cx);
    for arm in &mut m.arms {
        elaborate_match_arm(arm, cx);
    }
}

fn elaborate_match_arm(arm: &mut TypedMatchArm, cx: &ElabCtx<'_>) {
    if let Some(guard) = &mut arm.guard {
        elaborate_expr(guard, cx);
    }
    elaborate_block(&mut arm.body, cx);
}

/// Resolve a `dyn Aspect` method call's dispatch (metel-core#989): the bare aspect name
/// on `Type::Dyn` is resolved to its declaring module in the scope of the module the call
/// appears in, then to that aspect's `SymbolId`. `Inherent` when it doesn't resolve —
/// same fallback as before this was module-aware.
fn resolve_dyn_dispatch(cx: &ElabCtx<'_>, aspect: &str) -> MethodDispatch {
    cx.map
        .registry
        .aspect_declaring_module_in(cx.current_module, aspect)
        .and_then(|declaring_module| {
            cx.map
                .aspect_ids
                .get(&(declaring_module.clone(), aspect.to_string()))
        })
        .map_or(MethodDispatch::Inherent, |&aspect_id| {
            MethodDispatch::Aspect { aspect_id }
        })
}

/// Resolve dispatch for a single call site.
/// `recv_type` is `None` when the receiver has no nameable type (array, tuple, fn);
/// those calls are always `Inherent` since aspects only apply to named types.
fn resolve_dispatch(
    recv_type: Option<&str>,
    method: &str,
    map: &HashMap<(String, String), AspectDispatchOwner>,
) -> MethodDispatch {
    let Some(type_name) = recv_type else {
        return MethodDispatch::Inherent;
    };
    match map.get(&(type_name.to_string(), method.to_string())) {
        Some(owner) => MethodDispatch::Aspect {
            aspect_id: owner.aspect_id,
        },
        None => MethodDispatch::Inherent,
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbols::SYM_ASPECT_DISPLAY;

    fn display_owner() -> AspectDispatchOwner {
        AspectDispatchOwner {
            aspect_id: SYM_ASPECT_DISPLAY,
            aspect_name: "Display".to_string(),
            is_generic: false,
        }
    }

    #[test]
    fn resolve_dispatch_aspect_returns_aspect_variant() {
        let mut map = HashMap::new();
        map.insert(
            ("Foo".to_string(), "to_string".to_string()),
            display_owner(),
        );
        assert_eq!(
            resolve_dispatch(Some("Foo"), "to_string", &map),
            MethodDispatch::Aspect {
                aspect_id: SYM_ASPECT_DISPLAY
            }
        );
    }

    #[test]
    fn resolve_dispatch_wrong_type_returns_inherent() {
        let mut map = HashMap::new();
        map.insert(
            ("Foo".to_string(), "to_string".to_string()),
            display_owner(),
        );
        // Same method name but different receiver type → Inherent, not an aspect call.
        assert_eq!(
            resolve_dispatch(Some("Bar"), "to_string", &map),
            MethodDispatch::Inherent
        );
    }

    #[test]
    fn resolve_dispatch_no_type_returns_inherent() {
        let mut map = HashMap::new();
        map.insert(
            ("Foo".to_string(), "to_string".to_string()),
            display_owner(),
        );
        assert_eq!(
            resolve_dispatch(None, "to_string", &map),
            MethodDispatch::Inherent
        );
    }

    #[test]
    fn resolve_dispatch_unknown_method_returns_inherent() {
        let map = HashMap::new();
        assert_eq!(
            resolve_dispatch(Some("Foo"), "len", &map),
            MethodDispatch::Inherent
        );
    }

    #[test]
    fn resolve_dispatch_non_aspect_method_returns_inherent() {
        let mut map = HashMap::new();
        map.insert(
            ("Foo".to_string(), "to_string".to_string()),
            display_owner(),
        );
        assert_eq!(
            resolve_dispatch(Some("Foo"), "push", &map),
            MethodDispatch::Inherent
        );
    }
}
