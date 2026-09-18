//! Aspect implementation coherence: the orphan rule (`T0014`) and overlap
//! detection (`T0015`) for concrete impls (RFC-0060, issue #238).
//!
//! Runs after path normalization, before type-checking. It only needs to
//! resolve type and aspect *names* to their declaring module — exactly what
//! `ResolvedNames` already provides — so it works directly over each
//! module's `Decl::Impl` blocks rather than needing inferred types.
//!
//! Scope (ADR-0042 + RFC-0036): concrete impls AND conditional/blanket impls
//! with generic parameters are checked. `CanonicalType::TypeParam` represents
//! impl-scoped type variables during overlap detection. §3.1 (negation
//! disjointness) and §3.2 (unconditional vs. conditional conflict) are
//! handled via `provably_disjoint` checks on `scoped_type_param_bounds`.

use std::collections::HashMap;

use crate::ast::{Decl, ImplBlock, Polarity, Span, TypeExpr, WhereClause};
use crate::error::{MetelError, TypeErrorCode};
use crate::name_resolver::{GlobTier, ResolvedNames};
use crate::path_normalizer::NormalizedModuleGraph;
use crate::symbols::SymbolId;
use crate::typeinference::GenericBound;

/// Resolve a bare type- or aspect-position name to its declaring `SymbolId`,
/// from the perspective of `current_module`. Mirrors the precedence used by
/// `reference_resolver::resolve_name` and
/// `typeinference::TypeDefinitionRegistry::resolve_type_position_id` (local
/// declaration -> explicit import -> glob, user tier before std) — duplicated
/// here in miniature because coherence runs before `TypeDefinitionRegistry`
/// exists.
// arch-implements: ["arch.coherence.requirement-1"]
// arch-implements: ["arch.coherence.requirement-2"]
fn resolve_id(names: &ResolvedNames, current_module: &[String], name: &str) -> Option<SymbolId> {
    if let Some(id) = names
        .symbols
        .get(&(current_module.to_vec(), name.to_string()))
    {
        return Some(*id);
    }
    let scope = names.scopes.get(current_module)?;
    if let Some(binding) = scope.explicit.get(name) {
        return Some(binding.symbol_id);
    }
    let mut std_hit = None;
    for (tier, glob_module) in &scope.globs {
        if let Some(id) = names.symbols.get(&(glob_module.clone(), name.to_string())) {
            match tier {
                GlobTier::User => return Some(*id),
                GlobTier::Std => std_hit = std_hit.or(Some(*id)),
            }
        }
    }
    std_hit
}

/// `SymbolId -> declaring module`, inverted from `names.symbols`'
/// `(module, name) -> id` map. Every id has exactly one canonical declaring
/// entry: `SymbolTable::intern` dedups on the full `(module, name)` key, and
/// import bindings reuse the source declaration's id rather than minting a
/// second one under the importing module — so the inversion is unambiguous.
fn declaring_modules(names: &ResolvedNames) -> HashMap<SymbolId, Vec<String>> {
    names
        .symbols
        .iter()
        .map(|((module, _name), id)| (*id, module.clone()))
        .collect()
}

/// A structurally comparable form of `TypeExpr`, with `Named` constructors
/// resolved to their declaring `SymbolId` so that two spellings of the same
/// type (a local name vs. an imported alias) compare equal for overlap
/// detection. Only concrete impls exist today (no generics on `ImplBlock`),
/// so canonicalization never needs to account for bound type variables.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum CanonicalType {
    Resolved(SymbolId, Vec<CanonicalType>),
    Unresolved(String, Vec<CanonicalType>),
    Unit,
    Tuple(Vec<CanonicalType>),
    Record(Vec<(String, CanonicalType)>),
    Array(Box<CanonicalType>),
    SizedArray(Box<CanonicalType>, u64),
    Reference(Box<CanonicalType>),
    MutReference(Box<CanonicalType>),
    Fun(
        Vec<CanonicalType>,
        Option<Box<CanonicalType>>,
        crate::types::CallMultiplicity,
        crate::types::CallMutation,
    ),
    /// `impl Aspect` in parameter position — not expected in an impl's own
    /// target type, kept only so canonicalization stays total.
    Opaque,
    /// An impl-scoped type parameter (e.g. `T` in `impl<T: Copy> ... for Pair<T, T>`),
    /// keyed by its position in the target type's top-level arguments.
    /// Two conditional impls with different letters (`T` vs `U`) at the same
    /// position canonicalize identically — required for §3.1 overlap detection.
    TypeParam(usize),
}

fn canonicalize(names: &ResolvedNames, current_module: &[String], ty: &TypeExpr) -> CanonicalType {
    let go = |t: &TypeExpr| canonicalize(names, current_module, t);
    match ty {
        TypeExpr::Named(name, args) => {
            let cargs: Vec<_> = args.iter().map(go).collect();
            match resolve_id(names, current_module, name) {
                Some(id) => CanonicalType::Resolved(id, cargs),
                None => CanonicalType::Unresolved(name.clone(), cargs),
            }
        }
        TypeExpr::Unit => CanonicalType::Unit,
        TypeExpr::Tuple(items) => CanonicalType::Tuple(items.iter().map(go).collect()),
        TypeExpr::Record(fields) => CanonicalType::Record(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), go(ty)))
                .collect(),
        ),
        TypeExpr::Array(inner) => CanonicalType::Array(Box::new(go(inner))),
        TypeExpr::SizedArray(inner, n) => CanonicalType::SizedArray(Box::new(go(inner)), *n),
        TypeExpr::Reference(inner) => CanonicalType::Reference(Box::new(go(inner))),
        TypeExpr::MutReference(inner) => CanonicalType::MutReference(Box::new(go(inner))),
        TypeExpr::Fun {
            params,
            return_type: ret,
            call_multiplicity,
            call_mutation,
        } => CanonicalType::Fun(
            params.iter().map(go).collect(),
            ret.as_deref().map(go).map(Box::new),
            *call_multiplicity,
            *call_mutation,
        ),
        // `T::AssocType` (RFC-0082) isn't resolved to a concrete type at this pass
        // either — both stay opaque until issue #242 does that resolution for real.
        // `dyn Aspect` (RFC-0008) is existential, never a concrete impl target, so
        // it stays opaque here for the same reason.
        TypeExpr::ImplAspect { .. }
        | TypeExpr::Projection { .. }
        | TypeExpr::RecordProjection { .. }
        | TypeExpr::DynAspect { .. } => CanonicalType::Opaque,
    }
}

/// Canonicalize an impl's target type for overlap detection: top-level unresolved
/// names (impl-scoped type parameters like `T` in `impl<T> ... for Pair<T, T>`)
/// are mapped to `CanonicalType::TypeParam(i)` by position, so `Pair<T, T>` and
/// `Pair<U, U>` canonicalize identically. The same substitution applies to
/// structural targets (`T[]`, tuples, `fun` types) at their own top-level
/// positions -- RFC-0061 §2 requires structural targets to follow the ordinary
/// overlap rules "without special cases," so `T[]` and `U[]` must canonicalize
/// identically just like `Pair<T, T>` and `Pair<U, U>` do. Non-top-level
/// positions and resolved names use the ordinary `canonicalize` path.
fn canonicalize_impl_target(
    names: &ResolvedNames,
    current_module: &[String],
    ib: &ImplBlock,
) -> CanonicalType {
    // Collect the set of impl-scoped type param names (from ib.generics)
    // so we can identify them in the target type's top-level arguments.
    let impl_param_names: std::collections::HashSet<&str> =
        ib.generics.iter().map(|g| g.name.as_str()).collect();

    let map_arg = |i: usize, arg: &TypeExpr| -> CanonicalType {
        if let TypeExpr::Named(n, inner_args) = arg
            && inner_args.is_empty()
            && impl_param_names.contains(n.as_str())
        {
            return CanonicalType::TypeParam(i);
        }
        canonicalize(names, current_module, arg)
    };

    match &ib.target_type {
        TypeExpr::Named(target_name, args) if !args.is_empty() => {
            // Top-level args: map each to TypeParam(i) if it's an impl param,
            // else canonicalize normally.
            let cargs: Vec<CanonicalType> = args
                .iter()
                .enumerate()
                .map(|(i, arg)| map_arg(i, arg))
                .collect();
            match resolve_id(names, current_module, target_name) {
                Some(id) => CanonicalType::Resolved(id, cargs),
                None => CanonicalType::Unresolved(target_name.clone(), cargs),
            }
        }
        TypeExpr::Array(inner) => CanonicalType::Array(Box::new(map_arg(0, inner))),
        TypeExpr::SizedArray(inner, n) => {
            CanonicalType::SizedArray(Box::new(map_arg(0, inner)), *n)
        }
        TypeExpr::Tuple(items) => CanonicalType::Tuple(
            items
                .iter()
                .enumerate()
                .map(|(i, arg)| map_arg(i, arg))
                .collect(),
        ),
        TypeExpr::Record(fields) => CanonicalType::Record(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), canonicalize(names, current_module, ty)))
                .collect(),
        ),
        TypeExpr::Fun {
            params,
            return_type: ret,
            call_multiplicity,
            call_mutation,
        } => CanonicalType::Fun(
            params
                .iter()
                .enumerate()
                .map(|(i, arg)| map_arg(i, arg))
                .collect(),
            ret.as_deref().map(|r| Box::new(map_arg(params.len(), r))),
            *call_multiplicity,
            *call_mutation,
        ),
        _ => canonicalize(names, current_module, &ib.target_type),
    }
}

/// If `arg` is a bare `Named` type referring to one of the impl's own generic
/// parameters, return its name. Used to identify which top-level positions of
/// a structural or nominal target are impl-scoped type variables.
fn name_at<'a>(
    arg: &'a TypeExpr,
    impl_param_names: &std::collections::HashSet<&str>,
) -> Option<&'a str> {
    if let TypeExpr::Named(n, _) = arg
        && impl_param_names.contains(n.as_str())
    {
        return Some(n.as_str());
    }
    None
}

/// Collect the scoped type-param bounds for an impl block, indexed by the
/// target type's top-level argument position. Returns `(pos_bounds, neg_bounds)`
/// where `pos_bounds[i]` is the list of positive aspect names required of the
/// type at position `i`, and `neg_bounds[i]` is the list of negative aspect
/// names. Both are empty vectors for unconditional impls, or for any impl-scoped
/// param that isn't a bare `Named` type in top-level position.
///
/// Structural targets (`T[]`, tuples, `fun` types) get the same positional
/// treatment as `Named` targets: an array's element type is position 0, a
/// tuple's elements are positions `0..n`, and a function type's parameters are
/// positions `0..n` with the return type at position `n`. This is required by
/// RFC-0061 §2's "no special cases" claim -- without it, `extend<T: Bound>
/// T[]: Aspect` and `extend<T: !Bound> T[]: Aspect` would never be recognized
/// as syntactically disjoint (RFC-0036 §3.1) and would incorrectly conflict.
fn scoped_type_param_bounds(ib: &ImplBlock) -> (Vec<Vec<GenericBound>>, Vec<Vec<GenericBound>>) {
    // Build the set of impl param names.
    let impl_param_names: std::collections::HashSet<&str> =
        ib.generics.iter().map(|g| g.name.as_str()).collect();

    // Build a name → target-position map depending on the target's shape. A
    // type param at `ib.generics` position 0 may appear at a different target
    // position (e.g. `impl<T, U> ... for Pair<U, T>`).
    let (arg_count, name_to_target_pos): (usize, HashMap<&str, usize>) = match &ib.target_type {
        TypeExpr::Named(_, args) => {
            let map = args
                .iter()
                .enumerate()
                .filter_map(|(i, arg)| name_at(arg, &impl_param_names).map(|n| (n, i)))
                .collect();
            (args.len(), map)
        }
        TypeExpr::Array(inner) | TypeExpr::SizedArray(inner, _) => {
            let map = name_at(inner, &impl_param_names)
                .map(|n| (n, 0))
                .into_iter()
                .collect();
            (1, map)
        }
        TypeExpr::Tuple(items) => {
            let map = items
                .iter()
                .enumerate()
                .filter_map(|(i, arg)| name_at(arg, &impl_param_names).map(|n| (n, i)))
                .collect();
            (items.len(), map)
        }
        TypeExpr::Fun {
            params,
            return_type: ret,
            ..
        } => {
            let mut map: HashMap<&str, usize> = params
                .iter()
                .enumerate()
                .filter_map(|(i, arg)| name_at(arg, &impl_param_names).map(|n| (n, i)))
                .collect();
            if let Some(n) = ret.as_deref().and_then(|r| name_at(r, &impl_param_names)) {
                map.insert(n, params.len());
            }
            (params.len() + usize::from(ret.is_some()), map)
        }
        _ => return (vec![], vec![]),
    };

    let mut pos_bounds: Vec<Vec<GenericBound>> = vec![vec![]; arg_count];
    let mut neg_bounds: Vec<Vec<GenericBound>> = vec![vec![]; arg_count];

    // From inline bounds: `impl<T: Copy> ...` → pos_bounds for T's target position
    for gp in &ib.generics {
        if let Some(&pos) = name_to_target_pos.get(gp.name.as_str()) {
            for bound in &gp.bounds {
                if bound.polarity == crate::ast::Polarity::Positive {
                    if let Some(aspect) = GenericBound::from_ast(bound) {
                        pos_bounds[pos].push(aspect);
                    }
                } else if let Some(aspect) = GenericBound::from_ast(bound) {
                    neg_bounds[pos].push(aspect);
                }
            }
        }
    }

    // From where clause: `where T: Copy` → same merge
    if let Some(wc) = &ib.where_clause {
        merge_where_clause_bounds(
            wc,
            &name_to_target_pos,
            &impl_param_names,
            &mut pos_bounds,
            &mut neg_bounds,
        );
    }

    (pos_bounds, neg_bounds)
}

/// Merge where-clause constraints into the pos/neg bound vectors.
fn merge_where_clause_bounds(
    wc: &WhereClause,
    name_to_pos: &HashMap<&str, usize>,
    impl_param_names: &std::collections::HashSet<&str>,
    pos_bounds: &mut [Vec<GenericBound>],
    neg_bounds: &mut [Vec<GenericBound>],
) {
    for constraint in &wc.constraints {
        if !impl_param_names.contains(constraint.name.as_str()) {
            continue;
        }
        if let Some(&pos) = name_to_pos.get(constraint.name.as_str()) {
            for bound in &constraint.bounds {
                if bound.polarity == crate::ast::Polarity::Positive {
                    if let Some(aspect) = GenericBound::from_ast(bound) {
                        pos_bounds[pos].push(aspect);
                    }
                } else if let Some(aspect) = GenericBound::from_ast(bound) {
                    neg_bounds[pos].push(aspect);
                }
            }
        }
    }
}

/// Two sets of conditional impl bounds are provably disjoint iff, at some
/// position `i`, one impl's positive bound set contains an aspect name present
/// in the other's negative bound set at the same position. This is §3.1's
/// disjointness criterion: `impl<T: Copy> ...` and `impl<T: !Copy> ...` have
/// `Copy` in pos[0] of the first and `Copy` in neg[0] of the second.
fn provably_disjoint(
    (a_pos, a_neg): &(Vec<Vec<GenericBound>>, Vec<Vec<GenericBound>>),
    (b_pos, b_neg): &(Vec<Vec<GenericBound>>, Vec<Vec<GenericBound>>),
) -> bool {
    let len = a_pos.len().max(b_pos.len());
    for i in 0..len {
        let a_p = a_pos.get(i).map_or(&[] as &[GenericBound], |v| v);
        let a_n = a_neg.get(i).map_or(&[] as &[GenericBound], |v| v);
        let b_p = b_pos.get(i).map_or(&[] as &[GenericBound], |v| v);
        let b_n = b_neg.get(i).map_or(&[] as &[GenericBound], |v| v);
        // a's positive intersects b's negative → disjoint
        if a_p.iter().filter_map(GenericBound::aspect_name).any(|a| {
            b_n.iter()
                .filter_map(GenericBound::aspect_name)
                .any(|b| a == b)
        }) {
            return true;
        }
        // b's positive intersects a's negative → disjoint
        if b_p.iter().filter_map(GenericBound::aspect_name).any(|b| {
            a_n.iter()
                .filter_map(GenericBound::aspect_name)
                .any(|a| b == a)
        }) {
            return true;
        }
    }
    false
}

/// The declaring `SymbolId` of a type expression's own outermost constructor,
/// if it names one at all. Structural types (tuples, arrays, pointers,
/// function types) have no owning module, so they can never satisfy the
/// orphan rule's "local" half on their own — only `Named` types can.
///
/// `impl_generics` is the enclosing impl's own generic parameter list
/// (RFC-0097): when `ty` is a bare `Named(name, [])` matching one of those
/// parameters — `impl<T: Bound> Aspect for T` — the target is the impl's own
/// type parameter, not a declared struct or enum, and target-locality is
/// vacuously unsatisfiable for it (§2). That must be checked explicitly and
/// first, rather than left to `resolve_id` incidentally failing to find a
/// symbol named `T`: a generic parameter name is never registered in
/// `names.symbols` today, so the two cases happen to produce the same `None`
/// either way, but only this branch encodes that as a deliberate, specified
/// rule rather than a coincidence of how name resolution happens to fail.
fn outermost_id(
    names: &ResolvedNames,
    current_module: &[String],
    impl_generics: &[String],
    ty: &TypeExpr,
) -> Option<SymbolId> {
    match ty {
        TypeExpr::Named(name, args) if args.is_empty() && impl_generics.contains(name) => None,
        TypeExpr::Named(name, _) => resolve_id(names, current_module, name),
        _ => None,
    }
}

struct CollectedImpl<'a> {
    module: &'a [String],
    aspect_name: &'a str,
    aspect_id: Option<SymbolId>,
    target_local: bool,
    /// The aspect's own type arguments (e.g. `i64` in `impl From<i64> for f64`)
    /// plus the target type, canonicalized. `From<i64> for f64` and
    /// `From<u8> for f64` both target `f64` but are different impls of the
    /// aspect — overlap is about the *whole* instantiation, not the target
    /// type alone.
    canonical_key: (Vec<CanonicalType>, CanonicalType),
    /// Scoped type-param bounds for §3.1/§3.2 overlap checks.
    scoped_bounds: (Vec<Vec<GenericBound>>, Vec<Vec<GenericBound>>),
    /// RFC-0081/RFC-0060 §5: whether this is `impl !Aspect` or `impl Aspect`.
    polarity: Polarity,
    span: &'a Span,
    /// Method names this impl provides -- for the cross-aspect ambiguous-
    /// method check below (issue #272).
    method_names: Vec<&'a str>,
    /// The target type's head name, for diagnostics — `Foo` for both
    /// `Foo` and `Foo<T>`. Empty for a structural target, which has no head
    /// to name.
    target_head: String,
    /// Whether this impl has its own generics or a structural target. The
    /// elaborator's `build_aspect_method_map` (post-construction) already
    /// catches two *concrete, nominal* impls of different aspects providing
    /// the same method name -- but it walks `TypedImplBlock.methods`, which is
    /// empty for a generic impl (bodies are deferred to call-time
    /// reconstruction), and its target-name extraction skips structural
    /// targets entirely. This flag scopes the check below to exactly the
    /// cases the elaborator's check cannot see, so the two checks stay
    /// additive instead of double-reporting (with possibly differently
    /// worded messages) the same concrete-nominal collision.
    is_structural_or_generic: bool,
}

/// Whether two canonicalized targets could describe an overlapping concrete
/// instantiation — issue #244's shape-crossing overlap fix. Unlike plain
/// equality (the pre-#244 behavior, still correct for two identically-shaped
/// impls), `TypeParam` is treated as a wildcard that matches anything at that
/// position, so a blanket impl's target (`Resolved(Foo, [TypeParam(0)])`) is
/// compatible with a concrete impl's (`Resolved(Foo, [Resolved(i64, [])])`) —
/// the gap that let a blanket and a concrete impl of the same aspect silently
/// coexist without ever being compared.
fn canonical_types_compatible(a: &CanonicalType, b: &CanonicalType) -> bool {
    match (a, b) {
        (CanonicalType::TypeParam(_), _)
        | (_, CanonicalType::TypeParam(_))
        | (CanonicalType::Unit, CanonicalType::Unit)
        | (CanonicalType::Opaque, CanonicalType::Opaque) => true,
        (CanonicalType::Resolved(id_a, args_a), CanonicalType::Resolved(id_b, args_b)) => {
            id_a == id_b
                && args_a.len() == args_b.len()
                && args_a
                    .iter()
                    .zip(args_b)
                    .all(|(x, y)| canonical_types_compatible(x, y))
        }
        (CanonicalType::Unresolved(n_a, args_a), CanonicalType::Unresolved(n_b, args_b)) => {
            n_a == n_b
                && args_a.len() == args_b.len()
                && args_a
                    .iter()
                    .zip(args_b)
                    .all(|(x, y)| canonical_types_compatible(x, y))
        }
        (CanonicalType::Tuple(xs), CanonicalType::Tuple(ys)) => {
            xs.len() == ys.len()
                && xs
                    .iter()
                    .zip(ys)
                    .all(|(x, y)| canonical_types_compatible(x, y))
        }
        (CanonicalType::Array(x), CanonicalType::Array(y)) => canonical_types_compatible(x, y),
        (CanonicalType::SizedArray(x, n1), CanonicalType::SizedArray(y, n2)) => {
            n1 == n2 && canonical_types_compatible(x, y)
        }
        (CanonicalType::Reference(x), CanonicalType::Reference(y))
        | (CanonicalType::MutReference(x), CanonicalType::MutReference(y)) => {
            canonical_types_compatible(x, y)
        }
        (CanonicalType::Fun(ps1, r1, c1, m1), CanonicalType::Fun(ps2, r2, c2, m2)) => {
            ps1.len() == ps2.len()
                && c1 == c2
                && m1 == m2
                && ps1
                    .iter()
                    .zip(ps2)
                    .all(|(x, y)| canonical_types_compatible(x, y))
                && match (r1, r2) {
                    (Some(a), Some(b)) => canonical_types_compatible(a, b),
                    (None, None) => true,
                    _ => false,
                }
        }
        _ => false,
    }
}

/// Whether a canonicalized target contains a `TypeParam` anywhere — i.e.
/// whether the impl it came from is a blanket/conditional impl rather than a
/// fully concrete one. Used to distinguish RFC-0060 §5's two polarity-mismatch
/// cases: a negative impl vs. a *blanket* positive impl for an overlapping
/// instantiation is permitted (the negative impl wins), but a negative impl
/// vs. a *concrete* positive impl for the exact same type is still a `T0015`
/// coherence error (RFC-0081 §2.2/issue #264) — polarity alone doesn't decide
/// it, blanket-ness does.
fn contains_type_param(ct: &CanonicalType) -> bool {
    match ct {
        CanonicalType::TypeParam(_) => true,
        CanonicalType::Resolved(_, args) | CanonicalType::Unresolved(_, args) => {
            args.iter().any(contains_type_param)
        }
        CanonicalType::Tuple(items) => items.iter().any(contains_type_param),
        CanonicalType::Record(fields) => fields.iter().any(|(_, ty)| contains_type_param(ty)),
        CanonicalType::Array(inner)
        | CanonicalType::SizedArray(inner, _)
        | CanonicalType::Reference(inner)
        | CanonicalType::MutReference(inner) => contains_type_param(inner),
        CanonicalType::Fun(params, ret, _, _) => {
            params.iter().any(contains_type_param)
                || ret.as_deref().is_some_and(contains_type_param)
        }
        CanonicalType::Unit | CanonicalType::Opaque => false,
    }
}

fn is_local(
    declaring: &HashMap<SymbolId, Vec<String>>,
    id: Option<SymbolId>,
    module: &[String],
) -> bool {
    id.and_then(|id| declaring.get(&id))
        .is_some_and(|m| m.as_slice() == module)
}

/// Whether `concrete` (a fully-resolved `CanonicalType`, no `TypeParam`)
/// satisfies every required positive aspect and none of the required negative
/// aspects, per the OTHER impls collected in this same coherence pass. A
/// simple presence lookup (unconditional impls only) — this pass runs before
/// type-checking, so the typechecker's own `type_satisfies_aspect` (which
/// recurses into conditional impls) isn't available yet. Sufficient for this
/// issue's actual scope: a blanket impl with no bounds (the common case)
/// always overlaps a compatible concrete impl regardless of this check; this
/// only matters when the blanket carries real bound requirements.
fn concrete_satisfies_bounds(
    impls: &[CollectedImpl],
    concrete: &CanonicalType,
    pos_required: &[GenericBound],
    neg_required: &[GenericBound],
) -> bool {
    let has_direct_impl = |aspect: &str| {
        impls.iter().any(|imp| {
            imp.polarity == Polarity::Positive
                && imp.aspect_name == aspect
                && &imp.canonical_key.1 == concrete
        })
    };
    pos_required
        .iter()
        .filter_map(GenericBound::aspect_name)
        .all(has_direct_impl)
        && !neg_required
            .iter()
            .filter_map(GenericBound::aspect_name)
            .any(has_direct_impl)
}

/// Whether two shape-compatible impls of the same aspect actually overlap —
/// i.e. some concrete instantiation could satisfy both — given their
/// per-position bound requirements. Blanket-vs-blanket reduces to the
/// existing `provably_disjoint` bound-list comparison; blanket-vs-concrete
/// additionally requires the concrete side's argument to actually satisfy the
/// blanket's bound requirements at each differing position.
fn impls_actually_overlap(impls: &[CollectedImpl], a: &CollectedImpl, b: &CollectedImpl) -> bool {
    if provably_disjoint(&a.scoped_bounds, &b.scoped_bounds) {
        return false;
    }
    let (CanonicalType::Resolved(_, a_args) | CanonicalType::Unresolved(_, a_args)) =
        &a.canonical_key.1
    else {
        return true; // no per-position args to cross-check further
    };
    let (CanonicalType::Resolved(_, b_args) | CanonicalType::Unresolved(_, b_args)) =
        &b.canonical_key.1
    else {
        return true;
    };
    for i in 0..a_args.len().min(b_args.len()) {
        let a_pos = &a_args[i];
        let b_pos = &b_args[i];
        if matches!(a_pos, CanonicalType::TypeParam(_))
            && !matches!(b_pos, CanonicalType::TypeParam(_))
        {
            let pos = a
                .scoped_bounds
                .0
                .get(i)
                .map_or(&[] as &[GenericBound], |v| v);
            let neg = a
                .scoped_bounds
                .1
                .get(i)
                .map_or(&[] as &[GenericBound], |v| v);
            if !concrete_satisfies_bounds(impls, b_pos, pos, neg) {
                return false;
            }
        }
        if matches!(b_pos, CanonicalType::TypeParam(_))
            && !matches!(a_pos, CanonicalType::TypeParam(_))
        {
            let pos = b
                .scoped_bounds
                .0
                .get(i)
                .map_or(&[] as &[GenericBound], |v| v);
            let neg = b
                .scoped_bounds
                .1
                .get(i)
                .map_or(&[] as &[GenericBound], |v| v);
            if !concrete_satisfies_bounds(impls, a_pos, pos, neg) {
                return false;
            }
        }
    }
    true
}

/// Check the orphan rule (T0014) and overlap detection (T0015) for every
/// concrete `impl Aspect for Type` block in the program. See RFC-0060 / the
/// "Aspect Implementation Coherence" section of `declarations.md`.
///
/// # Errors
/// Returns an error if any `impl` violates the orphan rule (T0014) or overlaps
/// with another `impl` of the same aspect/type instantiation (T0015).
#[allow(clippy::too_many_lines)]
pub fn check(graph: &NormalizedModuleGraph, names: &ResolvedNames) -> Result<(), MetelError> {
    let declaring = declaring_modules(names);

    let mut impls: Vec<CollectedImpl> = Vec::new();
    for module in graph.modules() {
        for decl in &module.program.decls {
            let Decl::Impl(ib) = decl else { continue };
            let Some(aspect_name) = ib.aspect_name.as_deref() else {
                continue; // inherent impl (no aspect) — nothing to check
            };
            let aspect_id = resolve_id(names, &module.module_path, aspect_name);
            let impl_generic_names: Vec<String> =
                ib.generics.iter().map(|g| g.name.clone()).collect();
            let target_local = is_local(
                &declaring,
                outermost_id(
                    names,
                    &module.module_path,
                    &impl_generic_names,
                    &ib.target_type,
                ),
                &module.module_path,
            );
            let canonical_args = ib
                .aspect_type_args
                .iter()
                .map(|a| canonicalize(names, &module.module_path, a))
                .collect();
            // Use canonicalize_impl_target so TypeParam(i) is produced for
            // impl-scoped type variables — required for §3.1/§3.2 overlap detection.
            let canonical_target = canonicalize_impl_target(names, &module.module_path, ib);
            let scoped_bounds = scoped_type_param_bounds(ib);
            let is_structural_or_generic = !ib.generics.is_empty()
                || matches!(
                    ib.target_type,
                    TypeExpr::Array(_)
                        | TypeExpr::SizedArray(_, _)
                        | TypeExpr::Tuple(_)
                        | TypeExpr::Fun { .. }
                );
            let target_head = match &ib.target_type {
                TypeExpr::Named(name, _) => name.rsplit("::").next().unwrap_or(name).to_string(),
                _ => String::new(),
            };
            impls.push(CollectedImpl {
                module: &module.module_path,
                aspect_name,
                aspect_id,
                target_local,
                canonical_key: (canonical_args, canonical_target),
                scoped_bounds,
                polarity: ib.polarity,
                span: &ib.span,
                method_names: ib.methods.iter().map(|m| m.name.as_str()).collect(),
                target_head,
                is_structural_or_generic,
            });
        }
    }

    // Orphan rule (T0014). Skipped when the aspect name itself doesn't
    // resolve — an undefined aspect is a more fundamental error the
    // typechecker will report on its own (T0003), and layering a coherence
    // error on top of it would only obscure the real problem.
    for imp in &impls {
        if imp.aspect_name == "Drop" && matches!(imp.canonical_key.1, CanonicalType::Record(_)) {
            return Err(MetelError::type_error(
                TypeErrorCode::T0001,
                "anonymous records cannot implement `Drop`; teardown logic requires a nominal type",
                imp.span,
            ));
        }
        let Some(aspect_id) = imp.aspect_id else {
            continue;
        };
        let aspect_local = is_local(&declaring, Some(aspect_id), imp.module);
        if !aspect_local && !imp.target_local {
            return Err(MetelError::type_error(
                TypeErrorCode::T0014,
                format!(
                    "orphan implementation: neither `{}` nor the target type is local to this module",
                    imp.aspect_name
                ),
                imp.span,
            ));
        }
    }

    // Overlap detection (T0015): two impls of the same resolved aspect
    // conflict when some concrete instantiation could satisfy both. Checked
    // via a pairwise scan across ALL impls of a given aspect (issue #244),
    // not exact-key grouping — the pre-#244 grouping only ever compared
    // identically-shaped targets, so a blanket impl (`Resolved(Foo,
    // [TypeParam(0)])`) and a concrete impl (`Resolved(Foo, [Resolved(i64,
    // [])])`) were never even placed in the same group, silently missing a
    // real conflict. `canonical_types_compatible` treats `TypeParam` as a
    // wildcard so shape-crossing pairs are now compared too.
    let mut by_aspect: HashMap<SymbolId, Vec<&CollectedImpl>> = HashMap::new();
    for imp in &impls {
        let Some(aspect_id) = imp.aspect_id else {
            continue;
        };
        by_aspect.entry(aspect_id).or_default().push(imp);
    }

    for group in by_aspect.values() {
        for i in 0..group.len() {
            for j in (i + 1)..group.len() {
                let a = group[i];
                let b = group[j];
                // Different aspect type-args (e.g. `From<i64>` vs `From<u8>`)
                // never overlap regardless of target shape.
                if a.canonical_key.0 != b.canonical_key.0 {
                    continue;
                }
                if !canonical_types_compatible(&a.canonical_key.1, &b.canonical_key.1) {
                    continue;
                }
                // RFC-0060 §5: an explicit negative impl and a *blanket*
                // positive impl for an overlapping instantiation is permitted
                // — the negative impl wins, a priority question rather than a
                // coherence conflict. But a negative impl and a *concrete*
                // positive impl for the exact same type is still a T0015
                // conflict (RFC-0081 §2.2/issue #264) — polarity mismatch only
                // excuses the pair when the positive side is a blanket.
                if a.polarity != b.polarity {
                    let positive = if a.polarity == Polarity::Positive {
                        a
                    } else {
                        b
                    };
                    if contains_type_param(&positive.canonical_key.1) {
                        continue;
                    }
                }
                if !impls_actually_overlap(&impls, a, b) {
                    continue;
                }
                return Err(MetelError::type_error(
                    TypeErrorCode::T0015,
                    format!(
                        "conflicting implementation: `{}` is already implemented for this type at {}:{}:{}",
                        a.aspect_name, a.span.filename, a.span.line, a.span.col
                    ),
                    b.span,
                ));
            }
        }
    }

    // RFC-0071 §4: no type may implement both `Copy` and `Drop` (issue #302).
    //
    // `typechecker::inference` enforces this at each impl's own declaration
    // site, but only when the target is a *closed* nominal type — a
    // conditional impl has an open target, so that check bails and two
    // overlapping conditional impls of the two aspects slip through:
    // `extend<T: Copy> Foo<T>: Copy` plus `extend<T: Display> Foo<T>: Drop`
    // gives `Foo<i64>` both, since `i64` is `Copy` and `Display`. The
    // same-aspect T0015 scan above never compares them either, because it
    // groups by aspect and these are two different aspects.
    //
    // The question to ask is exactly the one the machinery above already
    // answers — "could a single concrete instantiation satisfy both of these
    // impls?" — so this reuses `canonical_types_compatible` +
    // `impls_actually_overlap` rather than approximating it. Consequences
    // worth stating, since they are the point of doing it precisely:
    //
    //   - `extend<T: Copy> Foo<T>: Copy` + `extend<T: !Copy> Foo<T>: Drop` is
    //     accepted; the bounds are provably disjoint, so no instantiation
    //     gets both.
    //   - `extend<T: Copy> Foo<T>: Copy` + `extend Foo<String>: Drop` is
    //     accepted, because `String` is not `Copy` and so is not in the
    //     blanket's reach — while the same pair with `Foo<i64>` is rejected.
    //
    // The declaration-site check stays rather than being folded into this
    // one. `impls_actually_overlap`'s blanket-vs-concrete arm resolves bounds
    // via `concrete_satisfies_bounds`, which only sees *unconditional* impls
    // collected in this pass, so it under-approximates exactly where the
    // typechecker's `type_satisfies_aspect` — which recurses through
    // conditional impls — does not. The two are complementary.
    //
    // Both aspects are looked up as the stdlib symbols rather than matched by
    // name, so a user module declaring its own unrelated `Copy` marker does
    // not inherit this rule. If either is absent (a program compiled without
    // the prelude) there is nothing to enforce.
    let std_core = vec!["std".to_string(), "core".to_string()];
    let copy_id = names.symbols.get(&(std_core.clone(), "Copy".to_string()));
    let drop_id = names.symbols.get(&(std_core, "Drop".to_string()));
    if let (Some(&copy_id), Some(&drop_id)) = (copy_id, drop_id) {
        let positive_impls_of = |id: SymbolId| {
            impls
                .iter()
                .filter(move |imp| imp.polarity == Polarity::Positive && imp.aspect_id == Some(id))
        };
        for copy_impl in positive_impls_of(copy_id) {
            for drop_impl in positive_impls_of(drop_id) {
                if !canonical_types_compatible(
                    &copy_impl.canonical_key.1,
                    &drop_impl.canonical_key.1,
                ) {
                    continue;
                }
                if !impls_actually_overlap(&impls, copy_impl, drop_impl) {
                    continue;
                }
                let subject = if drop_impl.target_head.is_empty() {
                    "this type".to_string()
                } else {
                    format!("`{}`", drop_impl.target_head)
                };
                return Err(MetelError::type_error(
                    TypeErrorCode::T0001,
                    format!(
                        "{subject} cannot implement both `Copy` and `Drop`: this `Drop` \
                         implementation overlaps the `Copy` implementation at {}:{}:{}",
                        copy_impl.span.filename, copy_impl.span.line, copy_impl.span.col
                    ),
                    drop_impl.span,
                ));
            }
        }
    }

    // Ambiguous method across two DIFFERENT aspects (T0013), generalizing
    // `elaborator::build_aspect_method_map` to conditional/generic impls and
    // structural targets (issue #272): if aspect A and aspect B both provide a
    // method of the same name, and some concrete instantiation could satisfy
    // both impls at once (the same "could this pair ever actually collide"
    // question T0015 asks of same-aspect overlaps, via `impls_actually_overlap`
    // /`provably_disjoint`), that's a genuine dispatch ambiguity -- reject it
    // up front rather than let dispatch silently pick whichever candidate's
    // bounds happen to be tried first. Skipped entirely for a pair that's both
    // concrete-nominal, since `build_aspect_method_map` already covers that
    // combination (see `is_structural_or_generic`'s doc).
    for i in 0..impls.len() {
        for j in (i + 1)..impls.len() {
            let a = &impls[i];
            let b = &impls[j];
            if a.aspect_id.is_none() || b.aspect_id.is_none() || a.aspect_id == b.aspect_id {
                continue;
            }
            if !a.is_structural_or_generic && !b.is_structural_or_generic {
                continue;
            }
            let Some(&shared_method) = a.method_names.iter().find(|m| b.method_names.contains(m))
            else {
                continue;
            };
            if !canonical_types_compatible(&a.canonical_key.1, &b.canonical_key.1) {
                continue;
            }
            if !impls_actually_overlap(&impls, a, b) {
                continue;
            }
            return Err(MetelError::type_error(
                TypeErrorCode::T0013,
                format!(
                    "ambiguous aspect method `{shared_method}`: both `{}` and `{}` provide this \
                     method for overlapping target types; use distinct method names or disjoint bounds",
                    a.aspect_name, b.aspect_name,
                ),
                b.span,
            ));
        }
    }

    Ok(())
}
