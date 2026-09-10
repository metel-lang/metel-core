//! RFC-0137 slice 2 (metel-core#858): move-triggered row narrowing and widening
//! on the inference side.
//!
//! The construction pass ([`crate::typechecker::construction::narrowing`]) runs
//! the same analysis over concrete `Type`s; this one runs over `InferType` so a
//! narrowed residual flowing into a slot that expects the whole struct is a real
//! `T0001`, reported at inference time rather than only surfacing in
//! `--move-check`. Both share [`crate::flow_state::FlowState`] and the same rules:
//! a depth-1 non-`Copy` field / tuple move off a plain binding narrows that
//! binding to an [`InferType::Residual`] of the same brand; reassigning the field
//! widens it back; the state is joined across `if` / `match` arms and to a fixed
//! point across loop back edges by the driver in `expressions.rs`.

use crate::flow_state::MoveCause;
use crate::place::{from_expr as place_from_expr, Place, Projection};
use crate::typed_ast::TypedExpr;
use crate::typeinference::{AspectAssumptions, InferContext, InferType};

impl InferContext {
    /// The current type of `name` once move-triggered narrowing is applied, or
    /// `None` to fall back to the ordinary `mono_env` lookup.
    pub(crate) fn narrowed_infertype(&self, name: &str) -> Option<InferType> {
        let declared = self.lookup_mono_raw(name)?;
        let moved = self.flow_ref().moved_shallow_projections(name);
        if moved.is_empty() {
            return None;
        }
        self.narrow_infer_row(&declared, &moved)
    }

    fn narrow_infer_row(&self, declared: &InferType, moved: &[Projection]) -> Option<InferType> {
        let moved_labels: std::collections::HashSet<&str> = moved
            .iter()
            .filter_map(|p| match p {
                Projection::Field { name, .. } => Some(name.as_str()),
                _ => None,
            })
            .collect();
        if moved_labels.is_empty() {
            return None;
        }
        match declared {
            // A branded struct value narrows to a same-brand residual (RFC-0137).
            InferType::Named(brand, args) => {
                let row = self.resolve_infer_struct_row(brand, args)?;
                filter_row(brand.clone(), &row, &moved_labels, Some(row.len()))
            }
            InferType::Residual { brand, fields } => {
                let full = self.resolve_infer_struct_row(brand, &[]).map(|r| r.len());
                filter_row(brand.clone(), fields, &moved_labels, full)
            }
            // An anonymous `record` value narrows to the record type with the
            // moved labels removed (RFC-0117). A label is only dropped when its
            // field type resolves to something not `Copy` — a `Copy` field read
            // by value is a copy, not a move, and does not narrow.
            InferType::Record(fields) => {
                let mut remaining: Vec<(String, InferType)> = fields
                    .iter()
                    .filter(|(name, ty)| {
                        !moved_labels.contains(name.as_str()) || self.field_is_copy(ty)
                    })
                    .cloned()
                    .collect();
                if remaining.len() == fields.len() || remaining.is_empty() {
                    return None;
                }
                remaining.sort_by(|(a, _), (b, _)| a.cmp(b));
                Some(InferType::Record(remaining))
            }
            _ => None,
        }
    }

    /// Whether `ty`, resolved against the substitution solved so far, is
    /// *definitely* `Copy`. An unresolved variable is not — narrowing holds a
    /// field until its type is known.
    fn field_is_copy(&self, ty: &InferType) -> bool {
        let resolved = self.apply_cached_subst(ty);
        // An unsuffixed numeric literal's var will default to a `Copy` primitive.
        if let InferType::Var(tv) = &resolved {
            return self.is_numeric_literal_var(*tv);
        }
        if infer_type_has_var(&resolved) {
            return false;
        }
        self.registry().infer_type_satisfies_aspect(
            self.current_module_path(),
            &resolved,
            "Copy",
            &AspectAssumptions::new(),
        )
    }

    /// The concrete-as-possible `(label, InferType)` row of a struct brand at the
    /// given type arguments, remapped per instantiation for a generic struct.
    fn resolve_infer_struct_row(
        &self,
        brand: &str,
        type_args: &[InferType],
    ) -> Option<Vec<(String, InferType)>> {
        let brand_id = self
            .registry()
            .resolve_type_id(self.current_module_path(), brand);
        if let Some(type_params) =
            brand_id.and_then(|id| self.registry().raw_struct_type_params().get(&id))
        {
            let raw = brand_id.and_then(|id| self.registry().raw_struct_env().get(&id))?;
            let mut remap = crate::typeinference::Substitution::new();
            for (&tp, arg) in type_params.iter().zip(type_args.iter()) {
                remap.bind(tp, arg.clone());
            }
            return Some(
                raw.iter()
                    .map(|entry| (entry.name.clone(), remap.apply(&entry.ty)))
                    .collect(),
            );
        }
        self.get_struct_fields(brand).map(|fields| {
            fields
                .iter()
                .map(|entry| (entry.name.clone(), entry.ty.clone()))
                .collect()
        })
    }

    /// After inferring an expression used in a *consuming* position, record any
    /// depth-1 partial move it performs so the base binding narrows from here on.
    /// The leaf field type is read from the registry, so this does not need the
    /// expression's already-inferred type in hand — only a direct field / tuple
    /// access off a bare identifier narrows (anything else is left to
    /// `move_check` and the construction pass).
    pub(crate) fn note_consumed_infer(&mut self, expr: &crate::ast::Expr) {
        let (root, label, projection) = match expr {
            crate::ast::Expr::FieldAccess { object, field, .. } => {
                let crate::ast::Expr::Ident(root, _) = object.as_ref() else {
                    return;
                };
                (
                    root.clone(),
                    Some(field.clone()),
                    Projection::field(field.clone()),
                )
            }
            crate::ast::Expr::TupleAccess { object, index, .. } => {
                let crate::ast::Expr::Ident(root, _) = object.as_ref() else {
                    return;
                };
                (root.clone(), None, Projection::TupleIndex(*index))
            }
            _ => return,
        };
        let Some(root_ty) = self.lookup_mono_raw(&root) else {
            return;
        };
        let leaf_ty = match &root_ty {
            InferType::Named(brand, args) => {
                let Some(l) = label.as_ref() else { return };
                let Some(row) = self.resolve_infer_struct_row(brand, args) else {
                    return;
                };
                match row.into_iter().find(|(name, _)| name == l) {
                    Some((_, ty)) => ty,
                    None => return,
                }
            }
            InferType::Residual { brand, .. } => {
                let Some(l) = label.as_ref() else { return };
                let Some(row) = self.resolve_infer_struct_row(brand, &[]) else {
                    return;
                };
                match row.into_iter().find(|(name, _)| name == l) {
                    Some((_, ty)) => ty,
                    None => return,
                }
            }
            InferType::Record(fields) => {
                let Some(l) = label.as_ref() else { return };
                match fields.iter().find(|(name, _)| name == l) {
                    Some((_, ty)) => ty.clone(),
                    None => return,
                }
            }
            _ => return,
        };
        // Record the move unless the moved leaf is *definitely* `Copy`. A `Named`
        // struct's field type is concrete or a generic parameter (a var there
        // means generic -- hold off, resolve at each call site). A `Record`'s
        // field type is often still a variable at this point (`"a".to_string()`
        // is unresolved until later); record optimistically and re-test each
        // moved label's `Copy`-ness at read time (`narrow_infer_row`).
        let is_record_root = matches!(&root_ty, InferType::Record(_));
        if !is_record_root && infer_type_has_var(&leaf_ty) {
            return;
        }
        if self.field_is_copy(&leaf_ty) {
            return;
        }
        let place = Place::new(root).with_projection(projection);
        let span = expr_span(expr);
        self.flow_mut()
            .record_move(place, span, MoveCause::Other, "struct-field".to_string());
    }

    /// Widen: `place := …` reinitializes `place`, so a field that was moved out
    /// of its root comes back and the root's type widens.
    pub(crate) fn note_reassigned_infer(&mut self, target: &crate::ast::AssignTarget) {
        if let Some(place) = place_from_assign_target(target) {
            self.flow_mut().reinitialize(&place);
        }
    }
}

fn filter_row(
    brand: String,
    fields: &[(String, InferType)],
    moved_labels: &std::collections::HashSet<&str>,
    full_len: Option<usize>,
) -> Option<InferType> {
    let mut remaining: Vec<(String, InferType)> = fields
        .iter()
        .filter(|(name, _)| !moved_labels.contains(name.as_str()))
        .cloned()
        .collect();
    if remaining.len() == fields.len() || remaining.is_empty() {
        return None;
    }
    if full_len == Some(remaining.len()) {
        return None;
    }
    remaining.sort_by(|(a, _), (b, _)| a.cmp(b));
    Some(InferType::Residual {
        brand,
        fields: remaining,
    })
}

/// A `Place` from an assignment target, for the depth-1 shapes narrowing tracks.
fn place_from_assign_target(target: &crate::ast::AssignTarget) -> Option<Place> {
    match target {
        crate::ast::AssignTarget::FieldAccess { object, field, .. } => {
            let crate::ast::Expr::Ident(root, _) = object.as_ref() else {
                return None;
            };
            Some(Place::new(root.clone()).with_projection(Projection::field(field.clone())))
        }
        crate::ast::AssignTarget::TupleAccess { object, index, .. } => {
            let crate::ast::Expr::Ident(root, _) = object.as_ref() else {
                return None;
            };
            Some(Place::new(root.clone()).with_projection(Projection::TupleIndex(*index)))
        }
        _ => None,
    }
}

fn expr_span(expr: &crate::ast::Expr) -> crate::ast::Span {
    expr.span().clone()
}

/// Whether `ty` mentions any type variable anywhere — i.e. is not fully
/// resolved. A leaf field type like this is not *known* non-`Copy`, so
/// narrowing on a move of it is held back until it is concrete.
fn infer_type_has_var(ty: &InferType) -> bool {
    match ty {
        InferType::Var(_) => true,
        InferType::Reference(inner)
        | InferType::MutReference(inner)
        | InferType::Array(inner)
        | InferType::SizedArray(inner, _) => infer_type_has_var(inner),
        InferType::Tuple(items) => items.iter().any(infer_type_has_var),
        InferType::Named(_, args)
        | InferType::Dyn {
            type_args: args, ..
        } => args.iter().any(infer_type_has_var),
        InferType::Record(fields) | InferType::Residual { fields, .. } => {
            fields.iter().any(|(_, t)| infer_type_has_var(t))
        }
        InferType::Fun(params, ret, ..) => {
            params.iter().any(infer_type_has_var) || infer_type_has_var(ret)
        }
        _ => false,
    }
}

/// Read a depth-1 move place out of a *typed* expression, for callers that
/// already have one in hand (mirrors the construction side).
#[allow(dead_code)]
pub(crate) fn typed_move_place(typed: &TypedExpr) -> Option<Place> {
    let place = place_from_expr(typed)?;
    match place.projections() {
        [Projection::Field { .. } | Projection::TupleIndex(_)] => Some(place),
        _ => None,
    }
}
