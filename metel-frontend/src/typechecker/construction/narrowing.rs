//! RFC-0137 slice 2 (metel-core#858): move-triggered row narrowing and widening,
//! run live during Pass 2 construction.
//!
//! A partial move of a non-`Copy` struct or `record` field (`let n := h.name;`)
//! narrows the base binding's *type* — `Handle` becomes `Handle.{ fd }`, a
//! [`Type::Residual`] of the same brand — for the rest of that binding's life,
//! joined conservatively across `if` / `match` arms and to a fixed point across
//! loop back edges. Reassigning the field (`h.name := "y";`) widens the type
//! back. Both are the type-level reading of the flow-sensitive moved-field state
//! [`crate::flow_state::FlowState`] already tracks — narrowing adds no
//! control-flow analysis of its own.
//!
//! This tracker is deliberately partial: it narrows on a depth-1 field / tuple
//! move out of a plain binding, which is what
//! `spec.ownership.narrowing.legality-1` and its fixtures exercise. A move
//! through a reference, a method receiver, a deeper path (`h.a.b`), or an index
//! is not narrowed here — `move_check` still enforces correctness over the typed
//! AST; only the residual *type* is unavailable at those sites.

use crate::flow_state::{FlowState, MoveCause};
use crate::place::{from_expr as place_from_expr, from_typed_place, Place, Projection};
use crate::typed_ast::{TypedExpr, TypedPlace};
use crate::types::Type;

use super::ConstructCtx;

impl ConstructCtx<'_> {
    /// Enter a fresh function / method body: stash the caller's move state and
    /// start an empty one. Parameters register themselves through the ordinary
    /// `ctx.bind` path (`bind_with_mutability` → `flow_bind`).
    pub(super) fn flow_enter_body(&mut self) -> FlowState {
        let saved = std::mem::take(&mut self.flow);
        self.flow.push_scope();
        saved
    }

    pub(super) fn flow_exit_body(&mut self, saved: FlowState) {
        self.flow = saved;
    }

    /// Register a binding for narrowing. Called from `bind_with_mutability`, so
    /// every `let` / `var` / pattern / parameter binding flows through here.
    pub(super) fn flow_bind(&mut self, name: &str, ty: &Type) {
        self.flow.bind_typed(name, ty);
    }

    /// The current type of `name` once move-triggered narrowing is applied, or
    /// `None` to fall back to the declared type in `ctx.env`. Only ever narrows a
    /// struct / `record` binding with a depth-1 field or tuple element moved out.
    pub(super) fn narrowed_type(&self, name: &str) -> Option<Type> {
        let declared = self.flow.binding_type(name)?.clone();
        let moved = self.flow.moved_shallow_projections(name);
        if moved.is_empty() {
            return None;
        }
        self.narrow_row(&declared, &moved)
    }

    /// A branded struct value narrows to a same-brand residual (RFC-0137); an
    /// anonymous `record` value narrows to the record type with the moved labels
    /// removed (RFC-0117).
    fn narrow_row(&self, declared: &Type, moved: &[Projection]) -> Option<Type> {
        match declared {
            Type::Named(brand, args, ..) => {
                let row = self.resolve_struct_row(brand, args)?;
                narrow_named(brand, args, &row, moved)
            }
            Type::Residual { brand, fields } => {
                let args = vec![];
                let full = self.resolve_struct_row(brand, &args);
                narrow_residual(brand, fields, full.as_deref(), moved)
            }
            Type::Record(fields) => narrow_record(fields, moved),
            _ => None,
        }
    }

    /// The concrete `(label, type)` row of a struct brand at the given type
    /// arguments. Mirrors `Expr::RecordProjection` construction's own field
    /// resolution — a generic struct's fields are remapped per instantiation.
    fn resolve_struct_row(&self, brand: &str, type_args: &[Type]) -> Option<Vec<(String, Type)>> {
        let brand_id = self.registry.resolve_type_id(self.current_module, brand);
        if let Some(type_params) =
            brand_id.and_then(|id| self.registry.raw_struct_type_params().get(&id))
        {
            let raw_fields = brand_id.and_then(|id| self.registry.raw_struct_env().get(&id))?;
            let mut remap = crate::typeinference::Substitution::new();
            for (&tp, arg) in type_params.iter().zip(type_args.iter()) {
                remap.bind(tp, super::type_to_infer(arg));
            }
            let dummy = crate::ast::Span::new(0, 0, "");
            return raw_fields
                .iter()
                .map(|entry| {
                    super::infer_type_to_type(&remap.apply(&entry.ty), &dummy)
                        .ok()
                        .map(|ty| (entry.name.clone(), ty))
                })
                .collect();
        }
        self.get_struct_fields(brand).map(|fields| {
            fields
                .iter()
                .map(|(name, ty, _)| (name.clone(), ty.clone()))
                .collect()
        })
    }

    /// After constructing an expression that is used in a *consuming* position
    /// (a `let` / `var` initializer, a call / method argument, a struct or
    /// record field initializer, a `return` / `break` value, a tuple or array
    /// element), record any depth-1 partial move it performs so the base
    /// binding narrows from here on.
    pub(super) fn note_consumed(&mut self, typed: &TypedExpr) {
        note_consumed_expr(self, typed);
    }

    /// Widen: assigning to `place` reinitializes it, so a field that was moved
    /// out of `place`'s root comes back and the root's type widens.
    pub(super) fn note_reassigned(&mut self, place: &TypedPlace) {
        if let Some(p) = from_typed_place(place) {
            self.flow.reinitialize(&p);
        }
    }
}

fn note_consumed_expr(ctx: &mut ConstructCtx, typed: &TypedExpr) {
    // A tuple / array literal takes ownership of each element.
    if let TypedExpr::Tuple(items, ..) | TypedExpr::Array(items, ..) = typed {
        for item in items {
            note_consumed_expr(ctx, item);
        }
        return;
    }
    if let TypedExpr::RecordLiteral { fields, .. } = typed {
        for (_, value) in fields {
            note_consumed_expr(ctx, value);
        }
        return;
    }
    if let TypedExpr::StructLiteral { fields, .. } = typed {
        for (_, value) in fields {
            note_consumed_expr(ctx, value);
        }
        return;
    }
    let Some(place) = place_from_expr(typed) else {
        return;
    };
    record_move_of_place(ctx, &place, typed);
}

/// Record `place` as moved, if it is a genuine depth-1 field / tuple move of a
/// non-`Copy` leaf out of a plain binding that still has a whole type.
fn record_move_of_place(ctx: &mut ConstructCtx, place: &Place, leaf: &TypedExpr) {
    // Only a depth-1 projection off a bare binding narrows that binding's own
    // row (RFC-0137 §2: a record-typed field moves as a unit; a deeper move is
    // RFC-0150's). Zero projections is a whole-value move — nothing to narrow.
    let [projection] = place.projections() else {
        return;
    };
    if !matches!(
        projection,
        Projection::Field { .. } | Projection::TupleIndex(_)
    ) {
        return;
    }
    // The moved leaf must be non-`Copy` for a move to happen at all.
    if is_copy(ctx, leaf.ty()) {
        return;
    }
    // The root must be a plain owned binding of a struct or anonymous record. A
    // reference root never narrows (RFC-0071 §7.1 already rejects moving a
    // non-`Copy` field out through one).
    let Some(root_ty) = ctx.flow.binding_type(place.root()) else {
        return;
    };
    if !matches!(
        root_ty,
        Type::Named(..) | Type::Residual { .. } | Type::Record(_)
    ) {
        return;
    }
    ctx.flow.record_move(
        place.clone(),
        leaf.span().clone(),
        MoveCause::Other,
        crate::move_check::type_bucket(leaf.ty()),
    );
}

fn is_copy(ctx: &ConstructCtx, ty: &Type) -> bool {
    matches!(
        ty,
        Type::Fun(_, _, _, crate::types::UseMultiplicity::Copy, _)
    ) || ctx
        .registry
        .type_satisfies_aspect(ctx.current_module, ty, "Copy")
}

fn narrow_named(
    brand: &str,
    args: &[Type],
    row: &[(String, Type)],
    moved: &[Projection],
) -> Option<Type> {
    let moved_labels = field_labels(moved);
    if moved_labels.is_empty() {
        return None;
    }
    let mut remaining: Vec<(String, Type)> = row
        .iter()
        .filter(|(name, _)| !moved_labels.contains(name.as_str()))
        .cloned()
        .collect();
    if remaining.len() == row.len() || remaining.is_empty() {
        // Nothing narrowed, or the whole value is gone (move_check reports the
        // latter as a use of a moved value).
        return None;
    }
    remaining.sort_by(|(a, _), (b, _)| a.cmp(b));
    let _ = args;
    Some(Type::Residual {
        brand: brand.to_string(),
        fields: remaining,
    })
}

fn narrow_residual(
    brand: &str,
    fields: &[(String, Type)],
    full_row: Option<&[(String, Type)]>,
    moved: &[Projection],
) -> Option<Type> {
    let moved_labels = field_labels(moved);
    if moved_labels.is_empty() {
        return None;
    }
    let mut remaining: Vec<(String, Type)> = fields
        .iter()
        .filter(|(name, _)| !moved_labels.contains(name.as_str()))
        .cloned()
        .collect();
    if remaining.len() == fields.len() || remaining.is_empty() {
        return None;
    }
    remaining.sort_by(|(a, _), (b, _)| a.cmp(b));
    if let Some(full) = full_row {
        if remaining.len() == full.len() {
            return None;
        }
    }
    Some(Type::Residual {
        brand: brand.to_string(),
        fields: remaining,
    })
}

/// RFC-0117: an anonymous record's row minus the moved labels. Construction runs
/// post-solve, so field types here are concrete and no `Copy` re-test is needed —
/// `record_move_of_place` already screened the leaf with `is_copy`.
fn narrow_record(fields: &[(String, Type)], moved: &[Projection]) -> Option<Type> {
    let moved_labels = field_labels(moved);
    if moved_labels.is_empty() {
        return None;
    }
    let remaining: Vec<(String, Type)> = fields
        .iter()
        .filter(|(name, _)| !moved_labels.contains(name.as_str()))
        .cloned()
        .collect();
    if remaining.len() == fields.len() || remaining.is_empty() {
        return None;
    }
    Some(Type::Record(remaining))
}

fn field_labels(moved: &[Projection]) -> std::collections::HashSet<&str> {
    moved
        .iter()
        .filter_map(|p| match p {
            Projection::Field { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect()
}
