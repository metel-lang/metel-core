//! Flow-sensitive partial-move tracking, shared across analyses.
//!
//! `crate::ownership::place::Place` is deliberately analysis-neutral (ADR-0045, RFC-0071
//! §9b) so a second analysis can walk the same places `move_check` does
//! without rebuilding them or disagreeing about partial moves. `FlowState`
//! and `MoveRecord` are the move-specific state layered on top of `Place` --
//! which fields of which binding are currently moved out, joined correctly
//! across `if`/`match` branches and widened to a fixed point across loop back
//! edges. They stayed inside `move_check` when `Place` itself moved to the
//! crate root (ADR-0045 kept them there deliberately, since nothing needed
//! them anywhere else yet), but RFC-0137 slice 2 (metel-core#858) is exactly
//! that second analysis: Pass 2 construction (`typechecker::construction`)
//! needs the same flow-sensitive moved-field tracking, live, to narrow a
//! binding's static type on a partial move and widen it back on reassignment
//! -- so this module exists now for the reason ADR-0045 anticipated.
//!
//! This module carries no diagnostic-reporting logic (no violation types, no
//! error messages) -- only the state and its pure transitions. Each consumer
//! decides what a moved/reassigned/joined/widened place *means* for its own
//! purposes: `move_check` turns it into `MoveViolation`s over the typed AST;
//! construction turns it into `Type::Residual` narrowing over `ctx.env`.

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::data::ast::Span;
use crate::data::types::Type;
use crate::ownership::place::{Place, Projection};

#[derive(Debug, Clone)]
pub(crate) struct MoveRecord {
    pub(crate) place: Place,
    pub(crate) moved_span: Span,
    pub(crate) cause: MoveCause,
    pub(crate) moved_type: String,
    /// Whether this move reached the current state around a loop's back edge.
    /// A loop-carried move is usually its own use -- the same expression, one
    /// iteration later -- so a diagnostic has to say which iteration it means.
    pub(crate) from_previous_iteration: bool,
}

/// A move identified by where it happened, ignoring how it was reached.
pub(crate) type FingerprintKey = (Place, String, u32, u32);

pub(crate) fn fingerprint_key(record: &MoveRecord) -> FingerprintKey {
    (
        record.place.clone(),
        record.moved_span.filename.clone(),
        record.moved_span.line,
        record.moved_span.col,
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MoveCause {
    Other,
    ByValueReceiver,
}

/// What introducing a binding displaced, so that leaving its scope restores the
/// binding it shadowed rather than deleting both.
#[derive(Debug, Clone)]
struct ShadowedBinding {
    name: String,
    moved: Option<Vec<MoveRecord>>,
    binding_type: Option<Type>,
    borrowed_array: bool,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct FlowState {
    moved: HashMap<String, Vec<MoveRecord>>,
    binding_types: HashMap<String, Type>,
    /// Loop bindings sourced from a `T[]` borrowed view. They may be read or
    /// borrowed, but a non-Copy value cannot be moved out through the binding.
    borrowed_array_bindings: HashSet<String>,
    scopes: Vec<Vec<ShadowedBinding>>,
    /// Whether the path walked so far has left the enclosing loop iteration
    /// through `break`, `continue`, or `return`. Only the loop driver reads it,
    /// to decide whether this state reaches the back edge; it is not part of the
    /// moved-state lattice and `union_from` deliberately leaves it alone.
    pub(crate) diverged: bool,
}

impl FlowState {
    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(Vec::new());
    }

    pub(crate) fn pop_scope(&mut self) {
        let Some(bindings) = self.scopes.pop() else {
            return;
        };
        // Reverse order: a name bound twice in one scope displaced the earlier
        // binding, so unwinding forwards would leave the *later* shadow's empty
        // state in place instead of what the scope was entered with.
        for shadowed in bindings.into_iter().rev() {
            let ShadowedBinding {
                name,
                moved,
                binding_type,
                borrowed_array,
            } = shadowed;
            match moved {
                Some(records) => self.moved.insert(name.clone(), records),
                None => self.moved.remove(&name),
            };
            match binding_type {
                Some(ty) => self.binding_types.insert(name.clone(), ty),
                None => self.binding_types.remove(&name),
            };
            if borrowed_array {
                self.borrowed_array_bindings.insert(name);
            } else {
                self.borrowed_array_bindings.remove(&name);
            }
        }
    }

    /// Introduce `name`, remembering whatever it displaced so leaving the scope
    /// can put it back.
    ///
    /// Clearing the moved state is right for the *new* binding -- it is a fresh
    /// value. What was wrong before #343 was that the clear also destroyed the
    /// shadowed binding's state, which `pop_scope` then had nothing to restore:
    /// a shadow inside a loop body laundered a carried move.
    pub(crate) fn bind(&mut self, name: &str) {
        let displaced = ShadowedBinding {
            name: name.to_string(),
            moved: self.moved.remove(name),
            binding_type: self.binding_types.remove(name),
            borrowed_array: self.borrowed_array_bindings.remove(name),
        };
        if let Some(scope) = self.scopes.last_mut() {
            scope.push(displaced);
        }
    }

    pub(crate) fn bind_typed(&mut self, name: &str, ty: &Type) {
        self.bind(name);
        self.binding_types.insert(name.to_string(), ty.clone());
    }

    pub(crate) fn bind_borrowed_array_element(&mut self, name: &str, ty: &Type) {
        self.bind_typed(name, ty);
        self.borrowed_array_bindings.insert(name.to_string());
    }

    pub(crate) fn is_borrowed_array_element(&self, place: &Place) -> bool {
        self.borrowed_array_bindings.contains(place.root())
    }

    pub(crate) fn binding_type(&self, name: &str) -> Option<&Type> {
        self.binding_types.get(name)
    }

    /// The depth-1 field / tuple projections currently moved directly out of
    /// `root` (`root.name`, `root.0`). RFC-0137 row narrowing (metel-core#858)
    /// reads these to compute a binding's residual type — a deeper move
    /// (`root.a.b`) does not narrow `root`'s own row, since a record-typed field
    /// moves as a unit.
    pub(crate) fn moved_shallow_projections(&self, root: &str) -> Vec<Projection> {
        let Some(records) = self.moved.get(root) else {
            return Vec::new();
        };
        records
            .iter()
            .filter(|record| record.place.projections().len() == 1)
            .map(|record| record.place.projections()[0].clone())
            .collect()
    }

    pub(crate) fn record_move(
        &mut self,
        place: Place,
        moved_span: Span,
        cause: MoveCause,
        moved_type: String,
    ) {
        let root = place.root().to_string();
        let records = self.moved.entry(root).or_default();
        if place.projections().is_empty() {
            // Moving the whole value subsumes every partial move of it.
            records.clear();
        } else {
            records.retain(|existing| !place.is_prefix_of(&existing.place));
        }
        records.push(MoveRecord {
            place,
            moved_span,
            cause,
            moved_type,
            from_previous_iteration: false,
        });
    }

    /// Mark every move that was not already in `before` as loop-carried. Called
    /// once a loop has folded its back edge into the state the body starts from:
    /// anything new got there by completing an iteration.
    pub(crate) fn mark_moves_as_carried_from(&mut self, before: &Self) {
        let previous = before.moved_fingerprint();
        for record in self.moved.values_mut().flatten() {
            if !previous.contains(&fingerprint_key(record)) {
                record.from_previous_iteration = true;
            }
        }
    }

    pub(crate) fn moved_record_for_descendant_use(&self, place: &Place) -> Option<&MoveRecord> {
        self.moved
            .get(place.root())?
            .iter()
            .find(|record| record.place.is_prefix_of(place))
    }

    pub(crate) fn moved_record_for_whole_use(&self, place: &Place) -> Option<&MoveRecord> {
        self.moved
            .get(place.root())?
            .iter()
            .find(|record| record.place.is_prefix_of(place) || place.is_prefix_of(&record.place))
    }

    /// A write makes its target valid again, along with everything under it:
    /// assigning `p.f` replaces `p.f.g` too.
    ///
    /// A move of a strict *ancestor* survives -- replacing one field does not
    /// revive the whole value -- but that case is already an error at the write
    /// itself, which needs a reachable base.
    pub(crate) fn reinitialize(&mut self, place: &Place) {
        let Some(records) = self.moved.get_mut(place.root()) else {
            return;
        };
        records.retain(|record| !place.is_prefix_of(&record.place));
        if records.is_empty() {
            self.moved.remove(place.root());
        }
    }

    pub(crate) fn union_from(&mut self, other: &Self) {
        for (root, incoming) in &other.moved {
            let records = self.moved.entry(root.clone()).or_default();
            for record in incoming {
                if records.iter().any(|existing| {
                    existing.place == record.place && existing.moved_span == record.moved_span
                }) {
                    continue;
                }
                if record.place.projections().is_empty() {
                    records.clear();
                    records.push(record.clone());
                    continue;
                }
                if records
                    .iter()
                    .any(|existing| existing.place.projections().is_empty())
                {
                    continue;
                }
                records.push(record.clone());
            }
        }
    }

    /// This state as it would be after leaving every scope opened since the
    /// stack was `depth` deep -- what a `break` or `continue` out of a loop body
    /// actually hands to its destination.
    pub(crate) fn unwound_to(&self, depth: usize) -> Self {
        let mut unwound = self.clone();
        while unwound.scopes.len() > depth {
            unwound.pop_scope();
        }
        unwound
    }

    pub(crate) fn scope_depth(&self) -> usize {
        self.scopes.len()
    }

    /// Discard all moved-field tracking, keeping scopes/binding-types/
    /// borrowed-array state as-is. Used by an `if`/`match` join to start the
    /// joined state's `moved` map empty before accumulating each live arm's
    /// contribution into it via `union_from`.
    pub(crate) fn clear_moved(&mut self) {
        self.moved.clear();
    }

    /// A stable, order-independent summary of the moved state, for deciding when
    /// a loop's entry state has stopped growing. `moved` is a `HashMap` of
    /// `Vec`s, so comparing it directly would compare iteration order too.
    pub(crate) fn moved_fingerprint(&self) -> BTreeSet<FingerprintKey> {
        self.moved.values().flatten().map(fingerprint_key).collect()
    }
}
