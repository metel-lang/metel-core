//! RFC-0008 §3: whether an aspect can be used as `dyn Aspect`.
//!
//! Three rules, checked per method:
//!
//! 1. **Receiver rule** — the method's first parameter must be `self: &Self` or
//!    `self: &var Self` (the third form, `self: @[r] Self`, doesn't parse yet --
//!    RFC-0141's syntax is what would write it -- so there is nothing to check for
//!    it, narrowing what's checked, not what's correct). A bare by-move receiver,
//!    or no receiver at all, is not object-safe. `Self` appearing anywhere else in
//!    the signature (a non-receiver parameter, the return type) is also not
//!    object-safe.
//! 2. **No generic methods** — a method with its own type parameters is simply
//!    excluded from the vtable; this does not by itself disqualify the aspect.
//! 3. **No associated types in signature** — a method whose signature references
//!    one of the aspect's own associated types (`Self::Target`, or the bare-name
//!    sugar RFC-0082 §1.2 allows inside an aspect body) is not object-safe.
//!
//! Rules 1 and 3 are checked only against non-generic methods (rule 2 already
//! excludes a generic method from the vtable, so its shape doesn't matter to the
//! rest of the aspect's object safety).
//!
//! Aspect declarations are never lowered by `lower_projections_in_program`
//! (`inference.rs`'s `lower_projections_in_decl` falls through to `other => other`
//! for `Decl::Aspect`) -- so unlike an ordinary function signature, `Self::Item` or
//! bare `Item` sugar inside an aspect's own method declarations survives as raw,
//! unlowered `TypeExpr::Named` nodes (`"Self::Item"` or `"Item"` as a literal
//! string) by the time this check runs. `type_expr_violation` checks both forms
//! directly rather than assuming a `TypeExpr::Projection` node exists.

use std::collections::HashSet;

use crate::data::ast::{AspectMethod, ReceiverKind, TypeExpr};

/// Why an aspect fails RFC-0008 §3's object-safety check.
pub(super) struct ObjectSafetyViolation {
    pub method_name: String,
    pub reason: String,
}

/// Check every non-generic method of `methods` against RFC-0008 §3's three rules.
/// `assoc_type_names` is the aspect's own declared associated-type names (rule 3).
pub(super) fn check_object_safe(
    methods: &[AspectMethod],
    assoc_type_names: &HashSet<&str>,
) -> Result<(), ObjectSafetyViolation> {
    for method in methods {
        // Rule 2: a method with its own generics is excluded from the vtable --
        // not a disqualifier, and its shape is irrelevant to rules 1/3.
        if !method.generics.is_empty() {
            continue;
        }

        // Rule 1: receiver shape. `reason` never repeats the method name -- the
        // caller (`projections.rs`) already prefixes every diagnostic with
        // `Aspect::method`.
        match method.params.first().and_then(|p| p.receiver.as_ref()) {
            Some(ReceiverKind::Ref | ReceiverKind::RefMut) => {}
            Some(ReceiverKind::Value) => {
                return Err(ObjectSafetyViolation {
                    method_name: method.name.clone(),
                    reason: "takes self by value".to_string(),
                });
            }
            None => {
                return Err(ObjectSafetyViolation {
                    method_name: method.name.clone(),
                    reason: "has no `self` receiver (associated functions cannot be dispatched through a vtable)".to_string(),
                });
            }
        }

        // Rule 1 (continued) + rule 3: walk every non-receiver parameter and the
        // return type for `Self` in non-receiver position, or a reference to one
        // of the aspect's own associated types.
        for param in method.params.iter().skip(1) {
            if let Some(ty) = &param.type_ann
                && let Some(reason) = type_expr_violation(ty, assoc_type_names)
            {
                return Err(ObjectSafetyViolation {
                    method_name: method.name.clone(),
                    reason: format!("parameter `{}` {reason}", param.name),
                });
            }
        }
        if let Some(ret) = &method.return_type {
            // Special-cased so the common case (`fun clone(&self) -> Self`) reads
            // exactly as RFC-0008 §3's own worked example does ("Clone::clone
            // returns Self"), not the generic nested-mention wording.
            let is_bare_self =
                matches!(ret, TypeExpr::Named(n, args) if n == "Self" && args.is_empty());
            if is_bare_self {
                return Err(ObjectSafetyViolation {
                    method_name: method.name.clone(),
                    reason: "returns Self".to_string(),
                });
            }
            if let Some(reason) = type_expr_violation(ret, assoc_type_names) {
                return Err(ObjectSafetyViolation {
                    method_name: method.name.clone(),
                    reason: format!("{reason} in its return type"),
                });
            }
        }
    }
    Ok(())
}

/// Recursively check `te` for a rule-1 or rule-3 violation, returning a
/// human-readable reason fragment (`"returns Self"`, `"references Deref::Target"`)
/// on the first one found.
fn type_expr_violation(te: &TypeExpr, assoc_type_names: &HashSet<&str>) -> Option<String> {
    match te {
        TypeExpr::Named(name, args) => {
            if name == "Self" {
                return Some("mentions Self".to_string());
            }
            // Unlowered `Self::AssocName` (a single dotted `type_path`, not yet
            // split by `lower_projections_in_type` -- see module doc comment).
            if let Some((base, assoc)) = name.split_once("::")
                && base == "Self"
                && assoc_type_names.contains(assoc)
            {
                return Some(format!("references Self::{assoc}"));
            }
            // RFC-0082 §1.2 bare-name sugar for one of this aspect's own
            // associated types.
            if args.is_empty() && assoc_type_names.contains(name.as_str()) {
                return Some(format!("references the associated type {name}"));
            }
            args.iter()
                .find_map(|a| type_expr_violation(a, assoc_type_names))
        }
        TypeExpr::Projection {
            base, assoc_name, ..
        } => {
            if matches!(base.as_ref(), TypeExpr::Named(n, _) if n == "Self")
                && assoc_type_names.contains(assoc_name.as_str())
            {
                return Some(format!("references Self::{assoc_name}"));
            }
            type_expr_violation(base, assoc_type_names)
        }
        TypeExpr::Tuple(items) => items
            .iter()
            .find_map(|t| type_expr_violation(t, assoc_type_names)),
        TypeExpr::Record(fields) => fields
            .iter()
            .find_map(|(_, t)| type_expr_violation(t, assoc_type_names)),
        TypeExpr::Array(inner)
        | TypeExpr::SizedArray(inner, _)
        | TypeExpr::Reference(inner)
        | TypeExpr::MutReference(inner) => type_expr_violation(inner, assoc_type_names),
        TypeExpr::Fun {
            params,
            return_type: ret,
            ..
        } => params
            .iter()
            .find_map(|p| type_expr_violation(p, assoc_type_names))
            .or_else(|| {
                ret.as_deref()
                    .and_then(|r| type_expr_violation(r, assoc_type_names))
            }),
        TypeExpr::ImplAspect { bound, .. } | TypeExpr::DynAspect { bound, .. } => {
            type_expr_violation(bound, assoc_type_names)
        }
        // A record projection or a bare unit type can't mention `Self` or an
        // associated type -- `RecordProjection`'s path names a struct, and unit
        // carries no type at all.
        TypeExpr::RecordProjection { .. } | TypeExpr::Unit => None,
    }
}
