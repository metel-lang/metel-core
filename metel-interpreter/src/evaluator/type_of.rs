use std::collections::HashMap;

use super::Value;
use crate::ast::Span;
use crate::typeinference::TypeDefinitionRegistry;
use crate::types::Type;

/// Derive a concrete `Type` from a runtime `Value`.
///
/// Used during construction-at-call-time for generic function bodies: the caller
/// maps each argument value to its type, then uses those types to instantiate the
/// function's `TypeScheme` and build the `Substitution` for `ConstructCtx`.
///
/// Limitations:
/// - Closures: the concrete function type is not stored in the runtime callable, so
///   `Fun([], Box::new(Unit))` is returned as a placeholder.
///
/// Generic structs/enums (issue #267): the runtime value itself carries no type
/// argument info (`Wrapper { value: 5 }`'s only intrinsic type tag is bare
/// `Named("Wrapper", [])`), so `registry` and `span` are used to recover them —
/// see `typechecker::infer_named_type_args`'s own doc comment for the mechanism.
pub(super) fn value_to_type(value: &Value, registry: &TypeDefinitionRegistry, span: &Span) -> Type {
    let go = |v: &Value| value_to_type(v, registry, span);
    match value {
        Value::I64(_) => Type::I64,
        Value::F64(_) => Type::F64,
        Value::Char(_) => Type::Char,
        Value::Boolean(_) => Type::Boolean,
        Value::Str(_) => Type::Str,
        Value::Unit => Type::Unit,
        Value::I8(_) => Type::I8,
        Value::I16(_) => Type::I16,
        Value::I32(_) => Type::I32,
        Value::U8(_) => Type::U8,
        Value::U16(_) => Type::U16,
        Value::U32(_) => Type::U32,
        Value::U64(_) => Type::U64,
        Value::F32(_) => Type::F32,
        Value::Tuple(elems) => Type::Tuple(elems.iter().map(go).collect()),
        Value::Record { fields } => {
            let mut items: Vec<(String, Type)> =
                fields.iter().map(|(k, v)| (k.clone(), go(v))).collect();
            items.sort_by(|(left, _), (right, _)| left.cmp(right));
            Type::Record(items)
        }
        Value::Array(rc) => {
            let borrowed = rc.borrow();
            // Empty: no element to sample. `Never` (not `Unit`) -- it already
            // coerces to any type and dispatches dynamically wherever construction
            // consults it (see construction.rs's method-call handling), so a
            // generic method body reconstructed at call time for this empty
            // array can still construct branches that reference the element type
            // even though they're provably unreachable at runtime for this call
            // (issue #271).
            let elem_ty = borrowed.first().map_or(Type::Never, go);
            Type::Array(Box::new(elem_ty))
        }
        Value::Struct {
            name,
            fields,
            type_id,
        } => {
            let field_types: HashMap<String, Type> =
                fields.iter().map(|(k, v)| (k.clone(), go(v))).collect();
            let args =
                crate::typechecker::infer_named_type_args(name, None, &field_types, registry, span);
            // metel-core#1129: carry the value's own resolved declaration
            // identity, when it has one, instead of only the bare name --
            // this is what lets a bound check on this type find the *actual*
            // impl rather than guessing by name across the whole program.
            Type::Named(name.clone(), args, crate::types::NominalId(*type_id))
        }
        Value::Enum {
            name,
            variant,
            fields,
            type_id,
        } => {
            let field_types: HashMap<String, Type> =
                fields.iter().map(|(k, v)| (k.clone(), go(v))).collect();
            let args = crate::typechecker::infer_named_type_args(
                name,
                Some(variant),
                &field_types,
                registry,
                span,
            );
            Type::Named(name.clone(), args, crate::types::NominalId(*type_id))
        }
        Value::Callable(callable) => match callable {
            super::RuntimeCallable::Closure(rc) => rc
                .fun_type
                .clone()
                .unwrap_or_else(|| crate::types::default_fun_type(vec![], Type::Unit)),
            super::RuntimeCallable::Intrinsic { .. } => {
                crate::types::default_fun_type(vec![], Type::Unit)
            }
        },
        Value::Reference(rc) => Type::Reference(Box::new(go(&rc.borrow()))),
        Value::MutReference(rc) => Type::MutReference(Box::new(go(&rc.borrow()))),
        Value::FieldReference { root, path } | Value::MutFieldReference { root, path } => {
            // Approximate: read the leaf type from the current root value.
            let root_val = root.borrow();
            let mut cur_type = go(&root_val);
            for seg in path {
                cur_type = match (seg, cur_type) {
                    (super::PathSegment::Field(f), Type::Named(name, ..)) => {
                        // A synthetic "Outer.field" phantom name, not a real
                        // declared type -- no identity to carry.
                        Type::Named(format!("{name}.{f}"), vec![], crate::types::NominalId::NONE)
                    }
                    (super::PathSegment::Field(f), Type::Record(fields)) => fields
                        .into_iter()
                        .find(|(name, _)| name == f)
                        .map_or(Type::Unit, |(_, ty)| ty),
                    (super::PathSegment::TupleIndex(_) | super::PathSegment::ArrayIndex(_), t) => t,
                    _ => Type::Unit,
                };
            }
            if matches!(value, Value::FieldReference { .. }) {
                Type::Reference(Box::new(cur_type))
            } else {
                Type::MutReference(Box::new(cur_type))
            }
        }
        // Erasure must round-trip through generic-body reconstruction (#286):
        // a `dyn Aspect` value's type stays `dyn Aspect`, never the concrete
        // type underneath `data` — that's the entire point of the fat pointer.
        Value::DynAspect {
            aspect_name,
            type_args,
            ..
        } => Type::Dyn {
            aspect: aspect_name.clone(),
            type_args: type_args.clone(),
        },
    }
}

/// Fill in what a runtime-derived type could not know, from the type recorded at the call
/// site (metel-core#286).
///
/// The runtime type stays authoritative — it is what dispatch already used, and for a
/// value that carries more information than its static type it is the more precise of the
/// two. The exception is where the runtime type is *missing* information rather than
/// disagreeing: `value_to_type` samples a collection's first element to learn its element
/// type, and an empty collection has none, so it yields `Never` there. `Never` coerces to
/// anything without ever binding a type variable, so a generic body constructed against it
/// cannot resolve a parameter that comes only from the element type.
///
/// So: keep the runtime type everywhere, except take the static type wherever the runtime
/// one says `Never` and the static one says something concrete. Narrow by construction —
/// no case that works today changes, because `Never` is precisely the marker of an
/// unsampled element.
#[must_use]
pub fn refine_with_static(runtime: &Type, static_ty: &Type) -> Type {
    match (runtime, static_ty) {
        (Type::Never, other) => other.clone(),
        (Type::Array(r), Type::Array(s)) => Type::Array(Box::new(refine_with_static(r, s))),
        (Type::SizedArray(r, n), Type::SizedArray(s, _)) => {
            Type::SizedArray(Box::new(refine_with_static(r, s)), *n)
        }
        (Type::Reference(r), Type::Reference(s)) => {
            Type::Reference(Box::new(refine_with_static(r, s)))
        }
        (Type::MutReference(r), Type::MutReference(s)) => {
            Type::MutReference(Box::new(refine_with_static(r, s)))
        }
        (Type::Tuple(r), Type::Tuple(s)) if r.len() == s.len() => Type::Tuple(
            r.iter()
                .zip(s.iter())
                .map(|(a, b)| refine_with_static(a, b))
                .collect(),
        ),
        (Type::Named(rn, ra, rid), Type::Named(sn, sa, sid))
            if rn == sn && ra.len() == sa.len() =>
        {
            Type::Named(
                rn.clone(),
                ra.iter()
                    .zip(sa.iter())
                    .map(|(a, b)| refine_with_static(a, b))
                    .collect(),
                // The runtime type is authoritative (see this fn's own doc);
                // its identity wins when it has one, same as everywhere else
                // here. Only take the static side's id when the runtime type
                // couldn't resolve one at all.
                crate::types::NominalId(rid.get().or_else(|| sid.get())),
            )
        }
        (Type::Fun(rp, rr, _, _, _), Type::Fun(sp, sr, call_mult, use_mult, call_mutation))
            if rp.len() == sp.len() =>
        {
            Type::Fun(
                rp.iter()
                    .zip(sp.iter())
                    .map(|(a, b)| refine_with_static(a, b))
                    .collect(),
                Box::new(refine_with_static(rr, sr)),
                *call_mult,
                *use_mult,
                *call_mutation,
            )
        }
        _ => runtime.clone(),
    }
}
