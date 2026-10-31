//! Keep enclosing facts separate from method-owned parameter spellings.

use super::{Bound, BoundHead, FunDecl, HashMap, ImplBlock, TypeExpr};

pub(super) fn enclosing_definition(method: &FunDecl, implementation: &ImplBlock) -> ImplBlock {
    let mut implementation = implementation.clone();
    let replacements: HashMap<_, _> = implementation
        .generics
        .iter()
        .enumerate()
        .filter(|(_, generic)| method.generics.iter().any(|own| own.name == generic.name))
        .map(|(index, generic)| {
            (
                generic.name.clone(),
                format!("$impl{index}_{}", generic.name),
            )
        })
        .collect();
    for generic in &mut implementation.generics {
        rename_name(&mut generic.name, &replacements);
        rename_bounds(&mut generic.bounds, &replacements);
    }
    rename_type(&mut implementation.target_type, &replacements);
    for argument in &mut implementation.aspect_type_args {
        rename_type(argument, &replacements);
    }
    for definition in &mut implementation.assoc_type_defs {
        rename_type(&mut definition.ty, &replacements);
    }
    if let Some(clause) = &mut implementation.where_clause {
        for constraint in &mut clause.constraints {
            rename_name(&mut constraint.name, &replacements);
            rename_bounds(&mut constraint.bounds, &replacements);
        }
        for equation in &mut clause.row_equations {
            rename_name(&mut equation.var, &replacements);
            rename_tail(&mut equation.tail, &replacements);
            rename_fields(&mut equation.fields, &replacements);
        }
        for constraint in &mut clause.field_wise {
            rename_name(&mut constraint.var, &replacements);
            rename_bounds(&mut constraint.bounds, &replacements);
        }
    }
    implementation
}

fn rename_name(name: &mut String, replacements: &HashMap<String, String>) {
    if let Some(replacement) = replacements.get(name) {
        *name = replacement.clone();
    }
}

fn rename_tail(tail: &mut super::RowTail, replacements: &HashMap<String, String>) {
    if let Some(name) = &mut tail.var {
        rename_name(name, replacements);
    }
}

fn rename_fields(fields: &mut [(String, TypeExpr)], replacements: &HashMap<String, String>) {
    for (_, ty) in fields {
        rename_type(ty, replacements);
    }
}

fn rename_bounds(bounds: &mut [Bound], replacements: &HashMap<String, String>) {
    for bound in bounds {
        match &mut bound.head {
            BoundHead::Aspect(ty) => rename_aspect_arguments(ty, replacements),
            BoundHead::Row(row) => {
                for field in &mut row.fields {
                    if let Some(ty) = &mut field.ty {
                        rename_type(ty, replacements);
                    }
                }
            }
        }
        rename_fields(&mut bound.assoc_bindings, replacements);
    }
}

fn rename_type(ty: &mut TypeExpr, replacements: &HashMap<String, String>) {
    match ty {
        TypeExpr::Named(name, arguments, _) => {
            rename_name(name, replacements);
            for argument in arguments {
                rename_type(argument, replacements);
            }
        }
        TypeExpr::Tuple(items) => {
            for item in items {
                rename_type(item, replacements);
            }
        }
        TypeExpr::Record(fields) => rename_fields(fields, replacements),
        TypeExpr::OpenRecord(fields, tail) => {
            rename_fields(fields, replacements);
            rename_tail(tail, replacements);
        }
        TypeExpr::Array(inner)
        | TypeExpr::SizedArray(inner, _)
        | TypeExpr::Reference(inner)
        | TypeExpr::MutReference(inner)
        | TypeExpr::Projection { base: inner, .. }
        // RFC-0180: the payload is an ordinary record type.
        | TypeExpr::RowArgLiteral(inner) => rename_type(inner, replacements),
        TypeExpr::ImplAspect { bound, .. } | TypeExpr::DynAspect { bound, .. } => {
            rename_aspect_arguments(bound, replacements);
        }
        TypeExpr::Fun {
            params,
            return_type,
            ..
        } => {
            for parameter in params {
                rename_type(parameter, replacements);
            }
            if let Some(result) = return_type {
                rename_type(result, replacements);
            }
        }
        TypeExpr::RecordProjection { path, .. } => {
            if let [name] = path.as_mut_slice() {
                rename_name(name, replacements);
            }
        }
        TypeExpr::OpenRecordProjection { path, tail, .. } => {
            if let [name] = path.as_mut_slice() {
                rename_name(name, replacements);
            }
            rename_tail(tail, replacements);
        }
        TypeExpr::RowArg(tail) => rename_tail(tail, replacements),
        TypeExpr::Unit => {}
    }
}

fn rename_aspect_arguments(ty: &mut TypeExpr, replacements: &HashMap<String, String>) {
    // Aspect heads resolve in the aspect namespace, even when a parameter has
    // the same spelling. Only their argument types refer to parameter binders.
    if let TypeExpr::Named(_, arguments, _) = ty {
        for argument in arguments {
            rename_type(argument, replacements);
        }
    }
}
