//! Construction by call: `Type(args)` and `Enum::Variant(args)` (RFC-0100 section 1, metel-core#1860).
//!
//! A construction call is not a function call: it builds the struct or enum variant directly, which is
//! what the compiler-synthesized default of `Construct` does (RFC-0100 section 7; RFC-0114 is not in the
//! v0.16.0 stage). The inference, construction and abstract-body passes therefore rewrite it, once the
//! callee is known to name a type, into the struct literal they already check, so field visibility
//! (T0009), generic inference, moves and drops are the literal's, unchanged.
//!
//! Arguments bind to fields exactly as they bind to a function's parameters (RFC-0223): positional in
//! declaration order, keyword by name, every field supplied (T0039, T0040, T0004). The rewritten literal
//! lists its fields in written order, so arguments evaluate left to right as written (dynamics-1).

use crate::data::ast::{Expr, SPREAD_ARG, Span, TypeExpr};
use crate::data::error::{MetelError, TypeErrorCode};
use crate::identity::symbols::SymbolId;

use super::keyword_binding::{ParamSlot, bind_arguments};

/// What a construction call's callee names, read from its syntax alone: the callee decides whether it
/// is a type only once the registry is consulted.
pub(super) enum Target<'a> {
    Struct(&'a str),
    Variant(&'a str, &'a str),
}

/// The type or variant a callee would name, if written as a plain name or an `Enum::Variant` path.
pub(super) fn target_of(callee: &Expr) -> Option<Target<'_>> {
    match callee {
        Expr::Ident(name, _) => Some(Target::Struct(name)),
        Expr::Path(segments, _, _) => match segments.as_slice() {
            [enum_name, variant] => Some(Target::Variant(enum_name, variant)),
            _ => None,
        },
        // A module-qualified or aliased type, which path normalization resolved to the declaration
        // it names and spelled by its own name.
        Expr::ResolvedPath {
            resolved,
            symbol_id: Some(_),
            ..
        } => match resolved.split_once("::") {
            Some((enum_name, variant)) => Some(Target::Variant(enum_name, variant)),
            None => Some(Target::Struct(resolved)),
        },
        _ => None,
    }
}

/// Whether a name reads as a variant or type by the naming convention (RFC-0101: capitalized), so a call
/// of `Enum::Name(field = ..)` that names no known variant is a construction of an unknown one, and its
/// literal reports it, instead of a call of a missing function.
pub(super) fn is_variant_like(name: &str) -> bool {
    name.chars().next().is_some_and(char::is_uppercase)
}

/// The declaration a normalized callee names, when path normalization resolved it.
pub(super) fn callee_symbol(callee: &Expr) -> Option<SymbolId> {
    match callee {
        Expr::ResolvedPath { symbol_id, .. } => *symbol_id,
        _ => None,
    }
}

/// The struct literal a construction call is equivalent to. `names` are the declared field names of the
/// type or variant, in declaration order.
///
/// # Errors
/// The binder's T0039, T0040 and T0004; T0039 for a spread that is not alone; `not_implemented` for a
/// spread of anything but a binding, whose value would be read once per field.
pub(super) fn literal_for(
    callee: &Expr,
    type_args: &[TypeExpr],
    args: &[Expr],
    span: &Span,
    names: &[String],
) -> Result<Expr, MetelError> {
    let path: Vec<String> = match callee {
        Expr::Ident(name, _) => vec![name.clone()],
        Expr::Path(segments, _, _) => segments.clone(),
        Expr::ResolvedPath { resolved, .. } => resolved.split("::").map(str::to_string).collect(),
        _ => {
            return Err(MetelError::internal(
                "construction call: callee is not a type name",
            ));
        }
    };
    let display = path.join("::");
    // No declared shape (an enum or variant the registry does not know): pass the keyword names through
    // so the literal's own checks report the unknown variant or enum.
    let fields = if names.is_empty()
        && args
            .iter()
            .all(|a| matches!(a, Expr::NamedArg { name, .. } if name != SPREAD_ARG))
        && !args.is_empty()
    {
        args.iter()
            .filter_map(|arg| match arg {
                Expr::NamedArg { name, value, .. } => Some((name.clone(), (**value).clone())),
                _ => None,
            })
            .collect()
    } else {
        match args {
            [
                Expr::NamedArg {
                    name,
                    value,
                    span: arg_span,
                },
            ] if name == SPREAD_ARG => spread_fields(&display, value, arg_span, names)?,
            _ => {
                if let Some(Expr::NamedArg { span: arg_span, .. }) = args
                    .iter()
                    .find(|arg| matches!(arg, Expr::NamedArg { name, .. } if name == SPREAD_ARG))
                {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0039,
                        format!(
                            "a spread argument builds `{display}` from a record and must be its only argument"
                        ),
                        arg_span,
                    ));
                }
                let slots: Vec<ParamSlot<'_>> =
                    names.iter().map(|name| ParamSlot { name }).collect();
                let binding = bind_arguments(&display, &slots, args, span)?;
                // Written order: the literal evaluates its fields in the order listed.
                let mut written: Vec<(usize, String, Expr)> = binding
                    .arg_for_param
                    .iter()
                    .enumerate()
                    .map(|(param, &index)| {
                        let value = match &args[index] {
                            Expr::NamedArg { value, .. } => (**value).clone(),
                            positional => positional.clone(),
                        };
                        (index, names[param].clone(), value)
                    })
                    .collect();
                written.sort_by_key(|(index, ..)| *index);
                written
                    .into_iter()
                    .map(|(_, name, value)| (name, value))
                    .collect()
            }
        }
    };
    // A call's own span starts at its `(`; the literal it stands for spans the whole `Type(args)`, so a
    // diagnostic points at the type.
    let mut literal_span = callee.span().clone();
    literal_span.end = span.end;
    let literal = Expr::StructLiteral {
        path: path.clone(),
        fields,
        symbol_id: callee_symbol(callee),
        span: literal_span.clone(),
    };
    if type_args.is_empty() || path.len() != 1 {
        return Ok(literal);
    }
    // Explicit type arguments, `Pair::<i64>(1, 2)`, constrain the built type by ascription.
    Ok(Expr::Ascribe {
        expr: Box::new(literal),
        ann: TypeExpr::Named(path[0].clone(), type_args.to_vec(), span.clone().into()),
        span: literal_span,
    })
}

/// `Type(..r)`: every field read from the binding `r`, which a record of exactly the type's row supplies.
fn spread_fields(
    display: &str,
    value: &Expr,
    span: &Span,
    names: &[String],
) -> Result<Vec<(String, Expr)>, MetelError> {
    let Expr::Ident(..) = value else {
        return Err(MetelError::not_implemented(format!(
            "`{display}(..value)` where the spread is not a plain binding (RFC-0100 section 7, metel-core#1860)"
        )));
    };
    Ok(names
        .iter()
        .map(|name| {
            (
                name.clone(),
                Expr::FieldAccess {
                    object: Box::new(value.clone()),
                    field: name.clone(),
                    span: span.clone(),
                },
            )
        })
        .collect())
}
