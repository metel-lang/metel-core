//! Call-syntax construction (RFC-0100 sections 2, 5 and 7): which calls construct, and the brace
//! literal each one is equivalent to.
//!
//! Inference, construction and the abstract bodies move checking reads each decide for themselves
//! whether a call constructs — a generic body is reconstructed at run time with no inference facts
//! to consult — so what they share lives here: the shapes a construction callee takes after path
//! normalization, and the brace literal a decided construction is handled as. Every pass then types
//! or analyses that literal exactly as it would the brace form, which is what keeps the two forms
//! from disagreeing about identity, field checks, evaluation order and ownership.

use super::keyword_binding::{ConstructionFields, construction_fields};
use crate::data::ast::{Expr, Span};
use crate::data::error::MetelError;
use crate::identity::symbols::SymbolId;

/// What a call's callee looks like after path normalization, before any name is looked up.
pub(super) enum CalleeShape<'a> {
    /// `T(..)` or an unqualified `V(..)`; or a module-qualified `m::T(..)` the path normalizer
    /// resolved, with the identity it stamped.
    Name {
        name: &'a str,
        symbol_id: Option<SymbolId>,
    },
    /// `E::V(..)` as written, or a module-qualified path the normalizer reduced to it — in which
    /// case it recorded the type the module prefix names against `path_span`.
    Member {
        type_name: &'a str,
        member: &'a str,
        path_span: &'a Span,
    },
    /// `m::E::V(..)` naming a unit variant, which the normalizer already turned into that
    /// variant's literal, carrying the enum's identity.
    UnitVariant {
        enum_name: &'a str,
        variant: &'a str,
        symbol_id: Option<SymbolId>,
    },
}

/// The shape of `callee`, or `None` for a callee that can never construct (a field, a call result).
pub(super) fn callee_shape(callee: &Expr) -> Option<CalleeShape<'_>> {
    match callee {
        Expr::Ident(name, _) => Some(CalleeShape::Name {
            name,
            symbol_id: None,
        }),
        // `resolved` is the local name the normalizer bound the path to, which need not be the
        // type's declared name; the last written segment is, and the identity says which type.
        Expr::ResolvedPath {
            resolved,
            symbol_id,
            original,
            ..
        } => Some(CalleeShape::Name {
            name: original.last().unwrap_or(resolved),
            symbol_id: *symbol_id,
        }),
        Expr::Path(segments, _, span) => match segments.as_slice() {
            [type_name, member] => Some(CalleeShape::Member {
                type_name,
                member,
                path_span: span,
            }),
            _ => None,
        },
        Expr::StructLiteral {
            path,
            fields,
            symbol_id,
            ..
        } if fields.is_empty() => match path.as_slice() {
            [enum_name, variant] => Some(CalleeShape::UnitVariant {
                enum_name,
                variant,
                symbol_id: *symbol_id,
            }),
            _ => None,
        },
        _ => None,
    }
}

/// How a construction call's positional arguments are named.
#[derive(Debug, Clone)]
pub(super) enum Fields {
    /// The struct's or variant's declared fields, in declaration order.
    Declared(Vec<String>),
    /// The enum has no such variant; the brace literal reports it.
    Unknown,
    /// An unqualified variant, resolved against the expected type later: keyword arguments only.
    Unqualified,
}

/// A call decided to construct, as the brace literal it is equivalent to.
#[derive(Debug, Clone)]
pub(super) struct Construction {
    /// `[T]` for a struct, `[E, V]` for a qualified variant, `[V]` for an unqualified one.
    pub path: Vec<String>,
    /// The constructed type's identity when the path normalizer resolved it; `None` leaves the
    /// literal to resolve its path exactly as the brace form written in the same place would.
    pub symbol_id: Option<SymbolId>,
    pub fields: Fields,
}

impl Construction {
    /// The brace literal this call is equivalent to.
    ///
    /// # Errors
    /// The argument errors of [`construction_fields`].
    ///
    /// The literal spans the callee through the closing parenthesis — what the brace form spans —
    /// so a diagnostic about the constructed value points where it would for that form.
    pub(super) fn literal(
        &self,
        callee: &Expr,
        args: &[Expr],
        span: &Span,
    ) -> Result<Expr, MetelError> {
        let name = self.path.last().map_or("", String::as_str);
        let fields = match &self.fields {
            Fields::Declared(names) => ConstructionFields::Declared(names),
            Fields::Unknown => ConstructionFields::Unknown,
            Fields::Unqualified => ConstructionFields::Unqualified,
        };
        let head = callee.span();
        let literal_span = Span {
            start: head.start.min(span.start),
            end: span.end,
            filename: span.filename.clone(),
            line: head.line,
            col: head.col,
        };
        Ok(Expr::StructLiteral {
            path: self.path.clone(),
            fields: construction_fields(name, &fields, args, span)?,
            symbol_id: self.symbol_id,
            span: literal_span,
        })
    }

    /// The name of the constructed type — the struct, or the enum of a qualified variant — which a
    /// turbofish's type arguments apply to. `None` for an unqualified variant.
    pub(super) fn type_name(&self) -> Option<&str> {
        match (self.path.as_slice(), &self.fields) {
            (_, Fields::Unqualified) => None,
            ([name] | [name, _], _) => Some(name),
            _ => None,
        }
    }
}
