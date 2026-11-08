//! Binding of a call's arguments to the callee's parameters (RFC-0223 section 2, metel-core#1858).
//!
//! One function, [`bind_arguments`], is the only place that decides which written argument fills which
//! parameter, so the inference and construction passes cannot disagree. It is pure: it takes the written
//! argument shapes and the callee's declared parameters and returns, for each parameter in declaration
//! order, the index of the written argument that fills it.
//!
//! The rules (`spec.functions.keyword-arguments.legality-1`):
//! - positional arguments bind the leading parameters in order, and every positional argument precedes
//!   the first keyword argument (T0040 otherwise);
//! - a keyword binds the parameter of that name, which must exist and be free (T0039 otherwise);
//! - every parameter is bound exactly once, and a missing or extra argument is an arity error (T0004).

use crate::data::ast::{Expr, Span};
use crate::data::error::{MetelError, TypeErrorCode};

/// One declared parameter of the callee, in declaration order, excluding the receiver.
#[derive(Debug, Clone, Copy)]
pub(super) struct ParamSlot<'a> {
    pub name: &'a str,
}

/// For each parameter in declaration order, the index into the written argument list that fills it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Binding {
    pub arg_for_param: Vec<usize>,
}

impl Binding {
    /// Whether the written order already is the declaration order, so no reordering is needed.
    pub(super) fn is_identity(&self) -> bool {
        self.arg_for_param.iter().enumerate().all(|(i, &a)| i == a)
    }
}

/// Bind `args` to `params`. `callee` names the function in messages.
///
/// # Errors
/// T0040 for a positional argument after a keyword, T0039 for a keyword that names no free parameter,
/// T0004 when a parameter is left unbound or there are more positional arguments than parameters.
pub(super) fn bind_arguments(
    callee: &str,
    params: &[ParamSlot<'_>],
    args: &[Expr],
    call_span: &Span,
) -> Result<Binding, MetelError> {
    let mut slot_arg: Vec<Option<usize>> = vec![None; params.len()];
    let mut seen_keyword: Option<&str> = None;
    let mut next_positional = 0usize;
    for (index, arg) in args.iter().enumerate() {
        match arg {
            Expr::NamedArg { name, span, .. } => {
                seen_keyword = Some(name);
                let Some(position) = params.iter().position(|p| p.name == name) else {
                    return Err(unknown_keyword(callee, name, params, span));
                };
                if slot_arg[position].is_some() {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0039,
                        format!(
                            "`{callee}` parameter `{name}` is already bound; a keyword argument \
                             may bind only a parameter no earlier argument bound"
                        ),
                        span,
                    ));
                }
                slot_arg[position] = Some(index);
            }
            positional => {
                if let Some(keyword) = seen_keyword {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0040,
                        format!(
                            "a positional argument cannot follow the keyword argument `{keyword}`; \
                             write every positional argument before the first keyword argument"
                        ),
                        positional.span(),
                    ));
                }
                if next_positional >= params.len() {
                    return Err(arity(callee, params.len(), args.len(), &[], call_span));
                }
                slot_arg[next_positional] = Some(index);
                next_positional += 1;
            }
        }
    }
    let unbound: Vec<&str> = params
        .iter()
        .zip(&slot_arg)
        .filter(|(_, slot)| slot.is_none())
        .map(|(p, _)| p.name)
        .collect();
    if !unbound.is_empty() {
        return Err(arity(callee, params.len(), args.len(), &unbound, call_span));
    }
    Ok(Binding {
        arg_for_param: slot_arg.into_iter().flatten().collect(),
    })
}

fn unknown_keyword(callee: &str, name: &str, params: &[ParamSlot<'_>], span: &Span) -> MetelError {
    let names: Vec<String> = params.iter().map(|p| format!("`{}`", p.name)).collect();
    let listing = if names.is_empty() {
        "it takes no parameters".to_string()
    } else {
        format!("its parameters are {}", names.join(", "))
    };
    MetelError::type_error(
        TypeErrorCode::T0039,
        format!("`{callee}` has no parameter named `{name}`; {listing}"),
        span,
    )
}

fn arity(callee: &str, expected: usize, got: usize, unbound: &[&str], span: &Span) -> MetelError {
    let detail = if unbound.is_empty() {
        String::new()
    } else {
        let names: Vec<String> = unbound.iter().map(|n| format!("`{n}`")).collect();
        format!("; unbound: {}", names.join(", "))
    };
    MetelError::type_error(
        TypeErrorCode::T0004,
        format!("`{callee}` takes {expected} argument(s), got {got}{detail}"),
        span,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::ast::Literal;

    fn span() -> Span {
        Span::new(0, 0, "t.mtl")
    }

    fn pos() -> Expr {
        Expr::Literal(Literal::Int(1), span())
    }

    fn kw(name: &str) -> Expr {
        Expr::NamedArg {
            name: name.to_string(),
            value: Box::new(pos()),
            span: span(),
        }
    }

    fn slots<'a>(names: &[&'a str]) -> Vec<ParamSlot<'a>> {
        names.iter().map(|&name| ParamSlot { name }).collect()
    }

    fn code(err: &MetelError) -> TypeErrorCode {
        match err {
            MetelError::TypeError { code, .. } => *code,
            other => panic!("expected a type error, found {other:?}"),
        }
    }

    fn bind(params: &[&str], args: &[Expr]) -> Result<Binding, MetelError> {
        bind_arguments("f", &slots(params), args, &span())
    }

    #[test]
    fn a_purely_positional_call_binds_in_order() {
        let b = bind(&["a", "b"], &[pos(), pos()]).unwrap();
        assert_eq!(b.arg_for_param, vec![0, 1]);
        assert!(b.is_identity());
    }

    #[test]
    fn keywords_bind_the_remaining_parameters_by_name() {
        let b = bind(
            &["host", "port", "timeout"],
            &[pos(), kw("timeout"), kw("port")],
        )
        .unwrap();
        assert_eq!(b.arg_for_param, vec![0, 2, 1]);
        assert!(!b.is_identity());
    }

    #[test]
    fn keywords_in_declaration_order_are_the_identity() {
        let b = bind(&["a", "b"], &[kw("a"), kw("b")]).unwrap();
        assert!(b.is_identity());
    }

    #[test]
    fn an_unknown_keyword_is_t0039_and_lists_the_parameters() {
        let err = bind(&["a", "b"], &[pos(), kw("c")]).unwrap_err();
        assert_eq!(code(&err), TypeErrorCode::T0039);
        assert!(err.to_string().contains("`a`, `b`"), "{err}");
    }

    #[test]
    fn a_keyword_naming_a_positionally_bound_parameter_is_t0039() {
        let err = bind(&["a", "b"], &[pos(), kw("a")]).unwrap_err();
        assert_eq!(code(&err), TypeErrorCode::T0039);
    }

    #[test]
    fn a_repeated_keyword_is_t0039() {
        let err = bind(&["a", "b"], &[kw("a"), kw("a")]).unwrap_err();
        assert_eq!(code(&err), TypeErrorCode::T0039);
    }

    #[test]
    fn a_positional_argument_after_a_keyword_is_t0040() {
        let err = bind(&["a", "b"], &[kw("a"), pos()]).unwrap_err();
        assert_eq!(code(&err), TypeErrorCode::T0040);
    }

    #[test]
    fn a_missing_argument_is_t0004_naming_the_unbound_parameter() {
        let err = bind(&["a", "b", "c"], &[pos(), kw("c")]).unwrap_err();
        assert_eq!(code(&err), TypeErrorCode::T0004);
        assert!(err.to_string().contains("`b`"), "{err}");
    }

    #[test]
    fn an_extra_positional_argument_is_t0004() {
        let err = bind(&["a"], &[pos(), pos()]).unwrap_err();
        assert_eq!(code(&err), TypeErrorCode::T0004);
    }

    #[test]
    fn a_call_with_no_parameters_and_a_keyword_is_t0039() {
        let err = bind(&[], &[kw("a")]).unwrap_err();
        assert_eq!(code(&err), TypeErrorCode::T0039);
        assert!(err.to_string().contains("takes no parameters"), "{err}");
    }
}
