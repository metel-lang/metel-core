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
use crate::identity::{MethodOwner, MethodParams};
use crate::pipeline::type_checking::type_engine::OverloadEntry;

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

    /// When the reorder is observable (dynamics-1: arguments evaluate strictly as written), for each
    /// written argument the declaration position it fills; `None` when the call is already in
    /// declaration order or at most one argument is not a literal.
    pub(super) fn written_to_param(&self, args: &[Expr]) -> Option<Vec<usize>> {
        let non_literal = args
            .iter()
            .filter(|arg| !matches!(unwrap_keyword(arg), Expr::Literal(..)))
            .count();
        (!self.is_identity() && non_literal > 1).then(|| {
            let mut order = vec![0; args.len()];
            for (param, &written) in self.arg_for_param.iter().enumerate() {
                order[written] = param;
            }
            order
        })
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

/// What a keyword-argument call's callee tells the binder.
pub(super) enum CalleeNames<'a> {
    /// A declared function: its value-parameter names, receiver excluded.
    Declared(&'a [String]),
    /// No declared names are known: a closure or other function value, whose type carries none.
    Value,
}

/// Whether any written argument is a keyword argument.
pub(super) fn has_keyword(args: &[Expr]) -> bool {
    args.iter().any(|arg| matches!(arg, Expr::NamedArg { .. }))
}

/// A keyword call rewritten to the positional call it is equivalent to.
pub(super) struct Positional {
    /// The argument expressions in the callee's declaration order.
    pub args: Vec<Expr>,
    /// When reordering changes evaluation order (dynamics-1: arguments evaluate strictly as written),
    /// for each *written* argument the declaration position it fills; construction then evaluates each
    /// into a temporary in written order. `None` when the written order is unobservable: the call is
    /// already in declaration order, or at most one argument is not a literal.
    pub written_to_param: Option<Vec<usize>>,
}

/// Rewrite the arguments of a call that names some of them into the positional argument list of the
/// callee's declaration order, so the rest of each pass types and constructs an ordinary call.
///
/// # Errors
/// T0041 for a callee with no declared names, and the binder's errors otherwise.
pub(super) fn to_positional(
    callee: &str,
    names: &CalleeNames<'_>,
    args: &[Expr],
    call_span: &Span,
) -> Result<Positional, MetelError> {
    let CalleeNames::Declared(names) = names else {
        let keyword = args.iter().find_map(|arg| match arg {
            Expr::NamedArg { span, .. } => Some(span),
            _ => None,
        });
        return Err(MetelError::type_error(
            TypeErrorCode::T0041,
            format!(
                "`{callee}` is called through a function value, which takes positional arguments \
                 only because a function type carries no parameter names"
            ),
            keyword.unwrap_or(call_span),
        ));
    };
    let params: Vec<ParamSlot<'_>> = names.iter().map(|name| ParamSlot { name }).collect();
    let binding = bind_arguments(callee, &params, args, call_span)?;
    let written_to_param = binding.written_to_param(args);
    Ok(Positional {
        args: binding
            .arg_for_param
            .iter()
            .map(|&index| unwrap_keyword(&args[index]).clone())
            .collect(),
        written_to_param,
    })
}

/// The method names a keyword call binds against, found by the method's name.
///
/// A method call resolves its receiver only while checking, so the names are looked up by method name
/// across every declared aspect and impl method. They are usable when every candidate declares the
/// same names, which RFC-0223 legality-4 guarantees for an aspect method and which conventional
/// inherent methods share; differing candidates need receiver-directed binding (metel-core#1858).
fn method_names<'a>(
    method: &str,
    candidates: &'a [MethodParams],
    head: Option<&str>,
) -> Result<&'a [String], MetelError> {
    let narrowed: Vec<&MethodParams> = match head {
        Some(head) => candidates
            .iter()
            .filter(|c| matches!(&c.owner, MethodOwner::Impl { target: Some(t), .. } if t == head))
            .collect(),
        None => Vec::new(),
    };
    let pool: Vec<&MethodParams> = if narrowed.is_empty() {
        candidates.iter().collect()
    } else {
        narrowed
    };
    let Some(first) = pool.first() else {
        return Err(MetelError::not_implemented(format!(
            "keyword arguments on `{method}`, whose declaration has no recorded parameter names \
             (RFC-0223, metel-core#1858)"
        )));
    };
    if pool.iter().all(|c| c.names == first.names) {
        Ok(&first.names)
    } else {
        Err(MetelError::not_implemented(format!(
            "keyword arguments on `{method}`: methods of that name declare different parameter \
             names, and binding by receiver type is pending (RFC-0223, metel-core#1858)"
        )))
    }
}

/// The positional argument list a keyword-argument call is equivalent to, shared by the inference and
/// construction passes so they bind identically.
///
/// `names` are the declared parameter names of the function the callee resolves to, when it resolves
/// to one (an overloaded name is selected by [`select_overload`] instead); `methods` are every declared method of the callee's name, for a path callee `Type::name`
/// (an associated function). Anything else, a constructor or a variant, is not yet
/// bound (metel-core#1858).
///
/// # Errors
/// As [`to_positional`], plus `not_implemented` for a callee not yet bound.
pub(super) fn positional_for_call(
    callee: &Expr,
    args: &[Expr],
    span: &Span,
    names: Option<&[String]>,
    methods: &std::collections::HashMap<String, Vec<MethodParams>>,
) -> Result<Positional, MetelError> {
    if let Expr::Path(segments, _, _) = callee
        && let [.., owner, name] = segments.as_slice()
    {
        let candidates = methods.get(name).map_or(&[][..], Vec::as_slice);
        let names = method_names(name, candidates, Some(owner))?;
        return to_positional(
            &format!("{owner}::{name}"),
            &CalleeNames::Declared(names),
            args,
            span,
        );
    }
    let Some(name) = super::overload::callee_name(callee) else {
        return Err(MetelError::not_implemented(
            "keyword arguments on a call whose callee is not a plain function name or a path \
             (RFC-0223, metel-core#1858)",
        ));
    };
    match names {
        Some(names) => to_positional(name, &CalleeNames::Declared(names), args, span),
        None => to_positional(name, &CalleeNames::Value, args, span),
    }
}

/// The overload candidate a keyword call selects (RFC-0223 legality-5), with how its arguments bind.
///
/// A candidate takes the call only if the call's keywords name some of its own parameters and the
/// arguments fill every slot; the resulting per-slot argument types must then equal the candidate's
/// parameter types. `arg_types` are the written arguments' types, in written order. `Ok(None)` means
/// some candidate binds by name but none by type, so the caller reports the ordinary no-match error.
///
/// # Errors
/// T0039 when no candidate binds the call by name, listing each candidate's parameters.
pub(super) fn select_overload<'a>(
    name: &str,
    entries: &'a [OverloadEntry],
    args: &[Expr],
    arg_types: &[crate::data::types::Type],
    span: &Span,
) -> Result<Option<(&'a OverloadEntry, Binding)>, MetelError> {
    let mut any_binds = false;
    for entry in entries {
        let params: Vec<ParamSlot<'_>> = entry
            .param_names
            .iter()
            .map(|name| ParamSlot { name })
            .collect();
        let Ok(binding) = bind_arguments(name, &params, args, span) else {
            continue;
        };
        any_binds = true;
        let types_match = binding
            .arg_for_param
            .iter()
            .zip(&entry.params)
            .all(|(&written, param)| arg_types.get(written) == Some(param));
        if types_match {
            return Ok(Some((entry, binding)));
        }
    }
    if any_binds {
        return Ok(None);
    }
    let candidates: Vec<String> = entries
        .iter()
        .map(|entry| format!("({})", entry.param_names.join(", ")))
        .collect();
    Err(MetelError::type_error(
        TypeErrorCode::T0039,
        format!(
            "no overload of `{name}` takes these keyword arguments; its candidates declare {}",
            candidates.join(", ")
        ),
        span,
    ))
}

/// The positional call a keyword call to the already selected overload `entry` is equivalent to.
///
/// # Errors
/// The binder's errors, which cannot occur for a selection [`select_overload`] made.
pub(super) fn positional_for_entry(
    name: &str,
    entry: &OverloadEntry,
    args: &[Expr],
    span: &Span,
) -> Result<Positional, MetelError> {
    to_positional(name, &CalleeNames::Declared(&entry.param_names), args, span)
}

/// Whether the methods named `method` declare different parameter names, so binding a keyword call
/// needs the receiver's type to choose among them.
pub(super) fn method_needs_receiver(
    method: &str,
    methods: &std::collections::HashMap<String, Vec<MethodParams>>,
) -> bool {
    let candidates = methods.get(method).map_or(&[][..], Vec::as_slice);
    candidates
        .first()
        .is_some_and(|first| candidates.iter().any(|c| c.names != first.names))
}

/// The head type name of a receiver type, for narrowing a method's candidates: a named type's name, or
/// a primitive's spelling. `None` for any other shape (an array, a tuple, a function), which no
/// nominal impl target names.
pub(super) fn receiver_head(named: Option<&str>, spelling: &str) -> Option<String> {
    named.map(str::to_string).or_else(|| {
        spelling
            .chars()
            .all(|c| c.is_alphanumeric() || c == '_')
            .then(|| spelling.to_string())
    })
}

/// The positional argument list a keyword method call `receiver.method(..)` is equivalent to.
///
/// # Errors
/// As [`to_positional`], plus `not_implemented` when the method's names are not unambiguous.
pub(super) fn positional_for_method(
    method: &str,
    args: &[Expr],
    span: &Span,
    methods: &std::collections::HashMap<String, Vec<MethodParams>>,
    receiver_head: Option<&str>,
) -> Result<Positional, MetelError> {
    let candidates = methods.get(method).map_or(&[][..], Vec::as_slice);
    let names = method_names(method, candidates, receiver_head)?;
    to_positional(method, &CalleeNames::Declared(names), args, span)
}

fn unwrap_keyword(arg: &Expr) -> &Expr {
    match arg {
        Expr::NamedArg { value, .. } => value,
        other => other,
    }
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
