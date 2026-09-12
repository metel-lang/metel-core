use std::cell::RefCell;
use std::rc::Rc;

use crate::ast::Span;
use crate::error::{MetelError, RuntimeErrorCode};

use super::{
    attach_stack, eval_block, pop_frame, profiler_enter, profiler_exit, push_frame, read_path,
    type_of, ClosureBody, ClosureValue, Environment, RuntimeCallable, RuntimeRegistry, Signal,
    Value,
};

/// Bind a method call's receiver and positional arguments into `call_env`,
/// keyed additionally by each parameter's [`LocalId`] in the id-indexed frame
/// when identity allocation stamped one (metel-core#1052b).
fn bind_method_params(
    call_env: &mut Environment,
    closure: &ClosureValue,
    receiver: ReceiverBinding,
    args: &[Value],
) {
    if !closure.params.is_empty() {
        let id = closure.param_ids.first().copied().flatten();
        match receiver {
            ReceiverBinding::Value(value) => call_env.define_binding(id, value),
            ReceiverBinding::Shared(cell) => call_env.define_binding_rc(id, cell),
        }
    }
    for (i, val) in args.iter().enumerate() {
        let id = closure.param_ids.get(i + 1).copied().flatten();
        call_env.define_binding(id, val.clone());
    }
}

/// How the receiver is bound into the callee's environment.
/// `Value` → cloned (value/&self receivers); `Shared` → Rc shared (mut self / &mut self).
/// See ADR-0036 for the dispatch design.
pub(super) enum ReceiverBinding {
    Value(Value),
    Shared(Rc<RefCell<Value>>),
}

/// Extract the named-type key for a receiver's runtime type, peeling pointer
/// layers (a `&self` / `&mut self` receiver arrives as a pointer to the value).
/// Used to look up a generic method's scheme in the registry's method env.
fn receiver_type_name(ty: &crate::types::Type) -> Option<&str> {
    use crate::types::Type;
    match ty {
        Type::Named(name, ..) => Some(name.as_str()),
        Type::Reference(inner) | Type::MutReference(inner) => receiver_type_name(inner),
        _ => None,
    }
}

fn call_runtime_callable(
    callable: RuntimeCallable,
    args: &[Value],
    static_arg_tys: Option<&[crate::types::Type]>,
    expected_ret: Option<&crate::types::Type>,
    span: &Span,
    runtime: &RuntimeRegistry,
) -> Result<Signal, MetelError> {
    match callable {
        RuntimeCallable::Intrinsic { label, fun } => {
            profiler_enter(&label);
            let result = fun(args, span).map(Signal::Value).map_err(attach_stack);
            profiler_exit();
            result
        }
        RuntimeCallable::Closure(rc) => {
            let is_mutating = rc.call_mutation == crate::types::CallMutation::Mutating;
            if is_mutating && rc.in_call.replace(true) {
                return Err(attach_stack(MetelError::panic(
                    RuntimeErrorCode::R0015,
                    "re-entrant call to a mutating closure",
                    span,
                )));
            }
            let closure = rc.as_ref();
            let fn_name = closure
                .name
                .clone()
                .unwrap_or_else(|| "<closure>".to_string());
            push_frame(fn_name, span.clone());
            let mut call_env = closure.captured.clone();
            call_env.push_scope();
            for (i, val) in args.iter().enumerate() {
                let id = closure.param_ids.get(i).copied().flatten();
                call_env.define_binding(id, val.clone());
            }
            let result = match &closure.body {
                ClosureBody::Typed(b) => eval_block(b, &mut call_env, runtime),
                ClosureBody::Untyped(b) => {
                    let scheme_and_ctx = closure
                        .name
                        .as_deref()
                        .zip(closure.type_ctx.as_ref())
                        .and_then(|(name, type_ctx)| {
                            type_ctx.scheme_env.get(name).map(|s| (s, type_ctx))
                        });
                    match scheme_and_ctx {
                        Some((scheme, type_ctx)) => {
                            // metel-core#286: prefer the argument types recorded at the
                            // call site. Re-deriving them from runtime values loses
                            // whatever the value cannot carry -- an empty array has no
                            // element to sample, so `value_to_type` yields
                            // `Array(Never)`, and `Never` coerces without ever *pinning*
                            // a type variable, leaving a nested generic call in this body
                            // unresolvable. The static types were known during
                            // construction and are exact.
                            let arg_types: Vec<_> = args
                                .iter()
                                .enumerate()
                                .map(|(i, v)| {
                                    let rt = type_of::value_to_type(v, &type_ctx.registry, span);
                                    match static_arg_tys.and_then(|t| t.get(i)) {
                                        Some(st) => type_of::refine_with_static(&rt, st),
                                        None => rt,
                                    }
                                })
                                .collect();
                            let tb = crate::typechecker::construct_generic_body(
                                scheme, &closure.params, &arg_types, b, span, type_ctx, expected_ret
                            )?;
                            eval_block(&tb, &mut call_env, runtime)
                        }
                        None => Err(attach_stack(MetelError::panic(
                            crate::error::RuntimeErrorCode::R0002,
                            format!("generic closure `{}` has no type context — construction-at-call-time unavailable",
                                closure.name.as_deref().unwrap_or("<anonymous>")),
                            span,
                        ))),
                    }
                }
            };
            let result = result.map_err(attach_stack);
            pop_frame();
            if is_mutating {
                rc.in_call.set(false);
            }
            let sig = result?;
            Ok(match sig {
                Signal::Return(v) => Signal::Value(v),
                other => other,
            })
        }
    }
}

/// Dispatch a function call to a callable runtime value.
/// Converts `Signal::Return` at the function boundary.
pub(super) fn call_function(
    func: Value,
    args: &[Value],
    static_arg_tys: Option<&[crate::types::Type]>,
    expected_ret: Option<&crate::types::Type>,
    span: &Span,
    runtime: &RuntimeRegistry,
) -> Result<Signal, MetelError> {
    // Auto-deref: calling through a function pointer transparently unwraps one pointer layer.
    let func = match func {
        Value::Reference(rc) | Value::MutReference(rc) => rc.borrow().clone(),
        Value::FieldReference { root, path } | Value::MutFieldReference { root, path } => {
            read_path(&root.borrow(), &path, span)?
        }
        other => other,
    };
    match func {
        Value::Callable(callable) => {
            call_runtime_callable(callable, args, static_arg_tys, expected_ret, span, runtime)
        }

        Value::Unit => Err(attach_stack(MetelError::panic(
            RuntimeErrorCode::R0002,
            "call: target is Unit, not a function",
            span,
        ))),

        other => Err(attach_stack(MetelError::panic(
            RuntimeErrorCode::R0010,
            format!(
                "call: expected a closure or builtin, got {:?}",
                std::mem::discriminant(&other)
            ),
            span,
        ))),
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn call_method_function(
    func: RuntimeCallable,
    receiver: ReceiverBinding,
    mut args: Vec<Value>,
    static_arg_tys: Option<&[crate::types::Type]>,
    static_receiver_ty: Option<&crate::types::Type>,
    expected_ret: Option<&crate::types::Type>,
    span: &Span,
    runtime: &RuntimeRegistry,
) -> Result<Signal, MetelError> {
    match func {
        RuntimeCallable::Closure(rc) => {
            let closure = (*rc).clone();
            let fn_name = closure
                .name
                .clone()
                .unwrap_or_else(|| "<closure>".to_string());
            push_frame(fn_name, span.clone());
            // Capture the receiver's runtime type before it is moved into the
            // call environment. Generic method bodies are constructed at call
            // time (ClosureBody::Untyped), and the method's TypeScheme lives in
            // the registry's method env keyed by the receiver's type name — so
            // we need that name plus the receiver type as the first arg type
            // (the scheme's signature includes `self`).
            // `receiver` is moved a few lines below (into `call_env`), so its type must be
            // captured now, before `closure.body` is even matched on — meaning a real
            // registry isn't always available yet here (only `ClosureBody::Untyped` with a
            // present `type_ctx` has one; `Typed` bodies never consult `receiver_type` at
            // all, so an empty fallback registry is harmless for them).
            let default_registry = crate::typeinference::TypeDefinitionRegistry::new();
            let registry_ref = closure
                .type_ctx
                .as_deref()
                .map_or(&default_registry, |tc| &tc.registry);
            let receiver_type = match &receiver {
                ReceiverBinding::Value(value) => type_of::value_to_type(value, registry_ref, span),
                ReceiverBinding::Shared(cell) => {
                    type_of::value_to_type(&cell.borrow(), registry_ref, span)
                }
            };
            let mut call_env = closure.captured.clone();
            call_env.push_scope();
            bind_method_params(&mut call_env, &closure, receiver, &args);
            let result = match &closure.body {
                ClosureBody::Typed(b) => eval_block(b, &mut call_env, runtime),
                ClosureBody::Untyped(b) => {
                    // Resolve the method's scheme. A generic method is registered
                    // in the registry's method env under (receiver type, method
                    // name); fall back to the flat scheme env for the rare case a
                    // free generic closure reaches this path.
                    let resolved = closure
                        .name
                        .as_deref()
                        .zip(closure.type_ctx.as_ref())
                        .and_then(|(name, type_ctx)| {
                            let method_scheme = match &receiver_type {
                                crate::types::Type::Array(_) => type_ctx
                                    .registry
                                    .array_method_scheme_for(name)
                                    .map(|(s, _)| s),
                                _ => receiver_type_name(&receiver_type).and_then(|tn| {
                                    type_ctx
                                        .registry
                                        .method_scheme_for(&type_ctx.current_module, tn, name)
                                        .map(|(s, _)| s)
                                }),
                            };
                            method_scheme
                                .or_else(|| type_ctx.scheme_env.get(name))
                                .map(|scheme| (scheme, type_ctx))
                        });
                    match resolved {
                        Some((scheme, type_ctx)) => {
                            // The scheme's signature includes `self`, so the arg
                            // types must lead with the receiver type to stay
                            // positionally aligned with `closure.params`.
                            // metel-core#286, as above. The receiver stays
                            // runtime-derived: dynamic dispatch depends on the runtime
                            // type being at least as precise as the static one, which is
                            // a separate question from the arguments.
                            let mut arg_types: Vec<_> = vec![match static_receiver_ty {
                                Some(st) => type_of::refine_with_static(&receiver_type, st),
                                None => receiver_type.clone(),
                            }];
                            arg_types.extend(args.iter().enumerate().map(|(i, v)| {
                                let rt = type_of::value_to_type(v, &type_ctx.registry, span);
                                match static_arg_tys.and_then(|t| t.get(i)) {
                                    Some(st) => type_of::refine_with_static(&rt, st),
                                    None => rt,
                                }
                            }));
                            let tb = crate::typechecker::construct_generic_body(
                                scheme, &closure.params, &arg_types, b, span, type_ctx, expected_ret
                            )?;
                            eval_block(&tb, &mut call_env, runtime)
                        }
                        None => Err(attach_stack(MetelError::panic(
                            crate::error::RuntimeErrorCode::R0002,
                            format!("generic method `{}` has no type context — construction-at-call-time unavailable",
                                closure.name.as_deref().unwrap_or("<anonymous>")),
                            span,
                        ))),
                    }
                }
            };
            let result = result.map_err(attach_stack);
            pop_frame();
            let sig = result?;
            Ok(match sig {
                Signal::Return(v) => Signal::Value(v),
                other => other,
            })
        }
        callable @ RuntimeCallable::Intrinsic { .. } => {
            let receiver_value = match receiver {
                ReceiverBinding::Value(value) => value,
                ReceiverBinding::Shared(cell) => cell.borrow().clone(),
            };
            args.insert(0, receiver_value);
            call_runtime_callable(callable, &args, static_arg_tys, expected_ret, span, runtime)
        }
    }
}
