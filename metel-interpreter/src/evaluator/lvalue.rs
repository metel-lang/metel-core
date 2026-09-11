use std::collections::HashMap;

use crate::ast::{BinOp, Span};
use crate::error::{MetelError, RuntimeErrorCode};
use crate::typed_ast::TypedPlace;

use super::{eval_expr, Environment, PathSegment, RuntimeRegistry, Signal, Value};

/// Resolve the root `Rc<RefCell<Value>>` for a projected assign target and collect
/// the full `PathSegment` sequence to navigate within it.
///
/// Handles three root forms:
/// - `Ident(x)` — looks up `x` in the environment; auto-derefs one `&mut` level.
/// - `Deref(ptr_expr)` — evaluates `ptr_expr` and extracts the `MutReference` inner Rc.
/// - Projections (`Field`, `Tuple`) recurse into `object`, then append a path segment.
pub(super) fn resolve_place_assign_root(
    place: &TypedPlace,
    env: &mut Environment,
    runtime: &RuntimeRegistry,
    span: &Span,
) -> Result<(std::rc::Rc<std::cell::RefCell<Value>>, Vec<PathSegment>), MetelError> {
    fn walk(
        place: &TypedPlace,
        path: &mut Vec<PathSegment>,
        env: &mut Environment,
        runtime: &RuntimeRegistry,
        span: &Span,
    ) -> Result<std::rc::Rc<std::cell::RefCell<Value>>, MetelError> {
        match place {
            TypedPlace::Ident(name, binding, ident_span) => {
                // A top-level `let` / `var`'s live global slot cell, or a
                // local's frame cell, by identity (metel-core#1052b). No
                // name-map fallback remains (metel-core#1054).
                let id_cell = match binding {
                    Some(crate::identity::BindingId::Global(sym)) => {
                        runtime.global_slot(*sym).cloned()
                    }
                    Some(crate::identity::BindingId::Local(id)) => env.get_local_rc(*id),
                    None => None,
                };
                let rc = id_cell.ok_or_else(|| {
                    MetelError::panic(
                        RuntimeErrorCode::R0003,
                        format!("assign: `{name}` not found"),
                        ident_span,
                    )
                })?;
                // Auto-deref: if the binding holds a &mut reference, follow it.
                let inner = {
                    let v = rc.borrow();
                    if let Value::MutReference(inner_rc) = &*v {
                        Some(inner_rc.clone())
                    } else {
                        None
                    }
                };
                Ok(inner.unwrap_or(rc))
            }
            TypedPlace::Deref {
                object,
                span: tspan,
            } => {
                let ptr = eval_expr(object, env, runtime)?.into_value();
                match ptr {
                    Value::MutReference(inner_rc) => Ok(inner_rc),
                    _ => Err(MetelError::panic(
                        RuntimeErrorCode::R0003,
                        "assign: not a &var reference",
                        tspan,
                    )),
                }
            }
            TypedPlace::Field { object, field, .. } => {
                let root_rc = walk(object, path, env, runtime, span)?;
                path.push(PathSegment::Field(field.clone()));
                Ok(root_rc)
            }
            TypedPlace::Tuple { object, index, .. } => {
                let root_rc = walk(object, path, env, runtime, span)?;
                path.push(PathSegment::TupleIndex(*index));
                Ok(root_rc)
            }
            TypedPlace::Index { .. } => Err(MetelError::panic(
                RuntimeErrorCode::R0003,
                "assign: unsupported receiver form",
                span,
            )),
        }
    }
    let mut path = Vec::new();
    let root_rc = walk(place, &mut path, env, runtime, span)?;
    Ok((root_rc, path))
}

/// Evaluate a `TypedPlace` to the `Value` it currently holds.
/// For arrays the returned `Value::Array(rc)` shares the same `Rc` as the binding,
/// so callers can mutate through it without a round-trip through the environment.
// Keep this as one dispatch table so the assign-place cases stay visibly aligned.
#[allow(clippy::too_many_lines)]
pub(super) fn eval_typed_place_value(
    place: &TypedPlace,
    env: &mut Environment,
    runtime: &RuntimeRegistry,
) -> Result<Value, MetelError> {
    match place {
        TypedPlace::Ident(name, binding, ident_span) => {
            match binding {
                Some(crate::identity::BindingId::Global(sym)) => {
                    if let Some(cell) = runtime.global_slot(*sym) {
                        return Ok(cell.borrow().clone());
                    }
                }
                Some(crate::identity::BindingId::Local(id)) => {
                    if let Some(v) = env.get_local(*id) {
                        return Ok(v);
                    }
                }
                None => {}
            }
            Err(MetelError::panic(
                RuntimeErrorCode::R0003,
                format!("assign: `{name}` not found"),
                ident_span,
            ))
        }
        TypedPlace::Deref {
            object,
            span: tspan,
        } => {
            let ptr = eval_expr(object, env, runtime)?.into_value();
            match ptr {
                Value::Reference(rc) | Value::MutReference(rc) => Ok(rc.borrow().clone()),
                _ => Err(MetelError::panic(
                    RuntimeErrorCode::R0003,
                    "assign: not a pointer",
                    tspan,
                )),
            }
        }
        TypedPlace::Field {
            object,
            field,
            span: tspan,
        } => {
            let parent = eval_typed_place_value(object, env, runtime)?;
            match parent {
                Value::Record { fields }
                | Value::Struct { fields, .. }
                | Value::Enum { fields, .. } => fields.get(field).cloned().ok_or_else(|| {
                    MetelError::panic(
                        RuntimeErrorCode::R0008,
                        format!("field access: no field `{field}`"),
                        tspan,
                    )
                }),
                _ => Err(MetelError::internal(format!(
                    "field `{field}`: receiver is not a record/struct/enum"
                ))),
            }
        }
        TypedPlace::Tuple {
            object,
            index,
            span: tspan,
        } => {
            let parent = eval_typed_place_value(object, env, runtime)?;
            match parent {
                // R0005: believed genuinely unreachable via well-typed source --
                // `index` is a source-literal tuple index the typechecker already
                // validates against the tuple type's known arity before this ever
                // runs (metel-core#987, #986's own audit). Kept as a defensive
                // fallback rather than `unreachable!()`/an outright panic: a
                // clean diagnostic here is strictly better than UB or a Rust
                // panic if some untried construct ever proves this wrong.
                Value::Tuple(elems) => elems.get(*index).cloned().ok_or_else(|| {
                    MetelError::panic(
                        RuntimeErrorCode::R0005,
                        format!("tuple index {index} out of bounds"),
                        tspan,
                    )
                }),
                _ => Err(MetelError::internal(format!(
                    "tuple `{index}`: receiver is not a tuple"
                ))),
            }
        }
        TypedPlace::Index {
            object,
            index,
            span: tspan,
        } => {
            let arr = eval_typed_place_value(object, env, runtime)?;
            let idx = eval_expr(index, env, runtime)?.into_value();
            let i: i64 = match idx {
                Value::U64(u) => {
                    if u > i64::MAX as u64 {
                        return Err(MetelError::panic(
                            RuntimeErrorCode::R0004,
                            format!("index {u} out of bounds"),
                            tspan,
                        ));
                    }
                    u as i64
                }
                _ => {
                    return Err(MetelError::internal(
                        "index: expected u64 index (typechecker should have caught this)",
                    ))
                }
            };
            match arr {
                Value::Array(rc) => {
                    let len = rc.borrow().len() as i64;
                    if i < 0 || i >= len {
                        return Err(MetelError::panic(
                            RuntimeErrorCode::R0004,
                            format!("index {i} out of bounds (len {len})"),
                            tspan,
                        ));
                    }
                    Ok(rc.borrow()[i as usize].clone())
                }
                _ => Err(MetelError::internal("index: receiver is not an Array")),
            }
        }
    }
}

pub(super) fn apply_assign_op(
    op: &crate::ast::AssignOp,
    cur: Value,
    rhs: Value,
    span: &Span,
) -> Result<Value, MetelError> {
    use crate::ast::AssignOp;
    let fake_binop = match op {
        AssignOp::AddAssign => BinOp::Add,
        AssignOp::SubAssign => BinOp::Sub,
        AssignOp::MulAssign => BinOp::Mul,
        AssignOp::DivAssign => BinOp::Div,
        AssignOp::RemAssign => BinOp::Rem,
        AssignOp::Assign => unreachable!("plain Assign handled before apply_assign_op"),
    };
    eval_binop(&fake_binop, cur, rhs, span).map(Signal::into_value)
}

// Metel's `==`/`!=` on f32/f64 are specified as exact IEEE-754 comparison, not
// epsilon-tolerant — this is the language's own equality semantics, not a bug.
#[allow(clippy::float_cmp)]
// Exhaustive match over every BinOp/Value combination; splitting it up would
// scatter one coherent dispatch table across many small functions with no
// real gain in clarity.
#[allow(clippy::too_many_lines)]
pub(super) fn eval_binop(
    op: &BinOp,
    lv: Value,
    rv: Value,
    span: &Span,
) -> Result<Signal, MetelError> {
    let result = match (op, lv, rv) {
        // ── Int (i64) arithmetic — overflow panics ─────────────────────────────
        (BinOp::Add, Value::I64(a), Value::I64(b)) =>
            Value::I64(a.checked_add(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "integer overflow", span))?),
        (BinOp::Sub, Value::I64(a), Value::I64(b)) =>
            Value::I64(a.checked_sub(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "integer overflow", span))?),
        (BinOp::Mul, Value::I64(a), Value::I64(b)) =>
            Value::I64(a.checked_mul(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "integer overflow", span))?),
        (BinOp::Div, Value::I64(a), Value::I64(b)) => {
            if b == 0 { return Err(MetelError::panic(RuntimeErrorCode::R0007, "division by zero", span)); }
            Value::I64(a.checked_div(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "integer overflow", span))?)
        }
        (BinOp::Rem, Value::I64(a), Value::I64(b)) => {
            if b == 0 { return Err(MetelError::panic(RuntimeErrorCode::R0007, "remainder by zero", span)); }
            Value::I64(a % b)
        }

        // ── i8 arithmetic ──────────────────────────────────────────────────────
        (BinOp::Add, Value::I8(a), Value::I8(b)) =>
            Value::I8(a.checked_add(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "i8 overflow", span))?),
        (BinOp::Sub, Value::I8(a), Value::I8(b)) =>
            Value::I8(a.checked_sub(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "i8 overflow", span))?),
        (BinOp::Mul, Value::I8(a), Value::I8(b)) =>
            Value::I8(a.checked_mul(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "i8 overflow", span))?),
        (BinOp::Div, Value::I8(a), Value::I8(b)) => {
            if b == 0 { return Err(MetelError::panic(RuntimeErrorCode::R0007, "division by zero", span)); }
            Value::I8(a.checked_div(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "i8 overflow", span))?)
        }
        (BinOp::Rem, Value::I8(a), Value::I8(b)) => {
            if b == 0 { return Err(MetelError::panic(RuntimeErrorCode::R0007, "remainder by zero", span)); }
            Value::I8(a % b)
        }

        // ── i16 arithmetic ─────────────────────────────────────────────────────
        (BinOp::Add, Value::I16(a), Value::I16(b)) =>
            Value::I16(a.checked_add(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "i16 overflow", span))?),
        (BinOp::Sub, Value::I16(a), Value::I16(b)) =>
            Value::I16(a.checked_sub(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "i16 overflow", span))?),
        (BinOp::Mul, Value::I16(a), Value::I16(b)) =>
            Value::I16(a.checked_mul(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "i16 overflow", span))?),
        (BinOp::Div, Value::I16(a), Value::I16(b)) => {
            if b == 0 { return Err(MetelError::panic(RuntimeErrorCode::R0007, "division by zero", span)); }
            Value::I16(a.checked_div(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "i16 overflow", span))?)
        }
        (BinOp::Rem, Value::I16(a), Value::I16(b)) => {
            if b == 0 { return Err(MetelError::panic(RuntimeErrorCode::R0007, "remainder by zero", span)); }
            Value::I16(a % b)
        }

        // ── i32 arithmetic ─────────────────────────────────────────────────────
        (BinOp::Add, Value::I32(a), Value::I32(b)) =>
            Value::I32(a.checked_add(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "i32 overflow", span))?),
        (BinOp::Sub, Value::I32(a), Value::I32(b)) =>
            Value::I32(a.checked_sub(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "i32 overflow", span))?),
        (BinOp::Mul, Value::I32(a), Value::I32(b)) =>
            Value::I32(a.checked_mul(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "i32 overflow", span))?),
        (BinOp::Div, Value::I32(a), Value::I32(b)) => {
            if b == 0 { return Err(MetelError::panic(RuntimeErrorCode::R0007, "division by zero", span)); }
            Value::I32(a.checked_div(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "i32 overflow", span))?)
        }
        (BinOp::Rem, Value::I32(a), Value::I32(b)) => {
            if b == 0 { return Err(MetelError::panic(RuntimeErrorCode::R0007, "remainder by zero", span)); }
            Value::I32(a % b)
        }

        // ── u8 arithmetic ──────────────────────────────────────────────────────
        (BinOp::Add, Value::U8(a), Value::U8(b)) =>
            Value::U8(a.checked_add(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "u8 overflow", span))?),
        (BinOp::Sub, Value::U8(a), Value::U8(b)) =>
            Value::U8(a.checked_sub(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "u8 underflow", span))?),
        (BinOp::Mul, Value::U8(a), Value::U8(b)) =>
            Value::U8(a.checked_mul(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "u8 overflow", span))?),
        (BinOp::Div, Value::U8(a), Value::U8(b)) => {
            if b == 0 { return Err(MetelError::panic(RuntimeErrorCode::R0007, "division by zero", span)); }
            Value::U8(a / b)
        }
        (BinOp::Rem, Value::U8(a), Value::U8(b)) => {
            if b == 0 { return Err(MetelError::panic(RuntimeErrorCode::R0007, "remainder by zero", span)); }
            Value::U8(a % b)
        }

        // ── u16 arithmetic ─────────────────────────────────────────────────────
        (BinOp::Add, Value::U16(a), Value::U16(b)) =>
            Value::U16(a.checked_add(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "u16 overflow", span))?),
        (BinOp::Sub, Value::U16(a), Value::U16(b)) =>
            Value::U16(a.checked_sub(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "u16 underflow", span))?),
        (BinOp::Mul, Value::U16(a), Value::U16(b)) =>
            Value::U16(a.checked_mul(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "u16 overflow", span))?),
        (BinOp::Div, Value::U16(a), Value::U16(b)) => {
            if b == 0 { return Err(MetelError::panic(RuntimeErrorCode::R0007, "division by zero", span)); }
            Value::U16(a / b)
        }
        (BinOp::Rem, Value::U16(a), Value::U16(b)) => {
            if b == 0 { return Err(MetelError::panic(RuntimeErrorCode::R0007, "remainder by zero", span)); }
            Value::U16(a % b)
        }

        // ── u32 arithmetic ─────────────────────────────────────────────────────
        (BinOp::Add, Value::U32(a), Value::U32(b)) =>
            Value::U32(a.checked_add(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "u32 overflow", span))?),
        (BinOp::Sub, Value::U32(a), Value::U32(b)) =>
            Value::U32(a.checked_sub(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "u32 underflow", span))?),
        (BinOp::Mul, Value::U32(a), Value::U32(b)) =>
            Value::U32(a.checked_mul(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "u32 overflow", span))?),
        (BinOp::Div, Value::U32(a), Value::U32(b)) => {
            if b == 0 { return Err(MetelError::panic(RuntimeErrorCode::R0007, "division by zero", span)); }
            Value::U32(a / b)
        }
        (BinOp::Rem, Value::U32(a), Value::U32(b)) => {
            if b == 0 { return Err(MetelError::panic(RuntimeErrorCode::R0007, "remainder by zero", span)); }
            Value::U32(a % b)
        }

        // ── u64 arithmetic ─────────────────────────────────────────────────────
        (BinOp::Add, Value::U64(a), Value::U64(b)) =>
            Value::U64(a.checked_add(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "u64 overflow", span))?),
        (BinOp::Sub, Value::U64(a), Value::U64(b)) =>
            Value::U64(a.checked_sub(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "u64 underflow", span))?),
        (BinOp::Mul, Value::U64(a), Value::U64(b)) =>
            Value::U64(a.checked_mul(b).ok_or_else(|| MetelError::panic(RuntimeErrorCode::R0007, "u64 overflow", span))?),
        (BinOp::Div, Value::U64(a), Value::U64(b)) => {
            if b == 0 { return Err(MetelError::panic(RuntimeErrorCode::R0007, "division by zero", span)); }
            Value::U64(a / b)
        }
        (BinOp::Rem, Value::U64(a), Value::U64(b)) => {
            if b == 0 { return Err(MetelError::panic(RuntimeErrorCode::R0007, "remainder by zero", span)); }
            Value::U64(a % b)
        }

        // ── Float arithmetic (no overflow semantics — IEEE 754) ────────────────
        (BinOp::Add, Value::F64(a), Value::F64(b)) => Value::F64(a + b),
        (BinOp::Sub, Value::F64(a), Value::F64(b)) => Value::F64(a - b),
        (BinOp::Mul, Value::F64(a), Value::F64(b)) => Value::F64(a * b),
        (BinOp::Div, Value::F64(a), Value::F64(b)) => Value::F64(a / b),
        (BinOp::Rem, Value::F64(a), Value::F64(b)) => Value::F64(a % b),

        (BinOp::Add, Value::F32(a), Value::F32(b)) => Value::F32(a + b),
        (BinOp::Sub, Value::F32(a), Value::F32(b)) => Value::F32(a - b),
        (BinOp::Mul, Value::F32(a), Value::F32(b)) => Value::F32(a * b),
        (BinOp::Div, Value::F32(a), Value::F32(b)) => Value::F32(a / b),
        (BinOp::Rem, Value::F32(a), Value::F32(b)) => Value::F32(a % b),

        // String concatenation
        (BinOp::Add, Value::Str(a), Value::Str(b)) => Value::Str(a + &b),

        // ── Integer comparisons ────────────────────────────────────────────────
        (BinOp::Eq, Value::I64(a), Value::I64(b)) => Value::Boolean(a == b),
        (BinOp::Ne, Value::I64(a), Value::I64(b)) => Value::Boolean(a != b),
        (BinOp::Lt, Value::I64(a), Value::I64(b)) => Value::Boolean(a <  b),
        (BinOp::Le, Value::I64(a), Value::I64(b)) => Value::Boolean(a <= b),
        (BinOp::Gt, Value::I64(a), Value::I64(b)) => Value::Boolean(a >  b),
        (BinOp::Ge, Value::I64(a), Value::I64(b)) => Value::Boolean(a >= b),

        (BinOp::Eq, Value::I8(a),  Value::I8(b))  => Value::Boolean(a == b),
        (BinOp::Ne, Value::I8(a),  Value::I8(b))  => Value::Boolean(a != b),
        (BinOp::Lt, Value::I8(a),  Value::I8(b))  => Value::Boolean(a <  b),
        (BinOp::Le, Value::I8(a),  Value::I8(b))  => Value::Boolean(a <= b),
        (BinOp::Gt, Value::I8(a),  Value::I8(b))  => Value::Boolean(a >  b),
        (BinOp::Ge, Value::I8(a),  Value::I8(b))  => Value::Boolean(a >= b),

        (BinOp::Eq, Value::I16(a), Value::I16(b)) => Value::Boolean(a == b),
        (BinOp::Ne, Value::I16(a), Value::I16(b)) => Value::Boolean(a != b),
        (BinOp::Lt, Value::I16(a), Value::I16(b)) => Value::Boolean(a <  b),
        (BinOp::Le, Value::I16(a), Value::I16(b)) => Value::Boolean(a <= b),
        (BinOp::Gt, Value::I16(a), Value::I16(b)) => Value::Boolean(a >  b),
        (BinOp::Ge, Value::I16(a), Value::I16(b)) => Value::Boolean(a >= b),

        (BinOp::Eq, Value::I32(a), Value::I32(b)) => Value::Boolean(a == b),
        (BinOp::Ne, Value::I32(a), Value::I32(b)) => Value::Boolean(a != b),
        (BinOp::Lt, Value::I32(a), Value::I32(b)) => Value::Boolean(a <  b),
        (BinOp::Le, Value::I32(a), Value::I32(b)) => Value::Boolean(a <= b),
        (BinOp::Gt, Value::I32(a), Value::I32(b)) => Value::Boolean(a >  b),
        (BinOp::Ge, Value::I32(a), Value::I32(b)) => Value::Boolean(a >= b),

        (BinOp::Eq, Value::U8(a),  Value::U8(b))  => Value::Boolean(a == b),
        (BinOp::Ne, Value::U8(a),  Value::U8(b))  => Value::Boolean(a != b),
        (BinOp::Lt, Value::U8(a),  Value::U8(b))  => Value::Boolean(a <  b),
        (BinOp::Le, Value::U8(a),  Value::U8(b))  => Value::Boolean(a <= b),
        (BinOp::Gt, Value::U8(a),  Value::U8(b))  => Value::Boolean(a >  b),
        (BinOp::Ge, Value::U8(a),  Value::U8(b))  => Value::Boolean(a >= b),

        (BinOp::Eq, Value::U16(a), Value::U16(b)) => Value::Boolean(a == b),
        (BinOp::Ne, Value::U16(a), Value::U16(b)) => Value::Boolean(a != b),
        (BinOp::Lt, Value::U16(a), Value::U16(b)) => Value::Boolean(a <  b),
        (BinOp::Le, Value::U16(a), Value::U16(b)) => Value::Boolean(a <= b),
        (BinOp::Gt, Value::U16(a), Value::U16(b)) => Value::Boolean(a >  b),
        (BinOp::Ge, Value::U16(a), Value::U16(b)) => Value::Boolean(a >= b),

        (BinOp::Eq, Value::U32(a), Value::U32(b)) => Value::Boolean(a == b),
        (BinOp::Ne, Value::U32(a), Value::U32(b)) => Value::Boolean(a != b),
        (BinOp::Lt, Value::U32(a), Value::U32(b)) => Value::Boolean(a <  b),
        (BinOp::Le, Value::U32(a), Value::U32(b)) => Value::Boolean(a <= b),
        (BinOp::Gt, Value::U32(a), Value::U32(b)) => Value::Boolean(a >  b),
        (BinOp::Ge, Value::U32(a), Value::U32(b)) => Value::Boolean(a >= b),

        (BinOp::Eq, Value::U64(a), Value::U64(b)) => Value::Boolean(a == b),
        (BinOp::Ne, Value::U64(a), Value::U64(b)) => Value::Boolean(a != b),
        (BinOp::Lt, Value::U64(a), Value::U64(b)) => Value::Boolean(a <  b),
        (BinOp::Le, Value::U64(a), Value::U64(b)) => Value::Boolean(a <= b),
        (BinOp::Gt, Value::U64(a), Value::U64(b)) => Value::Boolean(a >  b),
        (BinOp::Ge, Value::U64(a), Value::U64(b)) => Value::Boolean(a >= b),

        // ── Float comparisons ──────────────────────────────────────────────────
        (BinOp::Eq, Value::F64(a), Value::F64(b)) => Value::Boolean(a == b),
        (BinOp::Ne, Value::F64(a), Value::F64(b)) => Value::Boolean(a != b),
        (BinOp::Lt, Value::F64(a), Value::F64(b)) => Value::Boolean(a <  b),
        (BinOp::Le, Value::F64(a), Value::F64(b)) => Value::Boolean(a <= b),
        (BinOp::Gt, Value::F64(a), Value::F64(b)) => Value::Boolean(a >  b),
        (BinOp::Ge, Value::F64(a), Value::F64(b)) => Value::Boolean(a >= b),

        (BinOp::Eq, Value::F32(a), Value::F32(b)) => Value::Boolean(a == b),
        (BinOp::Ne, Value::F32(a), Value::F32(b)) => Value::Boolean(a != b),
        (BinOp::Lt, Value::F32(a), Value::F32(b)) => Value::Boolean(a <  b),
        (BinOp::Le, Value::F32(a), Value::F32(b)) => Value::Boolean(a <= b),
        (BinOp::Gt, Value::F32(a), Value::F32(b)) => Value::Boolean(a >  b),
        (BinOp::Ge, Value::F32(a), Value::F32(b)) => Value::Boolean(a >= b),

        // boolean equality
        (BinOp::Eq, Value::Boolean(a), Value::Boolean(b)) => Value::Boolean(a == b),
        (BinOp::Ne, Value::Boolean(a), Value::Boolean(b)) => Value::Boolean(a != b),

        // String equality
        (BinOp::Eq, Value::Str(a), Value::Str(b)) => Value::Boolean(a == b),
        (BinOp::Ne, Value::Str(a), Value::Str(b)) => Value::Boolean(a != b),

        // Char equality and ordering (Unicode scalar order)
        (BinOp::Eq, Value::Char(a), Value::Char(b)) => Value::Boolean(a == b),
        (BinOp::Ne, Value::Char(a), Value::Char(b)) => Value::Boolean(a != b),
        (BinOp::Lt, Value::Char(a), Value::Char(b)) => Value::Boolean(a <  b),
        (BinOp::Le, Value::Char(a), Value::Char(b)) => Value::Boolean(a <= b),
        (BinOp::Gt, Value::Char(a), Value::Char(b)) => Value::Boolean(a >  b),
        (BinOp::Ge, Value::Char(a), Value::Char(b)) => Value::Boolean(a >= b),

        // Range — produce a Struct value understood by for-in (issue #55)
        (BinOp::Range, Value::I64(a), Value::I64(b)) => Value::Struct {
            name: "Range".to_string(),
            type_id: Some(crate::symbols::SYM_TYPE_RANGE),
            fields: {
                let mut m = HashMap::new();
                m.insert("start".to_string(), Value::I64(a));
                m.insert("end".to_string(),   Value::I64(b));
                m
            },
        },
        (BinOp::RangeInclusive, Value::I64(a), Value::I64(b)) => Value::Struct {
            name: "RangeInclusive".to_string(),
            type_id: Some(crate::symbols::SYM_TYPE_RANGE_INCLUSIVE),
            fields: {
                let mut m = HashMap::new();
                m.insert("start".to_string(), Value::I64(a));
                m.insert("end".to_string(),   Value::I64(b));
                m
            },
        },

        (_, lv, rv) => return Err(MetelError::internal(
            format!("binop: unsupported operand types ({lv:?}, {rv:?}) (typechecker should have caught this)"),
        )),
    };
    Ok(Signal::Value(result))
}
