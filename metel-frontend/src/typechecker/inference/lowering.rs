use super::{
    Bound, Decl, Expr, FunDecl, GenericParam, ImplBlock, Param, Polarity, Program, Span, TypeExpr,
};

pub(super) fn lower_impl_aspect(fun: &FunDecl, counter: &mut usize) -> FunDecl {
    let mut extra_generics: Vec<GenericParam> = Vec::new();
    let new_params: Vec<Param> = fun
        .params
        .iter()
        .map(|p| {
            if let Some(type_ann) = &p.type_ann {
                Param {
                    mutable: p.mutable,
                    receiver: p.receiver.clone(),
                    name: p.name.clone(),
                    type_ann: Some(lower_impl_aspect_param_type(
                        type_ann,
                        counter,
                        &mut extra_generics,
                    )),
                    span: p.span.clone(),
                }
            } else {
                p.clone()
            }
        })
        .collect();

    let mut new_generics = fun.generics.clone();
    new_generics.extend(extra_generics);

    FunDecl {
        visibility: fun.visibility.clone(),
        name: fun.name.clone(),
        generics: new_generics,
        where_clause: fun.where_clause.clone(),
        params: new_params,
        return_type: fun.return_type.clone(),
        native: fun.native.clone(),
        body: fun.body.clone(),
        span: fun.span.clone(),
    }
}

fn lower_impl_aspect_param_type(
    type_expr: &TypeExpr,
    counter: &mut usize,
    extra_generics: &mut Vec<GenericParam>,
) -> TypeExpr {
    match type_expr {
        TypeExpr::ImplAspect { bound, span, .. } => {
            let anon_name = format!("_ImplT{counter}");
            *counter += 1;
            extra_generics.push(GenericParam {
                name: anon_name.clone(),
                is_record: false,
                bounds: vec![Bound {
                    polarity: Polarity::Positive,
                    head: crate::ast::BoundHead::Aspect(bound.as_ref().clone()),
                    assoc_bindings: vec![],
                    span: span.clone(),
                }],
            });
            TypeExpr::Named(anon_name, vec![])
        }
        TypeExpr::Named(name, args) => TypeExpr::Named(
            name.clone(),
            args.iter()
                .map(|arg| lower_impl_aspect_param_type(arg, counter, extra_generics))
                .collect(),
        ),
        TypeExpr::Tuple(items) => TypeExpr::Tuple(
            items
                .iter()
                .map(|item| lower_impl_aspect_param_type(item, counter, extra_generics))
                .collect(),
        ),
        TypeExpr::Record(fields) => TypeExpr::Record(
            fields
                .iter()
                .map(|(name, field_ty)| {
                    (
                        name.clone(),
                        lower_impl_aspect_param_type(field_ty, counter, extra_generics),
                    )
                })
                .collect(),
        ),
        TypeExpr::Array(inner) => TypeExpr::Array(Box::new(lower_impl_aspect_param_type(
            inner,
            counter,
            extra_generics,
        ))),
        TypeExpr::SizedArray(inner, len) => TypeExpr::SizedArray(
            Box::new(lower_impl_aspect_param_type(inner, counter, extra_generics)),
            *len,
        ),
        TypeExpr::Reference(inner) => TypeExpr::Reference(Box::new(lower_impl_aspect_param_type(
            inner,
            counter,
            extra_generics,
        ))),
        TypeExpr::MutReference(inner) => TypeExpr::MutReference(Box::new(
            lower_impl_aspect_param_type(inner, counter, extra_generics),
        )),
        TypeExpr::Fun {
            params,
            return_type: ret,
            call_multiplicity,
            call_mutation,
        } => TypeExpr::Fun {
            params: params
                .iter()
                .map(|param| lower_impl_aspect_param_type(param, counter, extra_generics))
                .collect(),
            return_type: ret.as_ref().map(|ret_ty| {
                Box::new(lower_impl_aspect_param_type(
                    ret_ty,
                    counter,
                    extra_generics,
                ))
            }),
            call_multiplicity: *call_multiplicity,
            call_mutation: *call_mutation,
        },
        TypeExpr::Projection {
            base,
            assoc_name,
            span,
        } => TypeExpr::Projection {
            base: Box::new(lower_impl_aspect_param_type(base, counter, extra_generics)),
            assoc_name: assoc_name.clone(),
            span: span.clone(),
        },
        // `dyn Aspect` is never lowered away (unlike `ImplAspect`, it's a real
        // existential type, not per-call-site generic sugar) -- only recurse into
        // its own type args, in case one of *those* happens to be `impl Aspect`
        // (`dyn Callable<impl Foo, i64>`).
        TypeExpr::DynAspect { bound, span } => TypeExpr::DynAspect {
            bound: Box::new(lower_impl_aspect_param_type(bound, counter, extra_generics)),
            span: span.clone(),
        },
        TypeExpr::RecordProjection { .. } | TypeExpr::Unit => type_expr.clone(),
    }
}

/// Lower all `impl Aspect` params in all `FunDecl`s in a `Program`.
/// Returns a new program with the lowered declarations.
pub(in crate::typechecker) fn lower_impl_aspects_in_program(program: Program) -> Program {
    let mut counter = 0usize;
    let decls = program
        .decls
        .into_iter()
        .map(|decl| match decl {
            Decl::Fun(fun) => Decl::Fun(lower_impl_aspect(&fun, &mut counter)),
            Decl::Impl(ib) => Decl::Impl(ImplBlock {
                methods: ib
                    .methods
                    .iter()
                    .map(|m| lower_impl_aspect(m, &mut counter))
                    .collect(),
                ..ib
            }),
            other => other,
        })
        .collect();
    Program { decls, ..program }
}

/// Rewrite `T::AssocType`-shaped `TypeExpr::Named` nodes into `TypeExpr::Projection`
/// wherever `T` matches one of `generics`' names (RFC-0082 SS3). Purely structural —
/// checks only whether the name is a declared generic parameter, not whether the
/// aspect it's bound to actually declares that associated type; real associated-type
/// resolution is issue #242's job. The parser can't do this itself (`type_path`
/// already accepts multi-segment names, so `T::Target` parses as a plain dotted
/// `Named` either way) since recognizing a projection needs to know which names are
/// declared generics, context the parser doesn't have.
fn lower_projections_in_decl(decl: Decl) -> Decl {
    match decl {
        Decl::Fun(fun) => Decl::Fun(lower_projections_in_fun(&fun, &[], false)),
        Decl::Let(let_decl) => Decl::Let(crate::ast::LetDecl {
            type_ann: let_decl.type_ann.as_ref().map(|t| {
                lower_projections_in_type(t, &std::collections::HashSet::new(), &let_decl.span)
            }),
            value: lower_projections_in_expr(&let_decl.value, &std::collections::HashSet::new()),
            ..let_decl
        }),
        Decl::Mut(mut_decl) => Decl::Mut(crate::ast::MutDecl {
            type_ann: mut_decl.type_ann.as_ref().map(|t| {
                lower_projections_in_type(t, &std::collections::HashSet::new(), &mut_decl.span)
            }),
            value: lower_projections_in_expr(&mut_decl.value, &std::collections::HashSet::new()),
            ..mut_decl
        }),
        Decl::Impl(ib) => Decl::Impl(crate::ast::ImplBlock {
            methods: ib
                .methods
                .iter()
                .map(|m| lower_projections_in_fun(m, &ib.generics, true))
                .collect(),
            ..ib
        }),
        Decl::Stmt(stmt) => Decl::Stmt(Box::new(lower_projections_in_stmt(
            &stmt,
            &std::collections::HashSet::new(),
        ))),
        other => other,
    }
}

fn lower_projections_in_block(
    block: &crate::ast::Block,
    generics: &std::collections::HashSet<String>,
) -> crate::ast::Block {
    crate::ast::Block {
        stmts: block
            .stmts
            .iter()
            .map(|d| lower_projections_in_decl_with_generics(d, generics))
            .collect(),
        tail: block
            .tail
            .as_ref()
            .map(|e| Box::new(lower_projections_in_expr(e, generics))),
        span: block.span.clone(),
    }
}

fn lower_projections_in_decl_with_generics(
    decl: &Decl,
    generics: &std::collections::HashSet<String>,
) -> Decl {
    match decl {
        Decl::Let(let_decl) => Decl::Let(crate::ast::LetDecl {
            type_ann: let_decl
                .type_ann
                .as_ref()
                .map(|t| lower_projections_in_type(t, generics, &let_decl.span)),
            value: lower_projections_in_expr(&let_decl.value, generics),
            ..let_decl.clone()
        }),
        Decl::Mut(mut_decl) => Decl::Mut(crate::ast::MutDecl {
            type_ann: mut_decl
                .type_ann
                .as_ref()
                .map(|t| lower_projections_in_type(t, generics, &mut_decl.span)),
            value: lower_projections_in_expr(&mut_decl.value, generics),
            ..mut_decl.clone()
        }),
        Decl::Stmt(stmt) => Decl::Stmt(Box::new(lower_projections_in_stmt(stmt, generics))),
        Decl::Fun(fun) => Decl::Fun(lower_projections_in_fun_with_generics(fun, generics)),
        Decl::Impl(ib) => Decl::Impl(crate::ast::ImplBlock {
            methods: ib
                .methods
                .iter()
                .map(|m| lower_projections_in_fun(m, &ib.generics, true))
                .collect(),
            ..ib.clone()
        }),
        other => other.clone(),
    }
}

fn lower_projections_in_fun_with_generics(
    fun: &FunDecl,
    parent_generics: &std::collections::HashSet<String>,
) -> FunDecl {
    let mut names: std::collections::HashSet<String> = parent_generics.clone();
    for g in &fun.generics {
        names.insert(g.name.clone());
    }
    if names.is_empty() {
        return fun.clone();
    }
    let params = fun
        .params
        .iter()
        .map(|p| Param {
            type_ann: p
                .type_ann
                .as_ref()
                .map(|t| lower_projections_in_type(t, &names, &p.span)),
            ..p.clone()
        })
        .collect();
    let return_type = fun
        .return_type
        .as_ref()
        .map(|t| lower_projections_in_type(t, &names, &fun.span));
    let body = lower_projections_in_block(&fun.body, &names);
    FunDecl {
        params,
        return_type,
        body,
        ..fun.clone()
    }
}

fn lower_projections_in_stmt(
    stmt: &crate::ast::Stmt,
    generics: &std::collections::HashSet<String>,
) -> crate::ast::Stmt {
    match stmt {
        crate::ast::Stmt::While(ws) => crate::ast::Stmt::While(crate::ast::WhileStmt {
            condition: lower_projections_in_expr(&ws.condition, generics),
            body: lower_projections_in_block(&ws.body, generics),
            span: ws.span.clone(),
        }),
        crate::ast::Stmt::For(fs) => {
            let init = fs.init.as_ref().map(|fi| match fi {
                crate::ast::ForInit::Let(l) => crate::ast::ForInit::Let(crate::ast::LetDecl {
                    type_ann: l
                        .type_ann
                        .as_ref()
                        .map(|t| lower_projections_in_type(t, generics, &l.span)),
                    value: lower_projections_in_expr(&l.value, generics),
                    ..l.clone()
                }),
                crate::ast::ForInit::Mut(m) => crate::ast::ForInit::Mut(crate::ast::MutDecl {
                    type_ann: m
                        .type_ann
                        .as_ref()
                        .map(|t| lower_projections_in_type(t, generics, &m.span)),
                    value: lower_projections_in_expr(&m.value, generics),
                    ..m.clone()
                }),
                crate::ast::ForInit::Expr(e) => {
                    crate::ast::ForInit::Expr(lower_projections_in_expr(e, generics))
                }
            });
            crate::ast::Stmt::For(Box::new(crate::ast::ForStmt {
                init,
                condition: fs
                    .condition
                    .as_ref()
                    .map(|c| lower_projections_in_expr(c, generics)),
                step: fs
                    .step
                    .as_ref()
                    .map(|s| lower_projections_in_expr(s, generics)),
                body: lower_projections_in_block(&fs.body, generics),
                span: fs.span.clone(),
            }))
        }
        crate::ast::Stmt::ForIn(fis) => crate::ast::Stmt::ForIn(Box::new(crate::ast::ForInStmt {
            binding: fis.binding.clone(),
            mutable: fis.mutable,
            iterable: lower_projections_in_expr(&fis.iterable, generics),
            body: lower_projections_in_block(&fis.body, generics),
            span: fis.span.clone(),
        })),
        crate::ast::Stmt::Expr(e) => crate::ast::Stmt::Expr(lower_projections_in_expr(e, generics)),
    }
}

// Exhaustive match over every Expr variant; splitting it up would scatter
// one coherent dispatch table across many small functions with no real gain
// in clarity.
#[allow(clippy::too_many_lines)]
fn lower_projections_in_expr(expr: &Expr, generics: &std::collections::HashSet<String>) -> Expr {
    let go = |e: &Expr| lower_projections_in_expr(e, generics);
    match expr {
        Expr::Call {
            callee,
            type_args,
            args,
            span,
        } => Expr::Call {
            callee: Box::new(go(callee)),
            type_args: type_args
                .iter()
                .map(|t| lower_projections_in_type(t, generics, span))
                .collect(),
            args: args.iter().map(go).collect(),
            span: span.clone(),
        },
        Expr::MethodCall {
            receiver,
            method,
            type_args,
            args,
            span,
        } => Expr::MethodCall {
            receiver: Box::new(go(receiver)),
            method: method.clone(),
            type_args: type_args
                .iter()
                .map(|t| lower_projections_in_type(t, generics, span))
                .collect(),
            args: args.iter().map(go).collect(),
            span: span.clone(),
        },
        Expr::Cast {
            expr: e,
            target_type,
            span,
        } => Expr::Cast {
            expr: Box::new(go(e)),
            target_type: lower_projections_in_type(target_type, generics, span),
            span: span.clone(),
        },
        Expr::Ascribe { expr: e, ann, span } => Expr::Ascribe {
            expr: Box::new(go(e)),
            ann: lower_projections_in_type(ann, generics, span),
            span: span.clone(),
        },
        Expr::Closure {
            captures,
            call_multiplicity,
            call_mutation,
            params,
            return_type,
            body,
            span,
        } => Expr::Closure {
            captures: captures.clone(),
            call_multiplicity: *call_multiplicity,
            call_mutation: *call_mutation,
            params: params
                .iter()
                .map(|p| Param {
                    type_ann: p
                        .type_ann
                        .as_ref()
                        .map(|t| lower_projections_in_type(t, generics, &p.span)),
                    ..p.clone()
                })
                .collect(),
            return_type: return_type
                .as_ref()
                .map(|t| lower_projections_in_type(t, generics, span)),
            body: lower_projections_in_block(body, generics),
            span: span.clone(),
        },
        Expr::If {
            condition,
            then_branch,
            else_branch,
            span,
        } => Expr::If {
            condition: Box::new(go(condition)),
            then_branch: lower_projections_in_block(then_branch, generics),
            else_branch: else_branch
                .as_ref()
                .map(|b| lower_projections_in_block(b, generics)),
            span: span.clone(),
        },
        Expr::Loop { body, span } => Expr::Loop {
            body: lower_projections_in_block(body, generics),
            span: span.clone(),
        },
        Expr::Match(m) => Expr::Match(crate::ast::MatchExpr {
            scrutinee: Box::new(go(&m.scrutinee)),
            arms: m
                .arms
                .iter()
                .map(|a| crate::ast::MatchArm {
                    pattern: a.pattern.clone(),
                    guard: a.guard.as_ref().map(&go),
                    body: lower_projections_in_block(&a.body, generics),
                    span: a.span.clone(),
                })
                .collect(),
            span: m.span.clone(),
        }),
        Expr::Tuple(es, s) => Expr::Tuple(es.iter().map(go).collect(), s.clone()),
        Expr::Array(es, s) => Expr::Array(es.iter().map(go).collect(), s.clone()),
        Expr::RecordLiteral { fields, span } => Expr::RecordLiteral {
            fields: fields
                .iter()
                .map(|(name, expr)| (name.clone(), go(expr)))
                .collect(),
            span: span.clone(),
        },
        Expr::RepeatArray(e, n, s) => Expr::RepeatArray(Box::new(go(e)), *n, s.clone()),
        Expr::BinOp(l, op, r, s) => {
            Expr::BinOp(Box::new(go(l)), op.clone(), Box::new(go(r)), s.clone())
        }
        Expr::UnaryOp(op, e, s) => Expr::UnaryOp(op.clone(), Box::new(go(e)), s.clone()),
        Expr::Assign {
            target,
            op,
            value,
            span,
        } => Expr::Assign {
            target: target.clone(),
            op: op.clone(),
            value: Box::new(go(value)),
            span: span.clone(),
        },
        Expr::FieldAccess {
            object,
            field,
            span,
        } => Expr::FieldAccess {
            object: Box::new(go(object)),
            field: field.clone(),
            span: span.clone(),
        },
        Expr::TupleAccess {
            object,
            index,
            span,
        } => Expr::TupleAccess {
            object: Box::new(go(object)),
            index: *index,
            span: span.clone(),
        },
        Expr::Index {
            object,
            index,
            span,
        } => Expr::Index {
            object: Box::new(go(object)),
            index: Box::new(go(index)),
            span: span.clone(),
        },
        Expr::PropagateError { expr: e, span } => Expr::PropagateError {
            expr: Box::new(go(e)),
            span: span.clone(),
        },
        Expr::Return(re) => Expr::Return(crate::ast::ReturnExpr {
            value: re.value.as_ref().map(|v| Box::new(go(v))),
            span: re.span.clone(),
        }),
        Expr::Break(br) => Expr::Break(crate::ast::BreakExpr {
            value: br.value.as_ref().map(|v| Box::new(go(v))),
            span: br.span.clone(),
        }),
        // Leaf expressions — no sub-Expr or TypeExpr to rewrite.
        Expr::Literal(_, _)
        | Expr::Ident(_, _)
        | Expr::Path(..)
        | Expr::ResolvedPath { .. }
        | Expr::Continue(_) => expr.clone(),
        Expr::StructLiteral {
            path,
            fields,
            symbol_id,
            span,
        } => Expr::StructLiteral {
            path: path.clone(),
            fields: fields.iter().map(|(n, e)| (n.clone(), go(e))).collect(),
            symbol_id: *symbol_id,
            span: span.clone(),
        },
        Expr::RecordProjection { path, fields, span } => Expr::RecordProjection {
            path: path.clone(),
            fields: fields.clone(),
            span: span.clone(),
        },
    }
}

fn lower_projections_in_type(
    te: &TypeExpr,
    generics: &std::collections::HashSet<String>,
    fallback_span: &Span,
) -> TypeExpr {
    let go = |t: &TypeExpr| lower_projections_in_type(t, generics, fallback_span);
    match te {
        TypeExpr::Named(name, args) if args.is_empty() => {
            if let Some((base, assoc)) = name.split_once("::") {
                if generics.contains(base) {
                    return TypeExpr::Projection {
                        base: Box::new(TypeExpr::Named(base.to_string(), vec![])),
                        assoc_name: assoc.to_string(),
                        span: fallback_span.clone(),
                    };
                }
            }
            te.clone()
        }
        TypeExpr::Named(name, args) => TypeExpr::Named(name.clone(), args.iter().map(go).collect()),
        TypeExpr::Unit => TypeExpr::Unit,
        TypeExpr::Tuple(items) => TypeExpr::Tuple(items.iter().map(go).collect()),
        TypeExpr::Record(fields) => TypeExpr::Record(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), go(ty)))
                .collect(),
        ),
        TypeExpr::Array(inner) => TypeExpr::Array(Box::new(go(inner))),
        TypeExpr::SizedArray(inner, n) => TypeExpr::SizedArray(Box::new(go(inner)), *n),
        TypeExpr::Reference(inner) => TypeExpr::Reference(Box::new(go(inner))),
        TypeExpr::MutReference(inner) => TypeExpr::MutReference(Box::new(go(inner))),
        TypeExpr::Fun {
            params,
            return_type: ret,
            call_multiplicity,
            call_mutation,
        } => TypeExpr::Fun {
            params: params.iter().map(go).collect(),
            return_type: ret.as_deref().map(go).map(Box::new),
            call_multiplicity: *call_multiplicity,
            call_mutation: *call_mutation,
        },
        TypeExpr::ImplAspect {
            bound,
            source_spell,
            span,
        } => TypeExpr::ImplAspect {
            bound: Box::new(go(bound)),
            source_spell: source_spell.clone(),
            span: span.clone(),
        },
        // Already a projection (e.g. re-run on already-lowered input) — nothing to do.
        TypeExpr::Projection { .. } | TypeExpr::RecordProjection { .. } => te.clone(),
        TypeExpr::DynAspect { bound, span } => TypeExpr::DynAspect {
            bound: Box::new(go(bound)),
            span: span.clone(),
        },
    }
}

/// Generic-parameter names in scope for lowering projections in `fun`'s signature:
/// its own generics plus (for impl methods) the impl block's, since a method can
/// reference either (`T` from `impl<T> Aspect for Type<T>`, or its own `<U>`).
///
/// `self_in_scope` adds `Self` to that set for impl-block methods (#740 part A):
/// `Self::AssocType` is exactly as much a projection as `T::AssocType` is, but
/// `Self` is never a declared `GenericParam` on the function or the impl block, so
/// it needs its own entry rather than falling out of `fun.generics`/`extra_generics`
/// the way `T` does. This also fixes a real correctness bug beyond just the missing
/// name: an impl-block method with *no* ordinary generics at all (e.g. `extend Box1:
/// Container { fun get(&self) -> Self::Item { ... } }`) used to hit the `names.is_empty()`
/// early return below and skip lowering entirely, so `Self::Item` never became a
/// `TypeExpr::Projection` in the first place -- not even the recognition step ran.
fn lower_projections_in_fun(
    fun: &FunDecl,
    extra_generics: &[GenericParam],
    self_in_scope: bool,
) -> FunDecl {
    let mut names: std::collections::HashSet<String> = fun
        .generics
        .iter()
        .chain(extra_generics)
        .map(|g| g.name.clone())
        .collect();
    if self_in_scope {
        names.insert("Self".to_string());
    }
    if names.is_empty() {
        return fun.clone();
    }
    lower_projections_in_fun_with_generics(fun, &names)
}

/// Lower all `T::AssocType` projections in every `FunDecl`'s params/return-type in a
/// `Program`. Also descends into function bodies to lower type annotations on
/// `let`/`mut` bindings, closure signatures, cast targets, ascribe annotations,
/// and generic type arguments in call sites — any `TypeExpr` that could reference
/// an associated type from a generic param.
pub(in crate::typechecker) fn lower_projections_in_program(program: Program) -> Program {
    let decls = program
        .decls
        .into_iter()
        .map(lower_projections_in_decl)
        .collect();
    Program { decls, ..program }
}
