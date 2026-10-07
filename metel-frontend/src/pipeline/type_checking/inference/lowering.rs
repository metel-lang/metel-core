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

/// Shared by `TypeExpr::Record`'s and `TypeExpr::OpenRecord`'s identical
/// per-field lowering below.
fn lower_impl_aspect_fields(
    fields: &[(String, TypeExpr)],
    counter: &mut usize,
    extra_generics: &mut Vec<GenericParam>,
) -> Vec<(String, TypeExpr)> {
    fields
        .iter()
        .map(|(name, field_ty)| {
            (
                name.clone(),
                lower_impl_aspect_param_type(field_ty, counter, extra_generics),
            )
        })
        .collect()
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
                is_row: false,
                bounds: vec![Bound {
                    polarity: Polarity::Positive,
                    head: crate::data::ast::BoundHead::Aspect(bound.as_ref().clone()),
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
        TypeExpr::Record(fields) => {
            TypeExpr::Record(lower_impl_aspect_fields(fields, counter, extra_generics))
        }
        // RFC-0121: a `fun_decl` parameter's open-row-tailed type can contain
        // `impl Aspect` sugar in a named field exactly as a closed `Record`
        // can (`{ x: impl Display, ..R }`) -- lower each field the same way;
        // the tail carries no `TypeExpr` of its own.
        TypeExpr::OpenRecord(fields, tail) => TypeExpr::OpenRecord(
            lower_impl_aspect_fields(fields, counter, extra_generics),
            tail.clone(),
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
        // RFC-0121 installment 2: `Handle.{ fd, ..R }` names a struct and its
        // own field labels only -- no `TypeExpr` of its own to lower `impl
        // Aspect` sugar inside of, exactly like `RecordProjection`.
        //
        // RFC-0121 item 2 (metel-core#1310): `Session<..R>`'s row splice is
        // likewise a leaf here -- no `impl Aspect` sugar can hide inside a
        // bare row splice. This runs before `projections::check` gets a
        // chance to reject a `RowArg`, so a leaf, not `unreachable!()`.
        TypeExpr::RecordProjection { .. }
        | TypeExpr::OpenRecordProjection { .. }
        | TypeExpr::RowArg(_)
        | TypeExpr::Unit => type_expr.clone(),
    }
}

/// Lower all `impl Aspect` params in all `FunDecl`s in a `Program`.
/// Returns a new program with the lowered declarations.
/// Every program-to-program lowering the checker applies before building its registry, in
/// the order they must run: `impl Aspect` parameters, then `T::AssocType` projections, then
/// the expansion of inherited aspect defaults into generic impls.
pub(in crate::pipeline::type_checking) fn lower_program(
    program: Program,
    base_registry: &super::super::type_engine::TypeDefinitionRegistry,
    current_module_path: &[String],
) -> Program {
    let program = lower_impl_aspects_in_program(program);
    let program = lower_projections_in_program(program);
    expand_generic_impl_defaults(program, base_registry, current_module_path)
}

/// metel-core#1329: write the inherited default methods of an aspect out into a *generic*
/// impl, as if the author had typed them, so the ordinary generic-impl machinery (method
/// schemes over the target's parameters, bounds, call-time reconstruction of the body)
/// handles them.
///
/// Default bodies of an impl on a non-generic type are registered and checked as plain
/// methods against a `self` of the bare target name. For `extend<T> Box<T>: Aspect` that
/// `self` has no type arguments, and the registered method is a scheme over `T`, so the two
/// never unify. Expanding sidesteps that: `infer_impl_method` already binds `Self` and the
/// target's parameters for a method written in the block.
///
/// Only an impl that is generic (its own generics, or a target with type arguments) and
/// whose aspect has neither type parameters nor associated types is expanded; anything
/// else is left to the existing path unchanged. An associated type is excluded because a
/// default body names it bare (`Item`, sugar for `Self::Item`), which resolves only in the
/// aspect's own context, not inside the impl the body is copied into. Each expanded method gets a span of its own (derived from the
/// impl's), because the registry identifies a generic method body by its declaration span
/// and every impl inheriting the same default would otherwise share the aspect's.
fn expand_generic_impl_defaults(
    program: Program,
    base_registry: &super::super::type_engine::TypeDefinitionRegistry,
    current_module_path: &[String],
) -> Program {
    use crate::data::ast::AspectMethod;
    use std::collections::HashMap;

    /// `(the aspect's type parameter names, its associated type names, its methods)`,
    /// keyed by aspect name.
    type AspectDefaults = HashMap<String, (Vec<String>, Vec<String>, Vec<AspectMethod>)>;

    fn collect(decls: &[Decl], into: &mut AspectDefaults) {
        for decl in decls {
            if let Decl::Aspect(ad) = decl {
                into.insert(
                    ad.name.clone(),
                    (
                        ad.generics.clone(),
                        ad.assoc_types.iter().map(|a| a.name.clone()).collect(),
                        ad.methods.clone(),
                    ),
                );
            }
        }
    }

    // Aspects declared in this module and in std::core, then whatever the registry already
    // knows from modules checked before this one.
    let Program {
        imports,
        exports,
        decls,
    } = program;
    let mut known: AspectDefaults = HashMap::new();
    collect(&decls, &mut known);
    collect(&crate::stdlib::core_program().decls, &mut known);

    let defaults_of = |aspect: &str| -> Option<(Vec<String>, Vec<String>, Vec<AspectMethod>)> {
        match known.get(aspect) {
            Some((params, assoc, methods)) => {
                Some((params.clone(), assoc.clone(), methods.clone()))
            }
            None => Some((
                base_registry
                    .aspect_generics_in(current_module_path, aspect)?
                    .clone(),
                base_registry
                    .aspect_assoc_type_decls_in(current_module_path, aspect)
                    .map_or_else(Vec::new, |decls| {
                        decls.iter().map(|d| d.name.clone()).collect()
                    }),
                base_registry
                    .aspect_method_defs_in(current_module_path, aspect)?
                    .clone(),
            )),
        }
    };

    let decls = decls
        .into_iter()
        .map(|decl| match decl {
            Decl::Impl(ib) => Decl::Impl(expand_impl_defaults(ib, &defaults_of)),
            other => other,
        })
        .collect();
    Program {
        imports,
        exports,
        decls,
    }
}

/// `(an aspect's type parameter names, its associated type names, its methods)`.
type AspectDefaultsEntry = (
    Vec<String>,
    Vec<String>,
    Vec<crate::data::ast::AspectMethod>,
);

/// Write out the inherited default methods of one impl block (see
/// `expand_generic_impl_defaults`).
fn expand_impl_defaults(
    mut ib: ImplBlock,
    defaults_of: &dyn Fn(&str) -> Option<AspectDefaultsEntry>,
) -> ImplBlock {
    use crate::data::ast::Visibility;
    use std::collections::HashMap;

    // A record target (RFC-0121 §3) has no nominal type to pre-register a
    // default against either, so it takes the same expansion.
    let generic_target = !ib.generics.is_empty()
        || matches!(&ib.target_type, TypeExpr::Named(_, args) if !args.is_empty())
        || matches!(
            &ib.target_type,
            TypeExpr::Record(_) | TypeExpr::OpenRecord(..)
        );
    let Some(aspect) = ib
        .aspect_name
        .clone()
        .filter(|_| ib.polarity == Polarity::Positive)
    else {
        return ib;
    };
    let Some((aspect_params, assoc_names, methods)) = defaults_of(&aspect) else {
        return ib;
    };
    // An aspect with type parameters (`aspect Conv<T>`): the impl's aspect type
    // arguments stand for them in the copied default (metel-core#1330). An arity
    // mismatch is the impl's own error, reported elsewhere.
    if aspect_params.len() != ib.aspect_type_args.len() {
        return ib;
    }
    let mut subst: HashMap<&str, &TypeExpr> = aspect_params
        .iter()
        .map(String::as_str)
        .zip(ib.aspect_type_args.iter())
        .collect();
    // An associated type a default names bare (`Item`, sugar for `Self::Item`)
    // resolves only in the aspect's own context, not once the text is copied into
    // the impl, so it is replaced by the impl's own definition of it (#1331). An
    // impl that does not define one is the impl's own error (`T0017`).
    let defined: HashMap<&str, &TypeExpr> = ib
        .assoc_type_defs
        .iter()
        .map(|d| (d.name.as_str(), &d.ty))
        .collect();
    if !assoc_names.iter().all(|a| defined.contains_key(a.as_str())) {
        return ib;
    }
    subst.extend(
        assoc_names
            .iter()
            .filter_map(|a| defined.get(a.as_str()).map(|ty| (a.as_str(), *ty))),
    );
    let provided: std::collections::HashSet<String> =
        ib.methods.iter().map(|m| m.name.clone()).collect();
    let mut offset = 0usize;
    for method in methods {
        let Some(body) = method.default_body.clone() else {
            continue;
        };
        if provided.contains(&method.name) {
            continue;
        }
        // On a non-generic target the pre-registered monomorphic signature serves
        // a default, except one with generics of its own: that would pin the
        // method's own parameter at its first call (metel-core#1332), so it is
        // written out as an ordinary generic method instead.
        // The same goes for any default of an aspect with type parameters: the
        // pre-registered signature still names the aspect's own `T` (#1330).
        if !generic_target
            && method.generics.is_empty()
            && aspect_params.is_empty()
            && assoc_names.is_empty()
        {
            continue;
        }
        offset += 1;
        ib.methods.push(FunDecl {
            visibility: Visibility::Private,
            name: method.name,
            generics: method.generics,
            where_clause: None,
            params: method
                .params
                .into_iter()
                .map(|mut p| {
                    p.type_ann = p.type_ann.map(|ty| substitute_type_params(&ty, &subst));
                    p
                })
                .collect(),
            return_type: method
                .return_type
                .map(|ty| substitute_type_params(&ty, &subst)),
            native: None,
            body: {
                // The default's own body can annotate with the aspect's parameter or
                // associated type too (`let x: T := ..`); a body the substitution cannot
                // rewrite is kept as written and reported by the checker.
                let mut rewritten = body.clone();
                if crate::pipeline::parsing::type_alias::substitute_type_names_in_block(
                    &mut rewritten,
                    &subst,
                )
                .is_ok()
                {
                    rewritten
                } else {
                    body
                }
            },
            span: Span {
                start: ib.span.start,
                end: ib.span.start + offset,
                filename: ib.span.filename.clone(),
                line: ib.span.line,
                col: ib.span.col,
            },
        });
    }
    ib
}

fn lower_impl_aspects_in_program(program: Program) -> Program {
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
        Decl::Let(let_decl) => Decl::Let(crate::data::ast::LetDecl {
            type_ann: let_decl.type_ann.as_ref().map(|t| {
                lower_projections_in_type(t, &std::collections::HashSet::new(), &let_decl.span)
            }),
            value: lower_projections_in_expr(&let_decl.value, &std::collections::HashSet::new()),
            ..let_decl
        }),
        Decl::Mut(mut_decl) => Decl::Mut(crate::data::ast::MutDecl {
            type_ann: mut_decl.type_ann.as_ref().map(|t| {
                lower_projections_in_type(t, &std::collections::HashSet::new(), &mut_decl.span)
            }),
            value: lower_projections_in_expr(&mut_decl.value, &std::collections::HashSet::new()),
            ..mut_decl
        }),
        Decl::Impl(ib) => Decl::Impl(crate::data::ast::ImplBlock {
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
        // An aspect's own signatures and default bodies: `Self::Item` and `P::Item` for a
        // type parameter `P` of the aspect or the method.
        Decl::Aspect(ad) => Decl::Aspect(crate::data::ast::AspectDecl {
            methods: ad
                .methods
                .iter()
                .map(|m| lower_projections_in_aspect_method(m, &ad.generics))
                .collect(),
            ..ad
        }),
        other => other,
    }
}

/// `lower_projections_in_fun` for an aspect method, with `Self` and the aspect's type
/// parameters in scope: the method is lowered as a function and its pieces copied back.
fn lower_projections_in_aspect_method(
    method: &crate::data::ast::AspectMethod,
    aspect_generics: &[String],
) -> crate::data::ast::AspectMethod {
    use crate::data::ast::Visibility;
    let as_fun = FunDecl {
        visibility: Visibility::Private,
        name: method.name.clone(),
        generics: method.generics.clone(),
        where_clause: None,
        params: method.params.clone(),
        return_type: method.return_type.clone(),
        native: None,
        body: method
            .default_body
            .clone()
            .unwrap_or_else(|| crate::data::ast::Block {
                stmts: vec![],
                tail: None,
                span: method.span.clone(),
            }),
        span: method.span.clone(),
    };
    let mut names: std::collections::HashSet<String> = aspect_generics.iter().cloned().collect();
    names.insert("Self".to_string());
    let lowered = lower_projections_in_fun_with_generics(&as_fun, &names);
    crate::data::ast::AspectMethod {
        params: lowered.params,
        return_type: lowered.return_type,
        default_body: method.default_body.as_ref().map(|_| lowered.body),
        ..method.clone()
    }
}

fn lower_projections_in_block(
    block: &crate::data::ast::Block,
    generics: &std::collections::HashSet<String>,
) -> crate::data::ast::Block {
    crate::data::ast::Block {
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
        Decl::Let(let_decl) => Decl::Let(crate::data::ast::LetDecl {
            type_ann: let_decl
                .type_ann
                .as_ref()
                .map(|t| lower_projections_in_type(t, generics, &let_decl.span)),
            value: lower_projections_in_expr(&let_decl.value, generics),
            ..let_decl.clone()
        }),
        Decl::Mut(mut_decl) => Decl::Mut(crate::data::ast::MutDecl {
            type_ann: mut_decl
                .type_ann
                .as_ref()
                .map(|t| lower_projections_in_type(t, generics, &mut_decl.span)),
            value: lower_projections_in_expr(&mut_decl.value, generics),
            ..mut_decl.clone()
        }),
        Decl::Stmt(stmt) => Decl::Stmt(Box::new(lower_projections_in_stmt(stmt, generics))),
        Decl::Fun(fun) => Decl::Fun(lower_projections_in_fun_with_generics(fun, generics)),
        Decl::Impl(ib) => Decl::Impl(crate::data::ast::ImplBlock {
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
    stmt: &crate::data::ast::Stmt,
    generics: &std::collections::HashSet<String>,
) -> crate::data::ast::Stmt {
    match stmt {
        crate::data::ast::Stmt::While(ws) => {
            crate::data::ast::Stmt::While(crate::data::ast::WhileStmt {
                condition: lower_projections_in_expr(&ws.condition, generics),
                body: lower_projections_in_block(&ws.body, generics),
                span: ws.span.clone(),
            })
        }
        crate::data::ast::Stmt::For(fs) => {
            let init = fs.init.as_ref().map(|fi| match fi {
                crate::data::ast::ForInit::Let(l) => {
                    crate::data::ast::ForInit::Let(crate::data::ast::LetDecl {
                        type_ann: l
                            .type_ann
                            .as_ref()
                            .map(|t| lower_projections_in_type(t, generics, &l.span)),
                        value: lower_projections_in_expr(&l.value, generics),
                        ..l.clone()
                    })
                }
                crate::data::ast::ForInit::Mut(m) => {
                    crate::data::ast::ForInit::Mut(crate::data::ast::MutDecl {
                        type_ann: m
                            .type_ann
                            .as_ref()
                            .map(|t| lower_projections_in_type(t, generics, &m.span)),
                        value: lower_projections_in_expr(&m.value, generics),
                        ..m.clone()
                    })
                }
                crate::data::ast::ForInit::Expr(e) => {
                    crate::data::ast::ForInit::Expr(lower_projections_in_expr(e, generics))
                }
            });
            crate::data::ast::Stmt::For(Box::new(crate::data::ast::ForStmt {
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
        crate::data::ast::Stmt::ForIn(fis) => {
            crate::data::ast::Stmt::ForIn(Box::new(crate::data::ast::ForInStmt {
                binding: fis.binding.clone(),
                mutable: fis.mutable,
                iterable: lower_projections_in_expr(&fis.iterable, generics),
                body: lower_projections_in_block(&fis.body, generics),
                span: fis.span.clone(),
            }))
        }
        crate::data::ast::Stmt::Expr(e) => {
            crate::data::ast::Stmt::Expr(lower_projections_in_expr(e, generics))
        }
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
        Expr::Match(m) => Expr::Match(crate::data::ast::MatchExpr {
            scrutinee: Box::new(go(&m.scrutinee)),
            arms: m
                .arms
                .iter()
                .map(|a| crate::data::ast::MatchArm {
                    pattern: a.pattern.clone(),
                    guard: a.guard.as_ref().map(go),
                    body: lower_projections_in_block(&a.body, generics),
                    span: a.span.clone(),
                })
                .collect(),
            span: m.span.clone(),
        }),
        Expr::Tuple(es, s) => Expr::Tuple(es.iter().map(go).collect(), s.clone()),
        Expr::Array(es, s) => Expr::Array(es.iter().map(go).collect(), s.clone()),
        Expr::RecordLiteral {
            fields,
            spread,
            span,
        } => Expr::RecordLiteral {
            fields: fields
                .iter()
                .map(|(name, expr)| (name.clone(), go(expr)))
                .collect(),
            spread: spread.as_ref().map(|(expr, index, spread_span)| {
                (Box::new(go(expr)), *index, spread_span.clone())
            }),
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
        Expr::Return(re) => Expr::Return(crate::data::ast::ReturnExpr {
            value: re.value.as_ref().map(|v| Box::new(go(v))),
            span: re.span.clone(),
        }),
        Expr::Break(br) => Expr::Break(crate::data::ast::BreakExpr {
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
        Expr::RecordProjection {
            path,
            path_span,
            fields,
            span,
        } => Expr::RecordProjection {
            path: path.clone(),
            path_span: path_span.clone(),
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
            if let Some((base, assoc)) = name.split_once("::")
                && generics.contains(base)
            {
                return TypeExpr::Projection {
                    base: Box::new(TypeExpr::Named(base.to_string(), vec![])),
                    assoc_name: assoc.to_string(),
                    span: fallback_span.clone(),
                };
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
        // RFC-0121 installment 2: `Handle.{ fd, ..R }` names a struct and its
        // own field labels only -- no `T::AssocType`-shaped `Named` of its
        // own to lower.
        // RFC-0121 item 2 (metel-core#1310): `Session<..R>`'s row splice is
        // likewise a leaf -- no `T::AssocType`-shaped `Named` can hide
        // inside it. This runs before `projections::check` gets a chance
        // to reject a `RowArg`, so a leaf, not `unreachable!()`.
        TypeExpr::Projection { .. }
        | TypeExpr::RecordProjection { .. }
        | TypeExpr::OpenRecordProjection { .. }
        | TypeExpr::RowArg(_) => te.clone(),
        TypeExpr::DynAspect { bound, span } => TypeExpr::DynAspect {
            bound: Box::new(go(bound)),
            span: span.clone(),
        },
        // RFC-0121: a `fun_decl` parameter's own type can be `{ x: T::AssocType,
        // ..R }` just as legitimately as an ordinary `T::AssocType` elsewhere in
        // its signature -- lower each named field's type the same way; the tail
        // itself (`RowTail`) carries no `TypeExpr` to lower.
        TypeExpr::OpenRecord(fields, tail) => TypeExpr::OpenRecord(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), go(ty)))
                .collect(),
            tail.clone(),
        ),
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
fn lower_projections_in_program(program: Program) -> Program {
    let decls = program
        .decls
        .into_iter()
        .map(lower_projections_in_decl)
        .collect();
    Program { decls, ..program }
}

/// `ty` with every bare `Named(param, [])` replaced by its binding in `subst`.
fn substitute_type_params(
    ty: &TypeExpr,
    subst: &std::collections::HashMap<&str, &TypeExpr>,
) -> TypeExpr {
    let go = |t: &TypeExpr| substitute_type_params(t, subst);
    match ty {
        TypeExpr::Named(name, args) if args.is_empty() => subst
            .get(name.as_str())
            .map_or_else(|| ty.clone(), |replacement| (*replacement).clone()),
        TypeExpr::Named(name, args) => TypeExpr::Named(name.clone(), args.iter().map(go).collect()),
        TypeExpr::Tuple(items) => TypeExpr::Tuple(items.iter().map(go).collect()),
        TypeExpr::Record(fields) => {
            TypeExpr::Record(fields.iter().map(|(n, t)| (n.clone(), go(t))).collect())
        }
        TypeExpr::OpenRecord(fields, tail) => TypeExpr::OpenRecord(
            fields.iter().map(|(n, t)| (n.clone(), go(t))).collect(),
            tail.clone(),
        ),
        TypeExpr::Array(inner) => TypeExpr::Array(Box::new(go(inner))),
        TypeExpr::SizedArray(inner, n) => TypeExpr::SizedArray(Box::new(go(inner)), *n),
        TypeExpr::Reference(inner) => TypeExpr::Reference(Box::new(go(inner))),
        TypeExpr::MutReference(inner) => TypeExpr::MutReference(Box::new(go(inner))),
        TypeExpr::Fun {
            params,
            return_type,
            call_multiplicity,
            call_mutation,
        } => TypeExpr::Fun {
            params: params.iter().map(go).collect(),
            return_type: return_type.as_deref().map(|r| Box::new(go(r))),
            call_multiplicity: *call_multiplicity,
            call_mutation: *call_mutation,
        },
        // `Self::Item` (a default lowered with its aspect's projections) names the same
        // associated type the bare spelling does
        TypeExpr::Projection {
            base, assoc_name, ..
        } if matches!(base.as_ref(), TypeExpr::Named(n, a) if n == "Self" && a.is_empty())
            && subst.contains_key(assoc_name.as_str()) =>
        {
            (*subst[assoc_name.as_str()]).clone()
        }
        TypeExpr::Projection {
            base,
            assoc_name,
            span,
        } => TypeExpr::Projection {
            base: Box::new(go(base)),
            assoc_name: assoc_name.clone(),
            span: span.clone(),
        },
        TypeExpr::DynAspect { bound, span } => TypeExpr::DynAspect {
            bound: Box::new(go(bound)),
            span: span.clone(),
        },
        TypeExpr::ImplAspect { .. }
        | TypeExpr::RecordProjection { .. }
        | TypeExpr::OpenRecordProjection { .. }
        | TypeExpr::RowArg(_)
        | TypeExpr::Unit => ty.clone(),
    }
}
