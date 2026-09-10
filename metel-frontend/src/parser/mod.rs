use pest::iterators::Pairs;
use pest::Parser;
use pest_derive::Parser;

use crate::ast::{
    AspectDecl, AspectMethod, AssignOp, AssignTarget, AssocTypeDecl, AssocTypeDef, BinOp, Block,
    Bound, BoundHead, BreakExpr, CaptureSpec, Decl, EnumDecl, ExportDecl, Expr, FieldDef,
    ForInStmt, ForInit, ForStmt, FunDecl, GenericParam, ImplBlock, ImportDecl, ImportPath,
    ImportTree, LetDecl, Literal, MatchArm, MatchExpr, MutDecl, NativeBinding, Param, PathRoot,
    Pattern, Polarity, Program, ReceiverKind, ReturnExpr, RowBound, RowBoundField, Span, Stmt,
    StructDecl, TypeExpr, UnaryOp, VariantDef, Visibility, WhereClause, WhereConstraint, WhileStmt,
};
use crate::error::{MetelError, ParseErrorCode};
use crate::types::{CallMultiplicity, CallMutation};

#[derive(Parser)]
#[grammar = "grammar.pest"]
/// The pest grammar entry point. `pub` so migration/lint tooling can walk the
/// concrete parse tree (with token spans) that the AST throws away — e.g. the
/// RFC-0136 `=` → `:=` rewriter in `examples/`.
pub struct MetelParser;

/// Parse a Metel source string into an untyped AST.
///
/// # Errors
/// Returns an error if `source` does not conform to the Metel grammar.
pub fn parse(source: &str, filename: &str) -> Result<Program, MetelError> {
    let mut pairs = MetelParser::parse(Rule::program, source).map_err(|e| {
        let (start, end) = match e.location {
            pest::error::InputLocation::Pos(p) => (p, p),
            pest::error::InputLocation::Span((s, e)) => (s, e),
        };
        let (line, col) = match &e.line_col {
            pest::error::LineColLocation::Pos((l, c))
            | pest::error::LineColLocation::Span((l, c), _) => (*l as u32, *c as u32),
        };
        MetelError::ParseError {
            code: ParseErrorCode::P0001,
            message: e.variant.to_string(),
            start,
            end,
            filename: filename.to_string(),
            line,
            col,
            source_line: Some(e.line().to_string()),
        }
    })?;

    parse_program(&mut pairs, filename)
}

fn parse_program(pairs: &mut Pairs<Rule>, filename: &str) -> Result<Program, MetelError> {
    let program_pair = pairs
        .next()
        .ok_or_else(|| MetelError::internal("parse_program: no program rule from pest"))?;
    if program_pair.as_rule() != Rule::program {
        return Err(MetelError::internal(
            "parse_program: first rule is not program",
        ));
    }
    let mut imports = Vec::new();
    let mut exports = Vec::new();
    let mut decls = Vec::new();
    for pair in program_pair.into_inner() {
        match pair.as_rule() {
            Rule::import_decl => imports.push(parse_import_decl(pair, filename)?),
            Rule::export_decl => exports.push(parse_export_decl(pair, filename)?),
            Rule::decl => decls.extend(parse_decl(pair, filename)?),
            _ => {}
        }
    }
    Ok(Program {
        imports,
        exports,
        decls,
    })
}

fn parse_import_decl(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<ImportDecl, MetelError> {
    let span = Span::of(&pair, filename);
    let path_pair = pair
        .into_inner()
        .next()
        .ok_or_else(|| MetelError::internal("import_decl: expected import path"))?;
    Ok(ImportDecl {
        path: parse_import_path(path_pair)?,
        span,
    })
}

fn parse_export_decl(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<ExportDecl, MetelError> {
    let span = Span::of(&pair, filename);
    let path_pair = pair
        .into_inner()
        .next()
        .ok_or_else(|| MetelError::internal("export_decl: expected import path"))?;
    Ok(ExportDecl {
        path: parse_import_path(path_pair)?,
        span,
    })
}

fn parse_import_path(pair: pest::iterators::Pair<Rule>) -> Result<ImportPath, MetelError> {
    let mut inner = pair.into_inner();
    let root_pair = inner
        .next()
        .ok_or_else(|| MetelError::internal("import_path: expected path root"))?;
    let tree_pair = inner
        .next()
        .ok_or_else(|| MetelError::internal("import_path: expected import tree"))?;
    Ok(ImportPath {
        root: parse_path_root(root_pair)?,
        tree: parse_import_tree(tree_pair)?,
    })
}

fn parse_path_root(pair: pest::iterators::Pair<Rule>) -> Result<PathRoot, MetelError> {
    match pair.as_rule() {
        Rule::path_root => {
            let inner = pair
                .into_inner()
                .next()
                .ok_or_else(|| MetelError::internal("path_root: expected inner root"))?;
            parse_path_root(inner)
        }
        Rule::root_kw => Ok(PathRoot::Root),
        Rule::std_kw => Ok(PathRoot::Std),
        Rule::self_kw => Ok(PathRoot::Self_),
        Rule::super_kw => Ok(PathRoot::Super),
        Rule::ident => Ok(PathRoot::Name(pair.as_str().to_string())),
        r => Err(MetelError::internal(format!(
            "path_root: unexpected rule {r:?}"
        ))),
    }
}

fn parse_import_tree(pair: pest::iterators::Pair<Rule>) -> Result<ImportTree, MetelError> {
    if pair.as_str().trim() == "*" {
        return Ok(ImportTree::Glob);
    }
    let mut inner = pair.into_inner();
    let first = inner
        .next()
        .ok_or_else(|| MetelError::internal("import_tree: expected import item"))?;
    match first.as_rule() {
        Rule::ident => {
            let name = first.as_str().to_string();
            match inner.next() {
                Some(second) if second.as_rule() == Rule::ident => Ok(ImportTree::Name {
                    name,
                    alias: Some(second.as_str().to_string()),
                }),
                Some(second) if second.as_rule() == Rule::import_tree => Ok(ImportTree::Path {
                    name,
                    tree: Box::new(parse_import_tree(second)?),
                }),
                Some(second) => Err(MetelError::internal(format!(
                    "import_tree: unexpected rule after name {:?}",
                    second.as_rule()
                ))),
                None => Ok(ImportTree::Name { name, alias: None }),
            }
        }
        Rule::import_item => {
            // Group opening item — collect all import_items as a Group
            let first_tree = parse_import_item(first)?;
            let mut trees = vec![first_tree];
            for p in inner {
                if p.as_rule() == Rule::import_item {
                    trees.push(parse_import_item(p)?);
                }
            }
            Ok(ImportTree::Group(trees))
        }
        r => Err(MetelError::internal(format!(
            "import_tree: unexpected rule {r:?}"
        ))),
    }
}

fn parse_import_item(pair: pest::iterators::Pair<Rule>) -> Result<ImportTree, MetelError> {
    let mut inner = pair.into_inner();
    let name = inner
        .next()
        .ok_or_else(|| MetelError::internal("import_item: expected name"))?
        .as_str()
        .to_string();
    let alias = inner.next().map(|p| p.as_str().to_string());
    Ok(ImportTree::Name { name, alias })
}

fn parse_decl(pair: pest::iterators::Pair<Rule>, filename: &str) -> Result<Vec<Decl>, MetelError> {
    // `decl` has exactly one child
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| MetelError::internal("decl: missing inner rule"))?;
    if inner.as_rule() == Rule::impl_block {
        return Ok(parse_impl_block(inner, filename)?
            .into_iter()
            .map(Decl::Impl)
            .collect());
    }
    Ok(vec![parse_single_decl(inner, filename)?])
}

fn parse_single_decl(
    inner: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Decl, MetelError> {
    match inner.as_rule() {
        Rule::let_decl => Ok(Decl::Let(parse_let_decl(inner, filename)?)),
        Rule::let_mut_decl => Ok(Decl::Mut(parse_mut_decl(inner, filename)?)),
        Rule::fun_decl => Ok(Decl::Fun(parse_fun_decl(inner, filename)?)),
        Rule::struct_decl => Ok(Decl::Struct(parse_struct_decl(inner, filename)?)),
        Rule::enum_decl => Ok(Decl::Enum(parse_enum_decl(inner, filename)?)),
        Rule::aspect_decl => Ok(Decl::Aspect(parse_aspect_decl(inner, filename)?)),
        Rule::type_alias => Ok(Decl::TypeAlias(parse_type_alias(inner, filename)?)),
        Rule::stmt => Ok(Decl::Stmt(Box::new(parse_stmt(inner, filename)?))),
        r => Err(MetelError::internal(format!("decl: unexpected rule {r:?}"))),
    }
}

fn parse_let_decl(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<LetDecl, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let name = inner
        .next()
        .ok_or_else(|| MetelError::internal("let_decl: expected identifier"))?
        .as_str()
        .to_string();
    let (type_ann, value) = parse_opt_type_then_expr(&mut inner, filename)?;
    Ok(LetDecl {
        name,
        type_ann,
        value,
        span,
    })
}

fn parse_mut_decl(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<MutDecl, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let first = inner
        .next()
        .ok_or_else(|| MetelError::internal("mut_decl: expected identifier"))?;
    let name = if first.as_rule() == Rule::mut_kw {
        inner
            .next()
            .ok_or_else(|| MetelError::internal("mut_decl: expected identifier after var"))?
            .as_str()
            .to_string()
    } else {
        first.as_str().to_string()
    };
    let (type_ann, value) = parse_opt_type_then_expr(&mut inner, filename)?;
    Ok(MutDecl {
        name,
        type_ann,
        value,
        span,
    })
}

/// Shared helper: parse `(":" type_expr)? expr` from a pair iterator.
fn parse_opt_type_then_expr(
    inner: &mut pest::iterators::Pairs<Rule>,
    filename: &str,
) -> Result<(Option<TypeExpr>, Expr), MetelError> {
    let next = inner
        .next()
        .ok_or_else(|| MetelError::internal("expected type annotation or expression"))?;
    match next.as_rule() {
        Rule::type_expr => {
            let type_ann = Some(parse_type_expr(next, filename)?);
            let expr_pair = inner
                .next()
                .ok_or_else(|| MetelError::internal("expected expression after type annotation"))?;
            let value = parse_expr(expr_pair, filename)?;
            Ok((type_ann, value))
        }
        Rule::expr => Ok((None, parse_expr(next, filename)?)),
        r => Err(MetelError::internal(format!(
            "expected type_expr or expr, got {r:?}"
        ))),
    }
}

fn parse_fun_decl(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<FunDecl, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner().peekable();

    // Optional `native(@…)` host-binding attribute.
    let mut native = None;
    if inner.peek().map(pest::iterators::Pair::as_rule) == Some(Rule::native_attr) {
        let attr = inner.next().unwrap();
        let attr_span = Span::of(&attr, filename);
        let path_pair = attr
            .into_inner()
            .find(|p| p.as_rule() == Rule::native_path)
            .ok_or_else(|| MetelError::internal("native_attr: expected native_path"))?;
        let key_path = path_pair.as_str().split('.').map(str::to_string).collect();
        native = Some(NativeBinding {
            key_path,
            span: attr_span,
        });
    }

    let first = inner
        .next()
        .ok_or_else(|| MetelError::internal("fun_decl: expected function name"))?;
    let (visibility, name) = if first.as_rule() == Rule::pub_kw {
        let n = inner
            .next()
            .ok_or_else(|| MetelError::internal("fun_decl: expected name after public"))?
            .as_str()
            .to_string();
        (Visibility::Public, n)
    } else {
        (Visibility::Private, first.as_str().to_string())
    };
    let mut generics = vec![];
    let mut where_clause = None;
    let mut params = vec![];
    let mut return_type = None;
    let mut body = None;
    for p in inner {
        match p.as_rule() {
            Rule::generic_params => generics = parse_generic_params(p, filename)?,
            Rule::where_clause => where_clause = Some(parse_where_clause(p, filename)?),
            Rule::param_list => params = parse_param_list(p, filename)?,
            Rule::type_expr => return_type = Some(parse_type_expr(p, filename)?),
            Rule::block => body = Some(parse_block(p, filename)?),
            _ => {}
        }
    }

    // A native function has no block body (`;`); other functions require one.
    let body = match (native.is_some(), body) {
        (true, Some(_)) => {
            return Err(MetelError::parse(
                ParseErrorCode::P0001,
                "a `native` function must not have a body block",
                &span,
            ))
        }
        (true, None) => empty_block(&span),
        (false, Some(b)) => b,
        (false, None) => {
            return Err(MetelError::parse(
                ParseErrorCode::P0001,
                "function requires a body block",
                &span,
            ))
        }
    };

    Ok(FunDecl {
        visibility,
        name,
        generics,
        where_clause,
        params,
        return_type,
        native,
        body,
        span,
    })
}

/// An empty placeholder block for `native` functions, which have no body.
fn empty_block(span: &Span) -> Block {
    Block {
        stmts: vec![],
        tail: None,
        span: span.clone(),
    }
}

fn parse_struct_decl(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<StructDecl, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let first = inner
        .next()
        .ok_or_else(|| MetelError::internal("struct_decl: expected name"))?;
    let (visibility, name) = if first.as_rule() == Rule::pub_kw {
        let n = inner
            .next()
            .ok_or_else(|| MetelError::internal("struct_decl: expected name after public"))?
            .as_str()
            .to_string();
        (Visibility::Public, n)
    } else {
        (Visibility::Private, first.as_str().to_string())
    };
    let mut generics = vec![];
    let mut where_clause = None;
    let mut fields = vec![];
    for p in inner {
        match p.as_rule() {
            Rule::generic_params => generics = parse_generic_params(p, filename)?,
            Rule::where_clause => where_clause = Some(parse_where_clause(p, filename)?),
            Rule::struct_fields => fields = parse_struct_fields(p, filename)?,
            _ => {}
        }
    }
    Ok(StructDecl {
        visibility,
        name,
        generics,
        where_clause,
        fields,
        span,
    })
}

fn parse_enum_decl(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<EnumDecl, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let first = inner
        .next()
        .ok_or_else(|| MetelError::internal("enum_decl: expected name"))?;
    let (visibility, name) = if first.as_rule() == Rule::pub_kw {
        let n = inner
            .next()
            .ok_or_else(|| MetelError::internal("enum_decl: expected name after public"))?
            .as_str()
            .to_string();
        (Visibility::Public, n)
    } else {
        (Visibility::Private, first.as_str().to_string())
    };
    let mut generics = vec![];
    let mut where_clause = None;
    let mut variants = vec![];
    for p in inner {
        match p.as_rule() {
            Rule::generic_params => generics = parse_generic_params(p, filename)?,
            Rule::where_clause => where_clause = Some(parse_where_clause(p, filename)?),
            Rule::enum_variants => {
                for v in p.into_inner() {
                    if v.as_rule() == Rule::enum_variant {
                        variants.push(parse_enum_variant(v, filename)?);
                    }
                }
            }
            _ => {}
        }
    }
    Ok(EnumDecl {
        visibility,
        name,
        generics,
        where_clause,
        variants,
        span,
    })
}

fn parse_impl_block(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Vec<ImplBlock>, MetelError> {
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| MetelError::internal("impl_block: expected inner impl form"))?;
    match inner.as_rule() {
        Rule::extend_impl_block => parse_extend_impl_block(inner, filename),
        r => Err(MetelError::internal(format!(
            "impl_block: unexpected inner rule {r:?}"
        ))),
    }
}

#[allow(clippy::too_many_lines)]
fn parse_extend_impl_block(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Vec<ImplBlock>, MetelError> {
    let span = Span::of(&pair, filename);
    let mut generics = vec![];
    let mut target_type = None;
    let mut where_clause = None;
    let mut assoc_type_defs = vec![];
    let mut methods = vec![];
    let mut aspects = vec![];
    let mut bodyless = false;

    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::generic_params => generics = parse_generic_params(p, filename)?,
            Rule::type_expr => target_type = Some(parse_type_expr(p, filename)?),
            Rule::extend_impl_bodyless => {
                bodyless = true;
                for inner in p.into_inner() {
                    match inner.as_rule() {
                        Rule::extend_aspect_list => {
                            aspects = parse_extend_aspect_list(inner, filename)?;
                        }
                        Rule::where_clause => {
                            where_clause = Some(parse_where_clause(inner, filename)?);
                        }
                        _ => {}
                    }
                }
            }
            Rule::extend_impl_braced => {
                for inner in p.into_inner() {
                    match inner.as_rule() {
                        Rule::extend_aspect => aspects.push(parse_extend_aspect(inner, filename)?),
                        Rule::where_clause => {
                            where_clause = Some(parse_where_clause(inner, filename)?);
                        }
                        Rule::assoc_type_def => {
                            assoc_type_defs.push(parse_assoc_type_def(inner, filename)?);
                        }
                        Rule::fun_decl => methods.push(parse_fun_decl(inner, filename)?),
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }

    let target_type = target_type
        .ok_or_else(|| MetelError::internal("extend_impl_block: missing target type"))?;

    if bodyless {
        if aspects.is_empty() {
            return Err(MetelError::parse(
                ParseErrorCode::P0001,
                "a bodyless `extend` requires at least one aspect",
                &span,
            ));
        }
        if aspects.len() > 1 && where_clause.is_some() {
            return Err(MetelError::parse(
                ParseErrorCode::P0001,
                "a multi-aspect bodyless `extend` cannot carry a where-clause",
                &span,
            ));
        }

        return aspects
            .into_iter()
            .map(|(polarity, aspect_name, aspect_type_args)| {
                Ok(ImplBlock {
                    polarity,
                    generics: generics.clone(),
                    aspect_name: Some(aspect_name),
                    aspect_type_args,
                    target_type: target_type.clone(),
                    where_clause: where_clause.clone(),
                    assoc_type_defs: vec![],
                    methods: vec![],
                    span: span.clone(),
                })
            })
            .collect();
    }

    if aspects.len() > 1 {
        return Err(MetelError::parse(
            ParseErrorCode::P0001,
            "a braced `extend` can target at most one aspect",
            &span,
        ));
    }

    if let Some((polarity, _, _)) = aspects.first() {
        if *polarity == Polarity::Negative {
            return Err(MetelError::parse(
                ParseErrorCode::P0001,
                "a negative `extend` must use the bodyless `;` form",
                &span,
            ));
        }
    }

    let (aspect_name, aspect_type_args) = match aspects.into_iter().next() {
        Some((_, name, args)) => (Some(name), args),
        None => (None, vec![]),
    };

    Ok(vec![ImplBlock {
        polarity: Polarity::Positive,
        generics,
        aspect_name,
        aspect_type_args,
        target_type,
        where_clause,
        assoc_type_defs,
        methods,
        span,
    }])
}

fn parse_extend_aspect_list(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Vec<(Polarity, String, Vec<TypeExpr>)>, MetelError> {
    pair.into_inner()
        .filter(|p| p.as_rule() == Rule::extend_aspect)
        .map(|p| parse_extend_aspect(p, filename))
        .collect()
}

fn parse_extend_aspect(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<(Polarity, String, Vec<TypeExpr>), MetelError> {
    let mut polarity = Polarity::Positive;
    let mut aspect_name = None;
    let mut aspect_type_args = vec![];

    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::bang => polarity = Polarity::Negative,
            Rule::named_type => {
                let mut inner_pairs = p.into_inner();
                let path_pair = inner_pairs.next().ok_or_else(|| {
                    MetelError::internal("extend_aspect: expected aspect type path")
                })?;
                aspect_name = Some(collect_path_components(path_pair)?.join("::"));
                for tp in inner_pairs {
                    if tp.as_rule() == Rule::type_args {
                        for arg in tp.into_inner() {
                            if arg.as_rule() == Rule::type_expr {
                                aspect_type_args.push(parse_type_expr(arg, filename)?);
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    Ok((
        polarity,
        aspect_name.ok_or_else(|| MetelError::internal("extend_aspect: missing aspect name"))?,
        aspect_type_args,
    ))
}

fn parse_param_list(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Vec<Param>, MetelError> {
    let mut params = vec![];
    for p in pair.into_inner() {
        if p.as_rule() == Rule::param {
            params.push(parse_param(p, filename)?);
        }
    }
    Ok(params)
}

fn parse_param(pair: pest::iterators::Pair<Rule>, filename: &str) -> Result<Param, MetelError> {
    let span = Span::of(&pair, filename);
    let text = pair.as_str().trim();
    if text == "self" {
        return Ok(Param {
            mutable: false,
            receiver: Some(ReceiverKind::Value),
            name: "self".into(),
            type_ann: None,
            span,
        });
    }
    if text == "&self" {
        return Ok(Param {
            mutable: false,
            receiver: Some(ReceiverKind::Ref),
            name: "self".into(),
            type_ann: None,
            span,
        });
    }
    if text == "&var self" {
        return Ok(Param {
            mutable: false,
            receiver: Some(ReceiverKind::RefMut),
            name: "self".into(),
            type_ann: None,
            span,
        });
    }
    // ident (":" type_expr)?
    let mut inner = pair.into_inner();
    let name = inner
        .next()
        .ok_or_else(|| MetelError::internal("param: expected name"))?
        .as_str()
        .to_string();
    let type_ann = inner
        .next()
        .map(|p| parse_type_expr(p, filename))
        .transpose()?;
    Ok(Param {
        mutable: false,
        receiver: None,
        name,
        type_ann,
        span,
    })
}

fn parse_struct_fields(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Vec<FieldDef>, MetelError> {
    let mut fields = vec![];
    for p in pair.into_inner() {
        if p.as_rule() == Rule::struct_field {
            let span = Span::of(&p, filename);
            let mut it = p.into_inner();
            let first = it
                .next()
                .ok_or_else(|| MetelError::internal("struct_field: expected field head"))?;
            let (visibility, name_pair) = if first.as_rule() == Rule::pub_kw {
                (
                    Visibility::Public,
                    it.next().ok_or_else(|| {
                        MetelError::internal("struct_field: expected name after public")
                    })?,
                )
            } else {
                (Visibility::Private, first)
            };
            let name = name_pair.as_str().to_string();
            let type_ann = parse_type_expr(
                it.next()
                    .ok_or_else(|| MetelError::internal("struct_field: expected type"))?,
                filename,
            )?;
            fields.push(FieldDef {
                visibility,
                name,
                type_ann,
                span,
            });
        }
    }
    Ok(fields)
}

fn parse_enum_variant(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<VariantDef, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let name = inner
        .next()
        .ok_or_else(|| MetelError::internal("enum_variant: expected name"))?
        .as_str()
        .to_string();
    let mut fields = vec![];
    for p in inner {
        if p.as_rule() == Rule::struct_fields {
            fields = parse_struct_fields(p, filename)?;
        }
    }
    Ok(VariantDef { name, fields, span })
}

fn parse_aspect_method(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<AspectMethod, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let name = inner
        .next()
        .ok_or_else(|| MetelError::internal("aspect_method: expected name"))?
        .as_str()
        .to_string();
    let mut generics = vec![];
    let mut params = vec![];
    let mut return_type = None;
    let mut default_body = None;
    for p in inner {
        match p.as_rule() {
            Rule::generic_params => generics = parse_generic_params(p, filename)?,
            Rule::param_list => params = parse_param_list(p, filename)?,
            Rule::type_expr => return_type = Some(parse_type_expr(p, filename)?),
            Rule::block => default_body = Some(parse_block(p, filename)?),
            _ => {}
        }
    }
    Ok(AspectMethod {
        name,
        generics,
        params,
        return_type,
        default_body,
        span,
    })
}

fn parse_stmt(pair: pest::iterators::Pair<Rule>, filename: &str) -> Result<Stmt, MetelError> {
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| MetelError::internal("stmt: missing inner rule"))?;
    match inner.as_rule() {
        Rule::while_stmt => Ok(Stmt::While(parse_while_stmt(inner, filename)?)),
        Rule::for_stmt => Ok(Stmt::For(Box::new(parse_for_stmt(inner, filename)?))),
        Rule::for_in_stmt => Ok(Stmt::ForIn(Box::new(parse_for_in_stmt(inner, filename)?))),
        Rule::expr_stmt => {
            let expr_pair = inner
                .into_inner()
                .next()
                .ok_or_else(|| MetelError::internal("expr_stmt: missing expression"))?;
            Ok(Stmt::Expr(parse_expr(expr_pair, filename)?))
        }
        r => Err(MetelError::internal(format!("stmt: unexpected rule {r:?}"))),
    }
}

fn parse_while_stmt(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<WhileStmt, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let condition = parse_expr(
        inner
            .next()
            .ok_or_else(|| MetelError::internal("while_stmt: expected condition"))?,
        filename,
    )?;
    let body = parse_block(
        inner
            .next()
            .ok_or_else(|| MetelError::internal("while_stmt: expected body"))?,
        filename,
    )?;
    Ok(WhileStmt {
        condition,
        body,
        span,
    })
}

fn parse_for_stmt(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<ForStmt, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();

    // for_init
    let init_pair = inner
        .next()
        .ok_or_else(|| MetelError::internal("for_stmt: expected init"))?;
    let init = if init_pair.as_rule() == Rule::for_init {
        match init_pair.into_inner().next() {
            Some(p) => match p.as_rule() {
                Rule::let_decl => Some(ForInit::Let(parse_let_decl(p, filename)?)),
                Rule::let_mut_decl => Some(ForInit::Mut(parse_mut_decl(p, filename)?)),
                Rule::expr_stmt => {
                    let ep = p.into_inner().next().ok_or_else(|| {
                        MetelError::internal("for_stmt: expected expr in expr_stmt")
                    })?;
                    Some(ForInit::Expr(parse_expr(ep, filename)?))
                }
                _ => None, // bare ";"
            },
            None => None,
        }
    } else {
        None
    };

    // condition and step are optional `expr` pairs; body is a `block`
    let mut condition = None;
    let mut step = None;
    let mut body = None;
    for p in inner {
        match p.as_rule() {
            Rule::expr => {
                if condition.is_none() {
                    condition = Some(parse_expr(p, filename)?);
                } else {
                    step = Some(parse_expr(p, filename)?);
                }
            }
            Rule::block => body = Some(parse_block(p, filename)?),
            _ => {}
        }
    }
    Ok(ForStmt {
        init,
        condition,
        step,
        body: body.ok_or_else(|| MetelError::internal("for_stmt: missing body"))?,
        span,
    })
}

fn parse_return_expr(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<ReturnExpr, MetelError> {
    let span = Span::of(&pair, filename);
    // `.into_inner()`'s first pair is the atomic `return_kw` marker (needed for
    // its own word-boundary lookahead, see grammar.pest) — skip to the actual
    // `expr` pair, if the value was present at all.
    let value = pair
        .into_inner()
        .find(|p| p.as_rule() == Rule::expr)
        .map(|p| parse_expr(p, filename).map(Box::new))
        .transpose()?;
    Ok(ReturnExpr { value, span })
}

fn parse_break_expr(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<BreakExpr, MetelError> {
    let span = Span::of(&pair, filename);
    let value = pair
        .into_inner()
        .find(|p| p.as_rule() == Rule::expr)
        .map(|p| parse_expr(p, filename).map(Box::new))
        .transpose()?;
    Ok(BreakExpr { value, span })
}

/// Entry point: consumes one `expr` pair.
fn parse_expr(pair: pest::iterators::Pair<Rule>, filename: &str) -> Result<Expr, MetelError> {
    match pair.as_rule() {
        Rule::expr => {
            let inner = pair
                .into_inner()
                .next()
                .ok_or_else(|| MetelError::internal("expr: missing inner rule"))?;
            parse_expr(inner, filename)
        }
        Rule::assign_expr => parse_assign_expr(pair, filename),
        Rule::or_expr
        | Rule::and_expr
        | Rule::cmp_expr
        | Rule::range_expr
        | Rule::add_expr
        | Rule::mul_expr => parse_lr_binary(pair, filename),
        Rule::cast_expr => parse_cast_expr(pair, filename),
        Rule::asc_expr => parse_asc_expr(pair, filename),
        Rule::unary_expr => parse_unary_expr(pair, filename),
        Rule::postfix_expr => parse_postfix_expr(pair, filename),
        Rule::primary_expr => {
            let inner = pair
                .into_inner()
                .next()
                .ok_or_else(|| MetelError::internal("primary_expr: missing inner rule"))?;
            parse_expr(inner, filename)
        }
        // Terminals and composites reachable from primary_expr
        Rule::int_lit
        | Rule::float_lit
        | Rule::string_lit
        | Rule::char_lit
        | Rule::bool_lit
        | Rule::unit_lit
        | Rule::int_lit_suffixed
        | Rule::float_lit_suffixed => parse_literal_expr(&pair, filename),
        Rule::path_expr => parse_path_expr(pair, filename),
        Rule::tuple_or_paren => parse_tuple_or_paren(pair, filename),
        Rule::array_lit => parse_array_lit(pair, filename),
        Rule::repeat_array => parse_repeat_array(pair, filename),
        Rule::match_expr => Ok(Expr::Match(parse_match_expr(pair, filename)?)),
        Rule::if_expr => parse_if_expr(pair, filename),
        Rule::loop_expr => parse_loop_expr(pair, filename),
        Rule::return_expr => Ok(Expr::Return(parse_return_expr(pair, filename)?)),
        Rule::break_expr => Ok(Expr::Break(parse_break_expr(pair, filename)?)),
        Rule::continue_expr => Ok(Expr::Continue(Span::of(&pair, filename))),
        Rule::closure_expr => parse_closure_expr(pair, filename),
        Rule::record_lit => parse_record_literal(pair, filename),
        Rule::record_projection_expr => parse_record_projection_expr(pair, filename),
        Rule::struct_literal => parse_struct_literal(pair, filename),
        r => Err(MetelError::internal(format!(
            "parse_expr: unexpected rule {r:?}"
        ))),
    }
}

// Exhaustive match over every AST/type-system variant; splitting it up would
// scatter one coherent dispatch table across many small functions with no
// real gain in clarity.
#[allow(clippy::too_many_lines)]
fn parse_literal_expr(
    pair: &pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Expr, MetelError> {
    use crate::ast::{FloatKind, IntKind};
    let span = Span::of(pair, filename);
    let text = pair.as_str();
    let lit = match pair.as_rule() {
        Rule::int_lit => {
            Literal::Int(
                text.replace('_', "")
                    .parse()
                    .map_err(|_| MetelError::ParseError {
                        code: ParseErrorCode::P0002,
                        message: format!("integer literal '{text}' is out of range for i64"),
                        start: span.start,
                        end: span.end,
                        filename: filename.to_string(),
                        line: span.line,
                        col: span.col,
                        source_line: None,
                    })?,
            )
        }
        Rule::float_lit => Literal::Float(text.parse().map_err(|_| MetelError::ParseError {
            code: ParseErrorCode::P0003,
            message: format!("invalid float literal '{text}'"),
            start: span.start,
            end: span.end,
            filename: filename.to_string(),
            line: span.line,
            col: span.col,
            source_line: None,
        })?),
        Rule::int_lit_suffixed => {
            // Split digits from suffix: find the first non-digit, non-underscore character.
            let (suffix, digits_end) =
                if let Some(pos) = text.find(|c: char| !c.is_ascii_digit() && c != '_') {
                    (&text[pos..], pos)
                } else {
                    (text, 0)
                };
            let digits = text[..digits_end].replace('_', "");
            let kind = match suffix {
                "i8" => IntKind::I8,
                "i16" => IntKind::I16,
                "i32" => IntKind::I32,
                "i64" => IntKind::I64,
                "u8" => IntKind::U8,
                "u16" => IntKind::U16,
                "u32" => IntKind::U32,
                "u64" => IntKind::U64,
                _ => {
                    return Err(MetelError::internal(format!(
                        "unknown int suffix '{suffix}'"
                    )))
                }
            };
            let value: i128 = digits.parse().map_err(|_| MetelError::ParseError {
                code: ParseErrorCode::P0002,
                message: format!("integer literal '{text}' is too large"),
                start: span.start,
                end: span.end,
                filename: filename.to_string(),
                line: span.line,
                col: span.col,
                source_line: None,
            })?;
            let in_range = match kind {
                // Allow abs(MIN) so that e.g. `-128i8` and `-32768i16` parse correctly;
                // the extra value wraps to MIN via the two's-complement cast in the evaluator.
                IntKind::I8 => value <= i128::from(i8::MAX) + 1,
                IntKind::I16 => value <= i128::from(i16::MAX) + 1,
                IntKind::I32 => value <= i128::from(i32::MAX) + 1,
                IntKind::I64 => value <= i128::from(i64::MAX) + 1,
                IntKind::U8 => value <= i128::from(u8::MAX),
                IntKind::U16 => value <= i128::from(u16::MAX),
                IntKind::U32 => value <= i128::from(u32::MAX),
                IntKind::U64 => value <= i128::from(u64::MAX),
            };
            if !in_range {
                return Err(MetelError::ParseError {
                    code: ParseErrorCode::P0002,
                    message: format!("literal '{text}' is out of range for {suffix}"),
                    start: span.start,
                    end: span.end,
                    filename: filename.to_string(),
                    line: span.line,
                    col: span.col,
                    source_line: None,
                });
            }
            Literal::SizedInt { value, kind }
        }
        Rule::float_lit_suffixed => {
            // Float literals: digits and '.' at the start, suffix follows.
            let (suffix, digits_end) = if let Some(pos) =
                text.find(|c: char| !c.is_ascii_digit() && c != '_' && c != '.')
            {
                (&text[pos..], pos)
            } else {
                (text, 0)
            };
            let digits = &text[..digits_end];
            let kind = match suffix {
                "f32" => FloatKind::F32,
                "f64" => FloatKind::F64,
                _ => {
                    return Err(MetelError::internal(format!(
                        "unknown float suffix '{suffix}'"
                    )))
                }
            };
            let value: f64 = digits.parse().map_err(|_| MetelError::ParseError {
                code: ParseErrorCode::P0003,
                message: format!("invalid float literal '{text}'"),
                start: span.start,
                end: span.end,
                filename: filename.to_string(),
                line: span.line,
                col: span.col,
                source_line: None,
            })?;
            Literal::SizedFloat { value, kind }
        }
        Rule::string_lit => return parse_string_literal_expr(text, span, filename),
        Rule::char_lit => {
            let inner = &text[1..text.len() - 1];
            let ch = parse_char_inner(inner).ok_or_else(|| MetelError::ParseError {
                code: ParseErrorCode::P0004,
                message: format!("invalid character literal {text}"),
                start: span.start,
                end: span.end,
                filename: filename.to_string(),
                line: span.line,
                col: span.col,
                source_line: None,
            })?;
            Literal::Char(ch)
        }
        Rule::bool_lit => Literal::Boolean(text == "true"),
        Rule::unit_lit => Literal::Unit,
        r => {
            return Err(MetelError::internal(format!(
                "parse_literal_expr: unexpected rule {r:?}"
            )))
        }
    };
    Ok(Expr::Literal(lit, span))
}

// Interpolated strings are lowered to plain string-concatenation here in the parser.
// No `Expr::Interpolation` AST node is emitted; downstream passes see only `BinOp(Plus, …)`
// and `.to_string()` calls. See ADR-0033.
fn parse_string_literal_expr(text: &str, span: Span, filename: &str) -> Result<Expr, MetelError> {
    let raw = &text[1..text.len() - 1];
    if !raw.contains("${") && !raw.contains("\\$") {
        return Ok(Expr::Literal(Literal::Str(unescape(raw)), span));
    }

    let mut parts: Vec<Expr> = vec![];
    let mut text_buf = String::new();
    let mut text_start: Option<usize> = None;
    let mut i = 0usize;
    while i < raw.len() {
        let c = raw[i..]
            .chars()
            .next()
            .ok_or_else(|| MetelError::internal("string interpolation: invalid char boundary"))?;
        let next = i + c.len_utf8();
        if c == '\\' {
            let escaped = raw[next..].chars().next();
            let decoded = match escaped {
                Some('n') => '\n',
                Some('t') => '\t',
                Some('r') => '\r',
                Some('\\') => '\\',
                Some('"') => '"',
                Some('$') => '$',
                Some(other) => {
                    text_buf.push('\\');
                    text_buf.push(other);
                    if text_start.is_none() {
                        text_start = Some(i);
                    }
                    i = next + other.len_utf8();
                    continue;
                }
                None => {
                    text_buf.push('\\');
                    if text_start.is_none() {
                        text_start = Some(i);
                    }
                    i = next;
                    continue;
                }
            };
            if text_start.is_none() {
                text_start = Some(i);
            }
            text_buf.push(decoded);
            i = next + escaped.map_or(0, char::len_utf8);
            continue;
        }

        if c == '$' && raw[next..].starts_with('{') {
            if !text_buf.is_empty() {
                let seg_start = text_start.unwrap_or(i);
                let seg_span = make_relative_span(&span, raw, seg_start, i);
                parts.push(Expr::Literal(
                    Literal::Str(std::mem::take(&mut text_buf)),
                    seg_span,
                ));
                text_start = None;
            }

            let interp_start = i;
            let expr_start = next + 1;
            let expr_end = find_interpolation_end(raw, expr_start, &span)?;
            let expr_span = make_relative_span(&span, raw, expr_start, expr_end);
            let placeholder_span = make_relative_span(&span, raw, interp_start, expr_end + 1);
            let mut expr =
                parse_interpolation_expr(&raw[expr_start..expr_end], &expr_span, filename)?;
            shift_expr_span(&mut expr, expr_span.start, expr_span.line, expr_span.col);
            parts.push(Expr::MethodCall {
                receiver: Box::new(expr),
                method: "to_string".to_string(),
                type_args: vec![],
                args: vec![],
                span: placeholder_span,
            });
            i = expr_end + 1;
            continue;
        }

        if text_start.is_none() {
            text_start = Some(i);
        }
        text_buf.push(c);
        i = next;
    }

    if !text_buf.is_empty() {
        let seg_start = text_start.unwrap_or(raw.len());
        let seg_span = make_relative_span(&span, raw, seg_start, raw.len());
        parts.push(Expr::Literal(Literal::Str(text_buf), seg_span));
    }

    if parts.is_empty() {
        return Ok(Expr::Literal(Literal::Str(String::new()), span));
    }
    Ok(fold_balanced_concat(parts, &span))
}

// Combine the interpolation parts into a **balanced** tree of `+` rather than a
// left-nested chain. `+` on strings is associative, so the produced string is
// unchanged, but downstream passes that recurse over the concat spine (type
// inference — `infer_binop` even calls `solve()` per node — evaluation, move
// checking) now see depth O(log n) instead of O(n). A left-nested chain of ~15
// `+` nodes (8 `${}` segments) was enough to overflow the ~2 MiB test-thread
// stack in a debug build. See metel-core#906.
fn fold_balanced_concat(mut level: Vec<Expr>, span: &Span) -> Expr {
    debug_assert!(!level.is_empty());
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        let mut iter = level.into_iter();
        while let Some(lhs) = iter.next() {
            match iter.next() {
                Some(rhs) => next.push(Expr::BinOp(
                    Box::new(lhs),
                    BinOp::Add,
                    Box::new(rhs),
                    span.clone(),
                )),
                None => next.push(lhs),
            }
        }
        level = next;
    }
    level
        .into_iter()
        .next()
        .expect("fold_balanced_concat: non-empty by precondition")
}

fn parse_interpolation_expr(source: &str, span: &Span, filename: &str) -> Result<Expr, MetelError> {
    let source = unescape(source);
    let mut pairs = MetelParser::parse(Rule::interp_expr_entry, &source).map_err(|e| {
        let (start, end) = match e.location {
            pest::error::InputLocation::Pos(p) => (p, p),
            pest::error::InputLocation::Span((s, e)) => (s, e),
        };
        let (line, col) = match &e.line_col {
            pest::error::LineColLocation::Pos((l, c))
            | pest::error::LineColLocation::Span((l, c), _) => (*l as u32, *c as u32),
        };
        let (line, col) = shift_line_col(line, col, span.line, span.col);
        MetelError::ParseError {
            code: ParseErrorCode::P0001,
            message: e.variant.to_string(),
            start: span.start + start,
            end: span.start + end,
            filename: filename.to_string(),
            line,
            col,
            source_line: Some(e.line().to_string()),
        }
    })?;
    let entry_pair = pairs
        .next()
        .ok_or_else(|| MetelError::internal("string interpolation: missing expr pair"))?;
    let pair = entry_pair
        .into_inner()
        .next()
        .ok_or_else(|| MetelError::internal("string interpolation: missing expr pair"))?;
    parse_expr(pair, filename)
}

fn find_interpolation_end(
    raw: &str,
    expr_start: usize,
    literal_span: &Span,
) -> Result<usize, MetelError> {
    let mut depth = 1usize;
    let mut in_string = false;
    let mut escaped = false;
    let mut i = expr_start;
    while i < raw.len() {
        let (c, consumed) = decoded_interpolation_char(raw, i)?;
        if in_string {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_string = false;
            }
        } else {
            match c {
                '"' => in_string = true,
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        return Ok(i);
                    }
                }
                _ => {}
            }
        }
        i += consumed;
    }

    Err(MetelError::parse(
        ParseErrorCode::P0001,
        "unterminated string interpolation",
        literal_span,
    ))
}

fn decoded_interpolation_char(raw: &str, start: usize) -> Result<(char, usize), MetelError> {
    let c = raw[start..]
        .chars()
        .next()
        .ok_or_else(|| MetelError::internal("string interpolation: invalid char boundary"))?;
    if c != '\\' {
        return Ok((c, c.len_utf8()));
    }

    let next_start = start + c.len_utf8();
    let escaped = raw[next_start..]
        .chars()
        .next()
        .ok_or_else(|| MetelError::internal("string interpolation: trailing backslash"))?;
    let decoded = match escaped {
        'n' => '\n',
        't' => '\t',
        'r' => '\r',
        '\\' => '\\',
        '"' => '"',
        '$' => '$',
        other => other,
    };
    Ok((decoded, c.len_utf8() + escaped.len_utf8()))
}

fn make_relative_span(literal_span: &Span, raw: &str, start: usize, end: usize) -> Span {
    let (line, col) = advance_line_col(literal_span.line, literal_span.col + 1, &raw[..start]);
    Span {
        start: literal_span.start + 1 + start,
        end: literal_span.start + 1 + end,
        filename: literal_span.filename.clone(),
        line,
        col,
    }
}

fn advance_line_col(mut line: u32, mut col: u32, text: &str) -> (u32, u32) {
    for ch in text.chars() {
        if ch == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

fn shift_line_col(local_line: u32, local_col: u32, base_line: u32, base_col: u32) -> (u32, u32) {
    if local_line <= 1 {
        (base_line, base_col + local_col.saturating_sub(1))
    } else {
        (base_line + local_line - 1, local_col)
    }
}

fn shift_span(span: &mut Span, base_start: usize, base_line: u32, base_col: u32) {
    span.start += base_start;
    span.end += base_start;
    let (line, col) = shift_line_col(span.line, span.col, base_line, base_col);
    span.line = line;
    span.col = col;
}

// Exhaustive match over every Expr variant; splitting it up would scatter one
// coherent dispatch table across many small functions with no real gain in
// clarity.
#[allow(clippy::too_many_lines)]
fn shift_expr_span(expr: &mut Expr, base_start: usize, base_line: u32, base_col: u32) {
    match expr {
        Expr::Path(_, seg_spans, span) => {
            for s in seg_spans.iter_mut() {
                shift_span(s, base_start, base_line, base_col);
            }
            shift_span(span, base_start, base_line, base_col);
        }
        Expr::Literal(_, span)
        | Expr::Ident(_, span)
        | Expr::Tuple(_, span)
        | Expr::Array(_, span)
        | Expr::RepeatArray(_, _, span)
        | Expr::BinOp(_, _, _, span)
        | Expr::UnaryOp(_, _, span)
        | Expr::PropagateError { span, .. }
        | Expr::RecordProjection { span, .. }
        | Expr::ResolvedPath { span, .. } => {
            shift_span(span, base_start, base_line, base_col);
        }
        Expr::Assign {
            target,
            value,
            span,
            ..
        } => {
            shift_assign_target_span(target, base_start, base_line, base_col);
            shift_expr_span(value, base_start, base_line, base_col);
            shift_span(span, base_start, base_line, base_col);
        }
        Expr::Call {
            callee, args, span, ..
        } => {
            shift_expr_span(callee, base_start, base_line, base_col);
            for arg in args {
                shift_expr_span(arg, base_start, base_line, base_col);
            }
            shift_span(span, base_start, base_line, base_col);
        }
        Expr::MethodCall {
            receiver,
            args,
            span,
            ..
        } => {
            shift_expr_span(receiver, base_start, base_line, base_col);
            for arg in args {
                shift_expr_span(arg, base_start, base_line, base_col);
            }
            shift_span(span, base_start, base_line, base_col);
        }
        Expr::FieldAccess { object, span, .. } | Expr::TupleAccess { object, span, .. } => {
            shift_expr_span(object, base_start, base_line, base_col);
            shift_span(span, base_start, base_line, base_col);
        }
        Expr::Index {
            object,
            index,
            span,
        } => {
            shift_expr_span(object, base_start, base_line, base_col);
            shift_expr_span(index, base_start, base_line, base_col);
            shift_span(span, base_start, base_line, base_col);
        }
        Expr::Cast { expr, span, .. } | Expr::Ascribe { expr, span, .. } => {
            shift_expr_span(expr, base_start, base_line, base_col);
            shift_span(span, base_start, base_line, base_col);
        }
        Expr::Match(m) => {
            shift_expr_span(&mut m.scrutinee, base_start, base_line, base_col);
            for arm in &mut m.arms {
                shift_match_arm_span(arm, base_start, base_line, base_col);
            }
            shift_span(&mut m.span, base_start, base_line, base_col);
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            span,
        } => {
            shift_expr_span(condition, base_start, base_line, base_col);
            shift_block_span(then_branch, base_start, base_line, base_col);
            if let Some(block) = else_branch {
                shift_block_span(block, base_start, base_line, base_col);
            }
            shift_span(span, base_start, base_line, base_col);
        }
        Expr::Loop { body, span } => {
            shift_block_span(body, base_start, base_line, base_col);
            shift_span(span, base_start, base_line, base_col);
        }
        Expr::Closure {
            params, body, span, ..
        } => {
            for param in params {
                shift_span(&mut param.span, base_start, base_line, base_col);
            }
            shift_block_span(body, base_start, base_line, base_col);
            shift_span(span, base_start, base_line, base_col);
        }
        Expr::StructLiteral { fields, span, .. } | Expr::RecordLiteral { fields, span } => {
            for (_, expr) in fields {
                shift_expr_span(expr, base_start, base_line, base_col);
            }
            shift_span(span, base_start, base_line, base_col);
        }
        Expr::Return(ret) => {
            if let Some(expr) = &mut ret.value {
                shift_expr_span(expr, base_start, base_line, base_col);
            }
            shift_span(&mut ret.span, base_start, base_line, base_col);
        }
        Expr::Break(brk) => {
            if let Some(expr) = &mut brk.value {
                shift_expr_span(expr, base_start, base_line, base_col);
            }
            shift_span(&mut brk.span, base_start, base_line, base_col);
        }
        Expr::Continue(span) => shift_span(span, base_start, base_line, base_col),
    }
}

fn shift_assign_target_span(
    target: &mut AssignTarget,
    base_start: usize,
    base_line: u32,
    base_col: u32,
) {
    match target {
        AssignTarget::Ident(_, span) => shift_span(span, base_start, base_line, base_col),
        AssignTarget::FieldAccess { object, span, .. }
        | AssignTarget::TupleAccess { object, span, .. }
        | AssignTarget::Deref { object, span } => {
            shift_expr_span(object, base_start, base_line, base_col);
            shift_span(span, base_start, base_line, base_col);
        }
        AssignTarget::Index {
            object,
            index,
            span,
        } => {
            shift_expr_span(object, base_start, base_line, base_col);
            shift_expr_span(index, base_start, base_line, base_col);
            shift_span(span, base_start, base_line, base_col);
        }
    }
}

fn shift_block_span(block: &mut Block, base_start: usize, base_line: u32, base_col: u32) {
    for stmt in &mut block.stmts {
        shift_decl_span(stmt, base_start, base_line, base_col);
    }
    if let Some(tail) = &mut block.tail {
        shift_expr_span(tail, base_start, base_line, base_col);
    }
    shift_span(&mut block.span, base_start, base_line, base_col);
}

fn shift_decl_span(decl: &mut Decl, base_start: usize, base_line: u32, base_col: u32) {
    match decl {
        Decl::Let(ld) => {
            shift_expr_span(&mut ld.value, base_start, base_line, base_col);
            shift_span(&mut ld.span, base_start, base_line, base_col);
        }
        Decl::Mut(md) => {
            shift_expr_span(&mut md.value, base_start, base_line, base_col);
            shift_span(&mut md.span, base_start, base_line, base_col);
        }
        Decl::Fun(fd) => {
            for param in &mut fd.params {
                shift_span(&mut param.span, base_start, base_line, base_col);
            }
            shift_block_span(&mut fd.body, base_start, base_line, base_col);
            shift_span(&mut fd.span, base_start, base_line, base_col);
        }
        Decl::Struct(sd) => {
            for field in &mut sd.fields {
                shift_span(&mut field.span, base_start, base_line, base_col);
            }
            shift_span(&mut sd.span, base_start, base_line, base_col);
        }
        Decl::Enum(ed) => {
            for variant in &mut ed.variants {
                for field in &mut variant.fields {
                    shift_span(&mut field.span, base_start, base_line, base_col);
                }
                shift_span(&mut variant.span, base_start, base_line, base_col);
            }
            shift_span(&mut ed.span, base_start, base_line, base_col);
        }
        Decl::Impl(ib) => {
            for method in &mut ib.methods {
                for param in &mut method.params {
                    shift_span(&mut param.span, base_start, base_line, base_col);
                }
                shift_block_span(&mut method.body, base_start, base_line, base_col);
                shift_span(&mut method.span, base_start, base_line, base_col);
            }
            shift_span(&mut ib.span, base_start, base_line, base_col);
        }
        Decl::Aspect(ad) => {
            for method in &mut ad.methods {
                for param in &mut method.params {
                    shift_span(&mut param.span, base_start, base_line, base_col);
                }
                if let Some(body) = &mut method.default_body {
                    shift_block_span(body, base_start, base_line, base_col);
                }
                shift_span(&mut method.span, base_start, base_line, base_col);
            }
            shift_span(&mut ad.span, base_start, base_line, base_col);
        }
        Decl::Stmt(stmt) => shift_stmt_span(stmt, base_start, base_line, base_col),
        Decl::TypeAlias(ta) => shift_span(&mut ta.span, base_start, base_line, base_col),
    }
}

fn shift_stmt_span(stmt: &mut Stmt, base_start: usize, base_line: u32, base_col: u32) {
    match stmt {
        Stmt::While(ws) => {
            shift_expr_span(&mut ws.condition, base_start, base_line, base_col);
            shift_block_span(&mut ws.body, base_start, base_line, base_col);
            shift_span(&mut ws.span, base_start, base_line, base_col);
        }
        Stmt::For(fs) => {
            if let Some(init) = &mut fs.init {
                match init {
                    ForInit::Let(ld) => {
                        shift_expr_span(&mut ld.value, base_start, base_line, base_col);
                        shift_span(&mut ld.span, base_start, base_line, base_col);
                    }
                    ForInit::Mut(md) => {
                        shift_expr_span(&mut md.value, base_start, base_line, base_col);
                        shift_span(&mut md.span, base_start, base_line, base_col);
                    }
                    ForInit::Expr(expr) => shift_expr_span(expr, base_start, base_line, base_col),
                }
            }
            if let Some(condition) = &mut fs.condition {
                shift_expr_span(condition, base_start, base_line, base_col);
            }
            if let Some(step) = &mut fs.step {
                shift_expr_span(step, base_start, base_line, base_col);
            }
            shift_block_span(&mut fs.body, base_start, base_line, base_col);
            shift_span(&mut fs.span, base_start, base_line, base_col);
        }
        Stmt::ForIn(fi) => {
            shift_expr_span(&mut fi.iterable, base_start, base_line, base_col);
            shift_block_span(&mut fi.body, base_start, base_line, base_col);
            shift_span(&mut fi.span, base_start, base_line, base_col);
        }
        Stmt::Expr(expr) => shift_expr_span(expr, base_start, base_line, base_col),
    }
}

fn shift_match_arm_span(arm: &mut MatchArm, base_start: usize, base_line: u32, base_col: u32) {
    shift_pattern_span(&mut arm.pattern, base_start, base_line, base_col);
    if let Some(guard) = &mut arm.guard {
        shift_expr_span(guard, base_start, base_line, base_col);
    }
    shift_block_span(&mut arm.body, base_start, base_line, base_col);
    shift_span(&mut arm.span, base_start, base_line, base_col);
}

fn shift_pattern_span(pattern: &mut Pattern, base_start: usize, base_line: u32, base_col: u32) {
    match pattern {
        Pattern::Wildcard(span)
        | Pattern::Binding(_, span)
        | Pattern::Literal(_, span)
        | Pattern::EnumVariant { span, .. }
        | Pattern::Struct { span, .. }
        | Pattern::Record { span, .. } => shift_span(span, base_start, base_line, base_col),
        Pattern::Tuple(items, span) => {
            for item in items {
                shift_pattern_span(item, base_start, base_line, base_col);
            }
            shift_span(span, base_start, base_line, base_col);
        }
        Pattern::Array { elems, span, .. } => {
            for item in elems {
                shift_pattern_span(item, base_start, base_line, base_col);
            }
            shift_span(span, base_start, base_line, base_col);
        }
    }
}

fn parse_path_expr(pair: pest::iterators::Pair<Rule>, filename: &str) -> Result<Expr, MetelError> {
    let span = Span::of(&pair, filename);
    // One span per segment, aligned with `parts` — the module-segment
    // go-to-definition click targets (metel-core#1070).
    let seg_spans: Vec<Span> = pair
        .clone()
        .into_inner()
        .filter(|p| matches!(p.as_rule(), Rule::path_root | Rule::ident))
        .map(|p| Span::of(&p, filename))
        .collect();
    let parts = collect_path_components(pair)?;
    if parts.len() == 1 {
        Ok(Expr::Ident(parts.into_iter().next().unwrap(), span))
    } else {
        Ok(Expr::Path(parts, seg_spans, span))
    }
}

fn parse_tuple_or_paren(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Expr, MetelError> {
    let span = Span::of(&pair, filename);
    let elems: Vec<Expr> = pair
        .into_inner()
        .filter(|p| p.as_rule() == Rule::expr)
        .map(|p| parse_expr(p, filename))
        .collect::<Result<_, _>>()?;
    if elems.len() == 1 {
        Ok(elems.into_iter().next().unwrap())
    } else {
        Ok(Expr::Tuple(elems, span))
    }
}

fn parse_array_lit(pair: pest::iterators::Pair<Rule>, filename: &str) -> Result<Expr, MetelError> {
    let span = Span::of(&pair, filename);
    let elems = pair
        .into_inner()
        .filter(|p| p.as_rule() == Rule::expr)
        .map(|p| parse_expr(p, filename))
        .collect::<Result<_, _>>()?;
    Ok(Expr::Array(elems, span))
}

fn parse_repeat_array(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Expr, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let elem = parse_expr(
        inner
            .next()
            .ok_or_else(|| MetelError::internal("repeat_array: expected element expr"))?,
        filename,
    )?;
    let n_str = inner
        .next()
        .ok_or_else(|| MetelError::internal("repeat_array: expected count"))?
        .as_str();
    let n: u64 = n_str.parse().map_err(|_| {
        MetelError::internal(format!("repeat_array: count '{n_str}' is not a valid u64"))
    })?;
    Ok(Expr::RepeatArray(Box::new(elem), n, span))
}

fn wrap_expr_as_block(expr: Expr) -> Block {
    let s = expr.span().clone();
    Block {
        stmts: vec![],
        tail: Some(Box::new(expr)),
        span: s,
    }
}

fn parse_if_expr(pair: pest::iterators::Pair<Rule>, filename: &str) -> Result<Expr, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();

    let condition = parse_expr(
        inner
            .next()
            .ok_or_else(|| MetelError::internal("if_expr: expected condition"))?,
        filename,
    )?;

    let then_pair = inner
        .next()
        .ok_or_else(|| MetelError::internal("if_expr: expected then body"))?;
    let then_is_block = then_pair.as_rule() == Rule::block;
    let then_branch = if then_is_block {
        parse_block(then_pair, filename)?
    } else {
        let expr = parse_expr(then_pair, filename)?;
        // Braceless body that is itself an if–else creates dangling-else ambiguity.
        if let Expr::If {
            else_branch: Some(_),
            ..
        } = &expr
        {
            return Err(MetelError::parse(
                ParseErrorCode::P0001,
                "braceless if body may not contain an if–else expression; wrap the outer body in braces",
                &span,
            ));
        }
        wrap_expr_as_block(expr)
    };

    let else_branch = match inner.next() {
        None => None,
        Some(p) => {
            let else_is_block = p.as_rule() == Rule::block;
            let else_is_if = p.as_rule() == Rule::if_expr;
            // Mixed arm styles are not allowed.
            if then_is_block && !else_is_block && !else_is_if {
                return Err(MetelError::parse(
                    ParseErrorCode::P0001,
                    "mismatched if arm styles: then branch uses braces but else branch does not",
                    &span,
                ));
            }
            if !then_is_block && else_is_block {
                return Err(MetelError::parse(
                    ParseErrorCode::P0001,
                    "mismatched if arm styles: then branch is braceless but else branch uses braces",
                    &span,
                ));
            }
            Some(match p.as_rule() {
                Rule::block => parse_block(p, filename)?,
                // `else if` — wrap the nested if_expr in a synthetic block so that
                // Expr::If.else_branch is always Option<Block>.
                Rule::if_expr => {
                    let nested = parse_if_expr(p, filename)?;
                    wrap_expr_as_block(nested)
                }
                _ => wrap_expr_as_block(parse_expr(p, filename)?),
            })
        }
    };

    Ok(Expr::If {
        condition: Box::new(condition),
        then_branch,
        else_branch,
        span,
    })
}

fn parse_loop_expr(pair: pest::iterators::Pair<Rule>, filename: &str) -> Result<Expr, MetelError> {
    let span = Span::of(&pair, filename);
    let body = parse_block(
        pair.into_inner()
            .next()
            .ok_or_else(|| MetelError::internal("loop_expr: expected body"))?,
        filename,
    )?;
    Ok(Expr::Loop { body, span })
}

fn parse_closure_expr(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Expr, MetelError> {
    let span = Span::of(&pair, filename);
    let mut captures = vec![];
    let mut call_multiplicity = CallMultiplicity::Many;
    let mut call_mutation = CallMutation::Reading;
    let mut params = vec![];
    let mut return_type = None;
    let mut body = None;
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::capture_list => captures = parse_capture_list(p, filename)?,
            Rule::once_kw => call_multiplicity = CallMultiplicity::Once,
            Rule::mut_kw => call_mutation = CallMutation::Mutating,
            Rule::param_list => params = parse_param_list(p, filename)?,
            Rule::type_expr => return_type = Some(parse_type_expr(p, filename)?),
            Rule::block => body = Some(parse_block(p, filename)?),
            _ => {}
        }
    }
    Ok(Expr::Closure {
        captures,
        call_multiplicity,
        call_mutation,
        params,
        return_type,
        body: body.ok_or_else(|| MetelError::internal("closure: missing body block"))?,
        span,
    })
}

fn parse_capture_list(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Vec<CaptureSpec>, MetelError> {
    pair.into_inner()
        .filter(|p| p.as_rule() == Rule::capture_item)
        .map(|item| {
            let span = Span::of(&item, filename);
            let spelling = item.as_str().trim();
            let name = item
                .clone()
                .into_inner()
                .find(|p| p.as_rule() == Rule::ident)
                .ok_or_else(|| MetelError::internal("capture_item: expected identifier"))?
                .as_str()
                .to_string();
            Ok(if spelling.starts_with("&var") {
                CaptureSpec::MutRef { name, span }
            } else if spelling.starts_with('&') {
                CaptureSpec::SharedRef { name, span }
            } else if spelling.ends_with(".clone()") {
                CaptureSpec::Clone { name, span }
            } else {
                CaptureSpec::Owned { name, span }
            })
        })
        .collect()
}

fn parse_struct_literal(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Expr, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let path_pair = inner
        .next()
        .ok_or_else(|| MetelError::internal("struct_literal: expected path"))?;
    let path = collect_path_components(path_pair)?;
    let mut fields = vec![];
    for p in inner {
        if p.as_rule() == Rule::field_init {
            let field_span = Span::of(&p, filename);
            let mut it = p.into_inner();
            let name_pair = it
                .next()
                .ok_or_else(|| MetelError::internal("struct_literal: expected field name"))?;
            let name = name_pair.as_str().to_string();
            let value = match it.next() {
                Some(expr_pair) => parse_expr(expr_pair, filename)?,
                None => Expr::Ident(name.clone(), field_span),
            };
            fields.push((name, value));
        }
    }
    Ok(Expr::StructLiteral {
        path,
        fields,
        symbol_id: None,
        span,
    })
}

fn parse_record_literal(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Expr, MetelError> {
    let span = Span::of(&pair, filename);
    let mut fields = vec![];
    for p in pair.into_inner() {
        if p.as_rule() == Rule::field_init {
            let field_span = Span::of(&p, filename);
            let mut it = p.into_inner();
            let name_pair = it
                .next()
                .ok_or_else(|| MetelError::internal("record_lit: expected field name"))?;
            let name = name_pair.as_str().to_string();
            let value = match it.next() {
                Some(expr_pair) => parse_expr(expr_pair, filename)?,
                None => Expr::Ident(name.clone(), field_span),
            };
            fields.push((name, value));
        }
    }
    sort_record_fields(&mut fields, filename, &span)?;
    Ok(Expr::RecordLiteral { fields, span })
}

fn parse_record_projection_expr(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Expr, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let path_pair = inner
        .next()
        .ok_or_else(|| MetelError::internal("record_projection_expr: expected path"))?;
    let path = collect_path_components(path_pair)?;
    let mut fields: Vec<String> = inner.map(|p| p.as_str().to_string()).collect();
    sort_record_labels(&mut fields, filename, &span, "record projection")?;
    Ok(Expr::RecordProjection { path, fields, span })
}

fn collect_path_components(pair: pest::iterators::Pair<Rule>) -> Result<Vec<String>, MetelError> {
    let mut parts = Vec::new();
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::path_root => {
                parts.push(path_root_to_component(parse_path_root(p)?));
            }
            Rule::ident => parts.push(p.as_str().to_string()),
            r => return Err(MetelError::internal(format!("path: unexpected rule {r:?}"))),
        }
    }
    Ok(parts)
}

fn path_root_to_component(root: PathRoot) -> String {
    match root {
        PathRoot::Root => "root".to_string(),
        PathRoot::Std => "std".to_string(),
        PathRoot::Self_ => "self".to_string(),
        PathRoot::Super => "super".to_string(),
        PathRoot::Name(name) => name,
    }
}

// ── Assignment ────────────────────────────────────────────────────────────────

fn parse_assign_expr(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Expr, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let first = inner
        .next()
        .ok_or_else(|| MetelError::internal("assign_expr: expected first child"))?;

    // assign_expr = { unary_expr ~ assign_op ~ assign_expr | or_expr }
    // If first child is unary_expr and next is assign_op, it's an assignment.
    // Otherwise it's an or_expr chain.
    match first.as_rule() {
        Rule::unary_expr => {
            let lhs = parse_unary_expr(first, filename)?;
            match inner.next() {
                Some(op_pair) if op_pair.as_rule() == Rule::assign_op => {
                    let op = parse_assign_op(op_pair.as_str());
                    let rhs = parse_expr(
                        inner
                            .next()
                            .ok_or_else(|| MetelError::internal("assign_expr: expected rhs"))?,
                        filename,
                    )?;
                    let target = expr_to_assign_target(lhs)?;
                    Ok(Expr::Assign {
                        target,
                        op,
                        value: Box::new(rhs),
                        span,
                    })
                }
                _ => Ok(lhs), // shouldn't happen with valid grammar
            }
        }
        Rule::or_expr => parse_lr_binary(first, filename),
        _ => parse_expr(first, filename),
    }
}

// ── Binary expressions (left-recursive) ──────────────────────────────────────

/// Handles `or_expr`, `and_expr`, `cmp_expr`, `range_expr`, `add_expr`, `mul_expr`.
/// All follow the pattern: operand (op operand)* where op is a named rule.
fn parse_lr_binary(pair: pest::iterators::Pair<Rule>, filename: &str) -> Result<Expr, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let first = inner
        .next()
        .ok_or_else(|| MetelError::internal("binary_expr: expected first operand"))?;
    let mut expr = parse_expr(first, filename)?;

    // Consume op/operand pairs
    while let Some(op_pair) = inner.next() {
        let op = parse_bin_op(&op_pair);
        let rhs_pair = inner
            .next()
            .ok_or_else(|| MetelError::internal("binary_expr: expected rhs operand"))?;
        let rhs = parse_expr(rhs_pair, filename)?;
        let op_span = Span::of(&op_pair, filename);
        expr = Expr::BinOp(Box::new(expr), op, Box::new(rhs), op_span);
    }
    let _ = span; // span used in outer call if needed
    Ok(expr)
}

// ── Ascription and Cast ───────────────────────────────────────────────────────

fn parse_asc_expr(pair: pest::iterators::Pair<Rule>, filename: &str) -> Result<Expr, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let first = inner
        .next()
        .ok_or_else(|| MetelError::internal("asc_expr: expected operand"))?;
    let expr = parse_expr(first, filename)?;
    match inner.next() {
        Some(ty_pair) => {
            let ann = parse_type_expr(ty_pair, filename)?;
            Ok(Expr::Ascribe {
                expr: Box::new(expr),
                ann,
                span,
            })
        }
        None => Ok(expr),
    }
}

fn parse_cast_expr(pair: pest::iterators::Pair<Rule>, filename: &str) -> Result<Expr, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let first = inner
        .next()
        .ok_or_else(|| MetelError::internal("cast_expr: expected operand"))?;
    let mut expr = parse_expr(first, filename)?;
    for p in inner {
        if p.as_rule() == Rule::type_expr {
            let target_type = parse_type_expr(p, filename)?;
            expr = Expr::Cast {
                expr: Box::new(expr),
                target_type,
                span: span.clone(),
            };
        }
    }
    Ok(expr)
}

// ── Unary ─────────────────────────────────────────────────────────────────────

fn parse_unary_expr(pair: pest::iterators::Pair<Rule>, filename: &str) -> Result<Expr, MetelError> {
    let span = Span::of(&pair, filename);
    let text = pair.as_str();
    let child = pair
        .into_inner()
        .next_back()
        .ok_or_else(|| MetelError::internal("unary_expr: expected operand"))?;
    if text.starts_with('!') {
        Ok(Expr::UnaryOp(
            UnaryOp::Not,
            Box::new(parse_expr(child, filename)?),
            span,
        ))
    } else if text.starts_with("&var") {
        Ok(Expr::UnaryOp(
            UnaryOp::RefMut,
            Box::new(parse_expr(child, filename)?),
            span,
        ))
    } else if text.starts_with('&') {
        Ok(Expr::UnaryOp(
            UnaryOp::Ref,
            Box::new(parse_expr(child, filename)?),
            span,
        ))
    } else if text.starts_with('-') {
        Ok(Expr::UnaryOp(
            UnaryOp::Neg,
            Box::new(parse_expr(child, filename)?),
            span,
        ))
    } else if text.starts_with('*') {
        // RFC-0110: explicit dereference.
        Ok(Expr::UnaryOp(
            UnaryOp::Deref,
            Box::new(parse_expr(child, filename)?),
            span,
        ))
    } else {
        parse_expr(child, filename)
    }
}

// ── Postfix ───────────────────────────────────────────────────────────────────

fn parse_postfix_expr(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Expr, MetelError> {
    let mut inner = pair.into_inner();
    let primary = inner
        .next()
        .ok_or_else(|| MetelError::internal("postfix_expr: expected primary"))?;
    let mut expr = parse_expr(primary, filename)?;
    for postfix in inner {
        if postfix.as_rule() == Rule::postfix {
            expr = apply_postfix(expr, postfix, filename)?;
        }
    }
    Ok(expr)
}

fn parse_type_args_pair(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Vec<TypeExpr>, MetelError> {
    pair.into_inner()
        .filter(|p| p.as_rule() == Rule::type_expr)
        .map(|p| parse_type_expr(p, filename))
        .collect()
}

// Exhaustive match over every AST/type-system variant; splitting it up would
// scatter one coherent dispatch table across many small functions with no
// real gain in clarity.
#[allow(clippy::too_many_lines)]
fn apply_postfix(
    base: Expr,
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Expr, MetelError> {
    let span = Span::of(&pair, filename);
    let text = pair.as_str();
    let mut inner = pair.into_inner();

    if text.starts_with("::<") {
        // Turbofish free function call: children are type_args, then optional arg_list
        let targs_pair = inner
            .next()
            .ok_or_else(|| MetelError::internal("turbofish call: expected type_args"))?;
        let type_args = parse_type_args_pair(targs_pair, filename)?;
        let args = match inner.next() {
            Some(a) if a.as_rule() == Rule::arg_list => collect_args(a.into_inner(), filename)?,
            _ => vec![],
        };
        Ok(Expr::Call {
            callee: Box::new(base),
            type_args,
            args,
            span,
        })
    } else if text.starts_with('(') {
        // Function call: postfix children are (arg_list?), so unwrap one level
        let args = match inner.next() {
            Some(a) if a.as_rule() == Rule::arg_list => collect_args(a.into_inner(), filename)?,
            _ => vec![],
        };
        Ok(Expr::Call {
            callee: Box::new(base),
            type_args: vec![],
            args,
            span,
        })
    } else if text.starts_with('[') {
        // Index
        let idx = parse_expr(
            inner
                .next()
                .ok_or_else(|| MetelError::internal("postfix index: expected index expr"))?,
            filename,
        )?;
        Ok(Expr::Index {
            object: Box::new(base),
            index: Box::new(idx),
            span,
        })
    } else if text == "?" {
        Ok(Expr::PropagateError {
            expr: Box::new(base),
            span,
        })
    } else {
        // Dot postfix — first named child is decimal_int or ident
        let first = inner
            .next()
            .ok_or_else(|| MetelError::internal("postfix dot: expected field name or index"))?;
        match first.as_rule() {
            Rule::decimal_int => {
                let idx = first.as_str().parse::<usize>().map_err(|_| {
                    MetelError::internal(format!(
                        "postfix dot: '{}' is not a valid tuple index",
                        first.as_str()
                    ))
                })?;
                Ok(Expr::TupleAccess {
                    object: Box::new(base),
                    index: idx,
                    span,
                })
            }
            Rule::ident => {
                let name = first.as_str().to_string();
                if text.contains("::<") {
                    // Method call with turbofish: next child is type_args, then optional arg_list
                    let targs_pair = inner.next().ok_or_else(|| {
                        MetelError::internal("method turbofish: expected type_args")
                    })?;
                    let type_args = parse_type_args_pair(targs_pair, filename)?;
                    let args = match inner.next() {
                        Some(a) if a.as_rule() == Rule::arg_list => {
                            collect_args(a.into_inner(), filename)?
                        }
                        _ => vec![],
                    };
                    Ok(Expr::MethodCall {
                        receiver: Box::new(base),
                        method: name,
                        type_args,
                        args,
                        span,
                    })
                } else if text.contains('(') {
                    // Method call without turbofish (arg_list may be absent if call has no args)
                    let args = match inner.next() {
                        Some(a) if a.as_rule() == Rule::arg_list => {
                            collect_args(a.into_inner(), filename)?
                        }
                        _ => vec![],
                    };
                    Ok(Expr::MethodCall {
                        receiver: Box::new(base),
                        method: name,
                        type_args: vec![],
                        args,
                        span,
                    })
                } else {
                    Ok(Expr::FieldAccess {
                        object: Box::new(base),
                        field: name,
                        span,
                    })
                }
            }
            r => Err(MetelError::internal(format!(
                "postfix dot: unexpected child rule {r:?}"
            ))),
        }
    }
}

fn collect_args(
    pairs: pest::iterators::Pairs<Rule>,
    filename: &str,
) -> Result<Vec<Expr>, MetelError> {
    pairs
        .filter(|p| p.as_rule() == Rule::expr)
        .map(|p| parse_expr(p, filename))
        .collect()
}

fn parse_match_expr(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<MatchExpr, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let scrutinee = parse_expr(
        inner
            .next()
            .ok_or_else(|| MetelError::internal("match_expr: expected scrutinee"))?,
        filename,
    )?;
    let arms: Vec<MatchArm> = inner
        .filter(|p| p.as_rule() == Rule::match_arm)
        .map(|p| parse_match_arm(p, filename))
        .collect::<Result<_, _>>()?;
    Ok(MatchExpr {
        scrutinee: Box::new(scrutinee),
        arms,
        span,
    })
}

fn parse_match_arm(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<MatchArm, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let pattern = parse_pattern(
        inner
            .next()
            .ok_or_else(|| MetelError::internal("match_arm: expected pattern"))?,
        filename,
    )?;

    // Remaining children: optionally a guard `expr`, then body `block | expr`.
    let remaining: Vec<_> = inner.collect();
    let (body_pair, guard_pairs) = remaining
        .split_last()
        .ok_or_else(|| MetelError::internal("match_arm: expected body"))?;

    let guard = guard_pairs
        .iter()
        .find(|p| p.as_rule() == Rule::expr)
        .map(|p| parse_expr(p.clone(), filename))
        .transpose()?;

    let body = match body_pair.as_rule() {
        Rule::block => parse_block(body_pair.clone(), filename)?,
        Rule::expr => {
            let body_span = Span::of(body_pair, filename);
            let expr = parse_expr(body_pair.clone(), filename)?;
            Block {
                stmts: vec![],
                tail: Some(Box::new(expr)),
                span: body_span,
            }
        }
        _ => return Err(MetelError::internal("match_arm: unexpected body rule")),
    };

    Ok(MatchArm {
        pattern,
        guard,
        body,
        span,
    })
}

/// `field_pat_list = { ident ~ ("," ~ ident)* ~ ("," ~ record_rest)? ~ ","? | record_rest }`
/// (RFC-0032 §4/§5) -- shared by `record_pattern` and `enum_pattern`'s fieldful forms.
/// Returns (named fields, whether a trailing `..` was present).
fn parse_field_pat_list(pair: pest::iterators::Pair<Rule>) -> (Vec<String>, bool) {
    let mut fields = vec![];
    let mut rest = false;
    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::ident => fields.push(child.as_str().to_string()),
            Rule::record_rest => rest = true,
            _ => {}
        }
    }
    (fields, rest)
}

#[allow(clippy::too_many_lines)]
fn parse_pattern(pair: pest::iterators::Pair<Rule>, filename: &str) -> Result<Pattern, MetelError> {
    match pair.as_rule() {
        Rule::pattern => {
            // The anonymous wildcard alternative (`"_" ~ !(...))`) produces a
            // Rule::pattern pair with no children, so check for it first.
            if pair.as_str().trim() == "_" {
                return Ok(Pattern::Wildcard(Span::of(&pair, filename)));
            }
            let inner = pair
                .into_inner()
                .next()
                .ok_or_else(|| MetelError::internal("pattern: missing inner rule"))?;
            parse_pattern(inner, filename)
        }
        Rule::tuple_pattern => {
            let span = Span::of(&pair, filename);
            let pats = pair
                .into_inner()
                .filter(|p| p.as_rule() == Rule::pattern)
                .map(|p| parse_pattern(p, filename))
                .collect::<Result<_, _>>()?;
            Ok(Pattern::Tuple(pats, span))
        }
        Rule::record_pattern => {
            let span = Span::of(&pair, filename);
            let field_list = pair
                .into_inner()
                .find(|p| p.as_rule() == Rule::field_pat_list)
                .ok_or_else(|| MetelError::internal("record_pattern: missing field_pat_list"))?;
            let (mut fields, rest) = parse_field_pat_list(field_list);
            sort_record_labels(&mut fields, filename, &span, "record pattern")?;
            Ok(Pattern::Record { fields, rest, span })
        }
        Rule::enum_pattern => {
            let span = Span::of(&pair, filename);
            // Two grammar alternatives share this rule: qualified `Enum::Variant`
            // (optionally `{ fields }`) and, per RFC-0107, bare fieldful `Variant
            // { fields }` -- the latter also covers a struct pattern (`Point { x, y }`),
            // ambiguous with a bare enum variant until the scrutinee's type is known
            // (`resolve_bare_variant` / `resolve_struct_pattern`). Every top-level
            // `Rule::ident` child here is a path segment (one for the bare form, two
            // for `Enum::Variant`) -- `field_pat_list`'s own idents are a separate
            // top-level child, not flattened into this iteration, harvested below via
            // its own `Rule::field_pat_list` arm.
            let mut path = vec![];
            let mut fields = vec![];
            let mut rest = false;
            for child in pair.into_inner() {
                match child.as_rule() {
                    Rule::ident => path.push(child.as_str().to_string()),
                    Rule::field_pat_list => {
                        let (f, r) = parse_field_pat_list(child);
                        fields = f;
                        rest = r;
                    }
                    _ => {}
                }
            }
            Ok(Pattern::EnumVariant {
                path,
                fields,
                rest,
                span,
            })
        }
        Rule::literal_pattern => {
            let span = Span::of(&pair, filename);
            let lit_pair = pair
                .into_inner()
                .next()
                .ok_or_else(|| MetelError::internal("literal_pattern: expected literal"))?;
            // Delegate to parse_literal_expr and extract the Literal.
            let Expr::Literal(lit, _) = parse_literal_expr(&lit_pair, filename)? else {
                return Err(MetelError::internal(
                    "literal_pattern: expected literal expr",
                ));
            };
            Ok(Pattern::Literal(lit, span))
        }
        Rule::bind_pattern => {
            let span = Span::of(&pair, filename);
            let name = pair
                .into_inner()
                .next()
                .ok_or_else(|| MetelError::internal("bind_pattern: expected name"))?
                .as_str()
                .to_string();
            Ok(Pattern::Binding(name, span))
        }
        Rule::array_pattern => {
            let span = Span::of(&pair, filename);
            // array_pattern = { "[" ~ array_pat_body ~ "]" }
            // array_pat_body = { (pattern ~ ("," ~ pattern)* ~ ("," ~ rest_pat)? | rest_pat)? }
            let body_pair = pair
                .into_inner()
                .find(|p| p.as_rule() == Rule::array_pat_body)
                .ok_or_else(|| MetelError::internal("array_pattern: missing body"))?;
            let mut elems = vec![];
            let mut rest = None;
            for child in body_pair.into_inner() {
                match child.as_rule() {
                    Rule::pattern => elems.push(parse_pattern(child, filename)?),
                    Rule::rest_pat => {
                        let name = child
                            .into_inner()
                            .find(|p| p.as_rule() == Rule::ident)
                            .ok_or_else(|| MetelError::internal("rest_pat: expected ident"))?
                            .as_str()
                            .to_string();
                        rest = Some(name);
                    }
                    _ => {}
                }
            }
            Ok(Pattern::Array { elems, rest, span })
        }
        // Wildcard: the `"_" ~ !(...)` alternative in `pattern` is anonymous;
        // pest emits no sub-rule, so `pair.as_rule() == Rule::pattern` and
        // `pair.as_str() == "_"` — handled by the outer `pattern` arm above
        // which recurses into the single child. If there is no child and the
        // text is "_", we match here.
        _ if pair.as_str().trim() == "_" => Ok(Pattern::Wildcard(Span::of(&pair, filename))),
        r => Err(MetelError::internal(format!(
            "pattern: unexpected rule {r:?}"
        ))),
    }
}

fn parse_bin_op(pair: &pest::iterators::Pair<Rule>) -> BinOp {
    match pair.as_rule() {
        Rule::add_op => {
            if pair.as_str() == "-" {
                BinOp::Sub
            } else {
                BinOp::Add
            }
        }
        Rule::mul_op => match pair.as_str() {
            "/" => BinOp::Div,
            "%" => BinOp::Rem,
            _ => BinOp::Mul,
        },
        Rule::or_op => BinOp::Or,
        Rule::and_op => BinOp::And,
        Rule::range_op => {
            if pair.as_str() == "..=" {
                BinOp::RangeInclusive
            } else {
                BinOp::Range
            }
        }
        Rule::cmp_op => match pair.as_str() {
            "==" => BinOp::Eq,
            "!=" => BinOp::Ne,
            "<=" => BinOp::Le,
            ">=" => BinOp::Ge,
            "<" => BinOp::Lt,
            _ => BinOp::Gt,
        },
        _ => BinOp::Add, // fallback
    }
}

fn parse_assign_op(s: &str) -> AssignOp {
    match s {
        "+=" => AssignOp::AddAssign,
        "-=" => AssignOp::SubAssign,
        "*=" => AssignOp::MulAssign,
        "/=" => AssignOp::DivAssign,
        "%=" => AssignOp::RemAssign,
        _ => AssignOp::Assign,
    }
}

fn expr_to_assign_target(expr: Expr) -> Result<AssignTarget, MetelError> {
    match expr {
        Expr::Ident(name, span) => Ok(AssignTarget::Ident(name, span)),
        // RFC-0110: `*p = v`.
        Expr::UnaryOp(UnaryOp::Deref, object, span) => Ok(AssignTarget::Deref { object, span }),
        Expr::FieldAccess {
            object,
            field,
            span,
        } => Ok(AssignTarget::FieldAccess {
            object,
            field,
            span,
        }),
        Expr::TupleAccess {
            object,
            index,
            span,
        } => Ok(AssignTarget::TupleAccess {
            object,
            index,
            span,
        }),
        Expr::Index {
            object,
            index,
            span,
        } => Ok(AssignTarget::Index {
            object,
            index,
            span,
        }),
        _ => Err(MetelError::internal(
            "assign target must be an identifier, field access, tuple access, or index expression",
        )),
    }
}

#[allow(clippy::only_used_in_recursion)]
// Exhaustive match over every AST/type-system variant; splitting it up would
// scatter one coherent dispatch table across many small functions with no
// real gain in clarity.
#[allow(clippy::too_many_lines)]
fn parse_type_expr(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<TypeExpr, MetelError> {
    match pair.as_rule() {
        Rule::type_expr => {
            let inner = pair
                .into_inner()
                .next()
                .ok_or_else(|| MetelError::internal("type_expr: missing inner rule"))?;
            parse_type_expr(inner, filename)
        }
        Rule::unit_type => Ok(TypeExpr::Unit),
        // RFC-0078: `!` lowers to the same AST shape the `Never` identifier
        // spelling already produces, reusing all existing `Never` machinery.
        Rule::never_type => Ok(TypeExpr::Named("Never".to_string(), vec![])),
        Rule::tuple_type => {
            let elems = pair
                .into_inner()
                .filter(|p| p.as_rule() == Rule::type_expr)
                .map(|p| parse_type_expr(p, filename))
                .collect::<Result<_, _>>()?;
            Ok(TypeExpr::Tuple(elems))
        }
        Rule::record_type => {
            let span = Span::of(&pair, filename);
            let mut fields = vec![];
            for field_pair in pair.into_inner() {
                if field_pair.as_rule() != Rule::record_type_field {
                    continue;
                }
                let mut inner = field_pair.into_inner();
                let name = inner
                    .next()
                    .ok_or_else(|| MetelError::internal("record_type: expected field name"))?
                    .as_str()
                    .to_string();
                let ty = parse_type_expr(
                    inner
                        .next()
                        .ok_or_else(|| MetelError::internal("record_type: expected field type"))?,
                    filename,
                )?;
                fields.push((name, ty));
            }
            sort_type_record_fields(&mut fields, filename, &span)?;
            Ok(TypeExpr::Record(fields))
        }
        Rule::reference_type => {
            let elem = parse_type_expr(
                pair.into_inner().next().ok_or_else(|| {
                    MetelError::internal("reference_type: expected referent type")
                })?,
                filename,
            )?;
            Ok(TypeExpr::Reference(Box::new(elem)))
        }
        Rule::mut_reference_type => {
            let elem = parse_type_expr(
                pair.into_inner()
                    .find(|p| p.as_rule() == Rule::type_expr)
                    .ok_or_else(|| {
                        MetelError::internal("mut_reference_type: expected referent type")
                    })?,
                filename,
            )?;
            Ok(TypeExpr::MutReference(Box::new(elem)))
        }
        Rule::sized_array_type => {
            let mut inner = pair.into_inner();
            let elem = parse_type_expr(
                inner.next().ok_or_else(|| {
                    MetelError::internal("sized_array_type: expected element type")
                })?,
                filename,
            )?;
            let n_str = inner
                .next()
                .ok_or_else(|| MetelError::internal("sized_array_type: expected count"))?
                .as_str();
            let n: u64 = n_str.parse().map_err(|_| {
                MetelError::internal(format!(
                    "sized_array_type: count '{n_str}' is not a valid u64"
                ))
            })?;
            Ok(TypeExpr::SizedArray(Box::new(elem), n))
        }
        Rule::array_type => {
            let elem = parse_type_expr(
                pair.into_inner()
                    .next()
                    .ok_or_else(|| MetelError::internal("array_type: expected element type"))?,
                filename,
            )?;
            Ok(TypeExpr::Array(Box::new(elem)))
        }
        Rule::fun_type => {
            let mut params = vec![];
            let mut return_type = None;
            let mut call_multiplicity = CallMultiplicity::Many;
            let mut call_mutation = CallMutation::Reading;
            for p in pair.into_inner() {
                match p.as_rule() {
                    Rule::fun_type_qualifier => match p.as_str() {
                        "once" => {
                            if call_multiplicity == CallMultiplicity::Once {
                                return Err(MetelError::parse(
                                    ParseErrorCode::P0001,
                                    "duplicate `once` function type qualifier",
                                    &Span::of(&p, filename),
                                ));
                            }
                            call_multiplicity = CallMultiplicity::Once;
                        }
                        "var" => {
                            if call_mutation == CallMutation::Mutating {
                                return Err(MetelError::parse(
                                    ParseErrorCode::P0001,
                                    "duplicate `var` function type qualifier",
                                    &Span::of(&p, filename),
                                ));
                            }
                            call_mutation = CallMutation::Mutating;
                        }
                        _ => {}
                    },
                    Rule::type_list => {
                        params = p
                            .into_inner()
                            .filter(|q| q.as_rule() == Rule::type_expr)
                            .map(|p| parse_type_expr(p, filename))
                            .collect::<Result<_, _>>()?;
                    }
                    Rule::type_expr => return_type = Some(Box::new(parse_type_expr(p, filename)?)),
                    _ => {}
                }
            }
            Ok(TypeExpr::Fun {
                params,
                return_type,
                call_multiplicity,
                call_mutation,
            })
        }
        Rule::named_type => {
            let mut inner = pair.into_inner();
            let path_pair = inner
                .next()
                .ok_or_else(|| MetelError::internal("named_type: expected name"))?;
            let name = collect_path_components(path_pair)?.join("::");
            let mut args = vec![];
            for p in inner {
                if p.as_rule() == Rule::type_args {
                    args = p
                        .into_inner()
                        .filter(|q| q.as_rule() == Rule::type_expr)
                        .map(|p| parse_type_expr(p, filename))
                        .collect::<Result<_, _>>()?;
                }
            }
            Ok(TypeExpr::Named(name, args))
        }
        Rule::record_projection_type => {
            let span = Span::of(&pair, filename);
            let mut inner = pair.into_inner();
            let path_pair = inner
                .next()
                .ok_or_else(|| MetelError::internal("record_projection_type: expected path"))?;
            let path = collect_path_components(path_pair)?;
            let mut fields: Vec<String> = inner.map(|p| p.as_str().to_string()).collect();
            sort_record_labels(&mut fields, filename, &span, "record projection")?;
            Ok(TypeExpr::RecordProjection { path, fields, span })
        }
        // RFC-0130: `extends Aspect` (renamed from `impl Aspect`). The AST node
        // keeps the internal name `ImplAspect`.
        Rule::extends_type => {
            let span = Span::of(&pair, filename);
            let source_spell = pair.as_str().to_string();
            let bound_pair = pair
                .into_inner()
                .next()
                .ok_or_else(|| MetelError::internal("extends_type: expected bound"))?;
            let bound = parse_type_expr(bound_pair, filename)?;
            Ok(TypeExpr::ImplAspect {
                bound: Box::new(bound),
                source_spell,
                span,
            })
        }
        Rule::dyn_type => {
            let span = Span::of(&pair, filename);
            let bound_pair = pair
                .into_inner()
                .next()
                .ok_or_else(|| MetelError::internal("dyn_type: expected bound"))?;
            let bound = parse_type_expr(bound_pair, filename)?;
            Ok(TypeExpr::DynAspect {
                bound: Box::new(bound),
                span,
            })
        }
        r => Err(MetelError::internal(format!(
            "type_expr: unexpected rule {r:?}"
        ))),
    }
}

fn sort_record_fields(
    fields: &mut [(String, Expr)],
    filename: &str,
    span: &Span,
) -> Result<(), MetelError> {
    fields.sort_by(|(left, _), (right, _)| left.cmp(right));
    for pair in fields.windows(2) {
        if pair[0].0 == pair[1].0 {
            return Err(record_duplicate_label_error(
                &pair[0].0,
                filename,
                span,
                "record literal",
            ));
        }
    }
    Ok(())
}

fn sort_type_record_fields(
    fields: &mut [(String, TypeExpr)],
    filename: &str,
    span: &Span,
) -> Result<(), MetelError> {
    fields.sort_by(|(left, _), (right, _)| left.cmp(right));
    for pair in fields.windows(2) {
        if pair[0].0 == pair[1].0 {
            return Err(record_duplicate_label_error(
                &pair[0].0,
                filename,
                span,
                "record type",
            ));
        }
    }
    Ok(())
}

fn sort_record_labels(
    fields: &mut [String],
    filename: &str,
    span: &Span,
    context: &str,
) -> Result<(), MetelError> {
    fields.sort();
    for pair in fields.windows(2) {
        if pair[0] == pair[1] {
            return Err(record_duplicate_label_error(
                &pair[0], filename, span, context,
            ));
        }
    }
    Ok(())
}

fn record_duplicate_label_error(
    label: &str,
    _filename: &str,
    span: &Span,
    context: &str,
) -> MetelError {
    MetelError::parse(
        ParseErrorCode::P0001,
        format!("duplicate label `{label}` in {context}"),
        span,
    )
}

fn parse_for_in_stmt(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<ForInStmt, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let first = inner
        .next()
        .ok_or_else(|| MetelError::internal("for_in: expected binding"))?;
    let (mutable, binding) = if first.as_rule() == Rule::ident {
        (false, first.as_str().to_string())
    } else {
        let name = inner
            .next()
            .ok_or_else(|| MetelError::internal("for_in: expected binding name after var"))?
            .as_str()
            .to_string();
        (true, name)
    };
    let iterable = parse_expr(
        inner
            .next()
            .ok_or_else(|| MetelError::internal("for_in: expected iterable expression"))?,
        filename,
    )?;
    let body = parse_block(
        inner
            .next()
            .ok_or_else(|| MetelError::internal("for_in: expected body block"))?,
        filename,
    )?;
    Ok(ForInStmt {
        binding,
        mutable,
        iterable,
        body,
        span,
    })
}

fn parse_block(pair: pest::iterators::Pair<Rule>, filename: &str) -> Result<Block, MetelError> {
    let span = Span::of(&pair, filename);
    let mut stmts = vec![];
    let mut tail = None;
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::block_item => {
                let inner = p
                    .into_inner()
                    .next()
                    .ok_or_else(|| MetelError::internal("block_item: missing inner rule"))?;
                match inner.as_rule() {
                    Rule::block_expr_stmt => {
                        let expr_pair = inner
                            .into_inner()
                            .next()
                            .ok_or_else(|| MetelError::internal("block_expr_stmt: missing expr"))?;
                        let expr = match expr_pair.as_rule() {
                            Rule::if_expr => parse_if_expr(expr_pair, filename)?,
                            Rule::match_expr => Expr::Match(parse_match_expr(expr_pair, filename)?),
                            Rule::loop_expr => parse_loop_expr(expr_pair, filename)?,
                            r => {
                                return Err(MetelError::internal(format!(
                                    "block_expr_stmt: unexpected rule {r:?}"
                                )))
                            }
                        };
                        stmts.push(Decl::Stmt(Box::new(Stmt::Expr(expr))));
                    }
                    Rule::decl => stmts.extend(parse_decl(inner, filename)?),
                    r => {
                        return Err(MetelError::internal(format!(
                            "block_item: unexpected rule {r:?}"
                        )))
                    }
                }
            }
            Rule::decl => stmts.extend(parse_decl(p, filename)?),
            Rule::expr => tail = Some(Box::new(parse_expr(p, filename)?)),
            _ => {}
        }
    }
    Ok(Block { stmts, tail, span })
}

fn parse_bound_list(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Vec<Bound>, MetelError> {
    pair.into_inner()
        .filter(|p| p.as_rule() == Rule::bound)
        .map(|p| parse_bound(p, filename))
        .collect()
}

fn parse_bound(pair: pest::iterators::Pair<Rule>, filename: &str) -> Result<Bound, MetelError> {
    let span = Span::of(&pair, filename);
    let mut polarity = Polarity::Positive;
    let mut head = None;
    let mut assoc_bindings = vec![];
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::bang => polarity = Polarity::Negative,
            Rule::bound_head => {
                let mut inner = p.into_inner();
                let first = inner
                    .next()
                    .ok_or_else(|| MetelError::internal("bound_head: expected content"))?;
                match first.as_rule() {
                    Rule::row_bound => {
                        head = Some(BoundHead::Row(parse_row_bound(first, filename)?));
                    }
                    Rule::type_path => {
                        let name = collect_path_components(first)?.join("::");
                        let mut args = vec![];
                        for arg in inner.filter(|q| q.as_rule() == Rule::bound_arg) {
                            let inner_arg = arg.into_inner().next().ok_or_else(|| {
                                MetelError::internal("bound_arg: expected content")
                            })?;
                            match inner_arg.as_rule() {
                                Rule::assoc_binding => {
                                    let mut it = inner_arg.into_inner();
                                    let assoc_name = it
                                        .next()
                                        .ok_or_else(|| {
                                            MetelError::internal("assoc_binding: expected name")
                                        })?
                                        .as_str()
                                        .to_string();
                                    let ty = parse_type_expr(
                                        it.next().ok_or_else(|| {
                                            MetelError::internal("assoc_binding: expected type")
                                        })?,
                                        filename,
                                    )?;
                                    assoc_bindings.push((assoc_name, ty));
                                }
                                Rule::type_expr => args.push(parse_type_expr(inner_arg, filename)?),
                                r => {
                                    return Err(MetelError::internal(format!(
                                        "bound_arg: unexpected rule {r:?}"
                                    )))
                                }
                            }
                        }
                        head = Some(BoundHead::Aspect(TypeExpr::Named(name, args)));
                    }
                    r => {
                        return Err(MetelError::internal(format!(
                            "bound_head: unexpected rule {r:?}"
                        )))
                    }
                }
            }
            _ => {}
        }
    }
    let head = head.ok_or_else(|| MetelError::internal("bound: expected bound_head"))?;

    // RFC-0118 §2: a negative row bound takes no `..` — absence has no rest to quantify
    // over. The grammar cannot express that (polarity and the row are separate pairs), and
    // the checker ignores `open` on the negative path, so without this the `..` would be
    // silently accepted as a no-op.
    if polarity == Polarity::Negative {
        if let BoundHead::Row(row) = &head {
            if row.open {
                return Err(MetelError::parse(
                    ParseErrorCode::P0001,
                    "a negative row bound takes no `..`: it names labels that must be absent, and absence has no rest to quantify over".to_string(),
                    &span,
                ));
            }
        }
    }

    Ok(Bound {
        polarity,
        head,
        assoc_bindings,
        span,
    })
}

fn parse_row_bound(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<RowBound, MetelError> {
    let span = Span::of(&pair, filename);
    let mut fields = Vec::new();
    let open = pair.as_str().contains("..");
    for p in pair.into_inner() {
        // The only other thing `row_bound` can yield is the trailing `..`, which is
        // already captured in `open` above.
        if p.as_rule() == Rule::row_field {
            let mut inner = p.into_inner();
            let label = inner
                .next()
                .ok_or_else(|| MetelError::internal("row_field: expected label"))?
                .as_str()
                .to_string();
            let ty = inner
                .next()
                .map(|te| parse_type_expr(te, filename))
                .transpose()?;
            fields.push(RowBoundField { label, ty });
        }
    }
    fields.sort_by(|a, b| a.label.cmp(&b.label));
    for pair in fields.windows(2) {
        if pair[0].label == pair[1].label {
            return Err(record_duplicate_label_error(
                &pair[0].label,
                filename,
                &span,
                "row bound",
            ));
        }
    }
    Ok(RowBound { fields, open })
}

fn parse_where_clause(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<WhereClause, MetelError> {
    let mut constraints = vec![];
    for p in pair.into_inner() {
        if p.as_rule() == Rule::where_constraint {
            let mut it = p.into_inner();
            let mut is_record = false;
            let first = it
                .next()
                .ok_or_else(|| MetelError::internal("where_constraint: expected param name"))?;
            let name_pair = if first.as_rule() == Rule::record_kw {
                is_record = true;
                it.next()
                    .ok_or_else(|| MetelError::internal("where_constraint: expected param name"))?
            } else {
                first
            };
            let name = name_pair.as_str().to_string();
            let bounds = it
                .next()
                .map(|bl| parse_bound_list(bl, filename))
                .transpose()?
                .unwrap_or_default();
            constraints.push(WhereConstraint {
                name,
                is_record,
                bounds,
            });
        }
    }
    Ok(WhereClause { constraints })
}

fn parse_generic_params(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<Vec<GenericParam>, MetelError> {
    let mut params = vec![];
    for p in pair.into_inner() {
        if p.as_rule() == Rule::generic_param {
            let mut it = p.into_inner();
            let mut is_record = false;
            let first = it
                .next()
                .ok_or_else(|| MetelError::internal("generic_param: expected name"))?;
            let name_pair = if first.as_rule() == Rule::record_kw {
                is_record = true;
                it.next()
                    .ok_or_else(|| MetelError::internal("generic_param: expected name"))?
            } else {
                first
            };
            let name = name_pair.as_str().to_string();
            let bounds = it
                .next()
                .map(|bl| parse_bound_list(bl, filename))
                .transpose()?
                .unwrap_or_default();
            params.push(GenericParam {
                name,
                is_record,
                bounds,
            });
        }
    }
    Ok(params)
}

fn parse_aspect_decl(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<AspectDecl, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let first = inner
        .next()
        .ok_or_else(|| MetelError::internal("aspect_decl: expected name"))?;
    let (visibility, name) = if first.as_rule() == Rule::pub_kw {
        let n = inner
            .next()
            .ok_or_else(|| MetelError::internal("aspect_decl: expected name after public"))?
            .as_str()
            .to_string();
        (Visibility::Public, n)
    } else {
        (Visibility::Private, first.as_str().to_string())
    };
    let mut generics = vec![];
    let mut assoc_types = vec![];
    let mut methods = vec![];
    for p in inner {
        match p.as_rule() {
            Rule::generic_params => {
                for gp in p.into_inner() {
                    if gp.as_rule() == Rule::generic_param {
                        let pname = gp
                            .into_inner()
                            .next()
                            .map(|i| i.as_str().to_string())
                            .unwrap_or_default();
                        generics.push(pname);
                    }
                }
            }
            Rule::assoc_type_decl => {
                assoc_types.push(parse_assoc_type_decl(p, filename)?);
            }
            Rule::aspect_method => {
                methods.push(parse_aspect_method(p, filename)?);
            }
            _ => {}
        }
    }
    Ok(AspectDecl {
        visibility,
        name,
        generics,
        assoc_types,
        methods,
        span,
    })
}

fn parse_assoc_type_decl(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<AssocTypeDecl, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let name = inner
        .next()
        .ok_or_else(|| MetelError::internal("assoc_type_decl: expected name"))?
        .as_str()
        .to_string();
    let bounds = inner
        .next()
        .map(|bl| parse_bound_list(bl, filename))
        .transpose()?
        .unwrap_or_default();
    Ok(AssocTypeDecl { name, bounds, span })
}

fn parse_type_alias(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<crate::ast::TypeAliasDecl, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner().peekable();
    let visibility = if inner.peek().map(pest::iterators::Pair::as_rule) == Some(Rule::pub_kw) {
        inner.next();
        Visibility::Public
    } else {
        Visibility::Private
    };
    let name = inner
        .next()
        .ok_or_else(|| MetelError::internal("type_alias: expected name"))?
        .as_str()
        .to_string();
    let mut generics = vec![];
    let mut target = None;
    for p in inner {
        match p.as_rule() {
            Rule::generic_params => generics = parse_generic_params(p, filename)?,
            Rule::type_expr => target = Some(parse_type_expr(p, filename)?),
            _ => {}
        }
    }
    Ok(crate::ast::TypeAliasDecl {
        visibility,
        name,
        generics,
        target: target.ok_or_else(|| MetelError::internal("type_alias: expected target type"))?,
        span,
    })
}

fn parse_assoc_type_def(
    pair: pest::iterators::Pair<Rule>,
    filename: &str,
) -> Result<AssocTypeDef, MetelError> {
    let span = Span::of(&pair, filename);
    let mut inner = pair.into_inner();
    let name = inner
        .next()
        .ok_or_else(|| MetelError::internal("assoc_type_def: expected name"))?
        .as_str()
        .to_string();
    let ty = parse_type_expr(
        inner
            .next()
            .ok_or_else(|| MetelError::internal("assoc_type_def: expected type"))?,
        filename,
    )?;
    Ok(AssocTypeDef { name, ty, span })
}

fn parse_char_inner(s: &str) -> Option<char> {
    if let Some(rest) = s.strip_prefix('\\') {
        let mut chars = rest.chars();
        match chars.next()? {
            'n' => Some('\n'),
            't' => Some('\t'),
            'r' => Some('\r'),
            '\\' => Some('\\'),
            '\'' => Some('\''),
            'u' => {
                let hex = rest.strip_prefix("u{")?.strip_suffix('}')?;
                let code = u32::from_str_radix(hex, 16).ok()?;
                char::from_u32(code)
            }
            _ => None,
        }
    } else {
        let mut chars = s.chars();
        let c = chars.next()?;
        if chars.next().is_none() {
            Some(c)
        } else {
            None
        }
    }
}

fn unescape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => out.push('\n'),
                Some('t') => out.push('\t'),
                Some('r') => out.push('\r'),
                Some('\\') | None => out.push('\\'),
                Some('"') => out.push('"'),
                Some('$') => out.push('$'),
                Some(c) => {
                    out.push('\\');
                    out.push(c);
                }
            }
        } else {
            out.push(c);
        }
    }
    out
}

#[cfg(test)]
mod path_segment_span_tests {
    use super::parse;
    use crate::ast::{Decl, Expr};

    /// The tail expression of `fn main`.
    fn main_tail(src: &str) -> Expr {
        let program = parse(src, "t.mtl").expect("parse");
        let main = program
            .decls
            .iter()
            .find_map(|d| match d {
                Decl::Fun(f) if f.name == "main" => Some(f),
                _ => None,
            })
            .expect("fn main");
        main.body.tail.as_deref().expect("tail expr").clone()
    }

    #[test]
    fn multi_segment_path_carries_one_span_per_segment() {
        // `mod::inner::Thing` — three segments, each span slicing its own name.
        let src = "fun main() -> i64 { mod::inner::Thing }\n";
        let Expr::Path(segments, seg_spans, _) = main_tail(src) else {
            panic!("expected an Expr::Path");
        };
        assert_eq!(segments, ["mod", "inner", "Thing"]);
        assert_eq!(seg_spans.len(), 3);
        for (name, span) in segments.iter().zip(&seg_spans) {
            assert_eq!(&src[span.start..span.end], name);
            assert_eq!(span.filename, "t.mtl");
        }
        // Segments are in source order, non-overlapping, left to right.
        assert!(seg_spans[0].end <= seg_spans[1].start);
        assert!(seg_spans[1].end <= seg_spans[2].start);
    }

    #[test]
    fn keyword_root_path_spans_cover_the_root_segment() {
        let src = "fun main() -> i64 { root::top::V }\n";
        let Expr::Path(segments, seg_spans, _) = main_tail(src) else {
            panic!("expected an Expr::Path");
        };
        assert_eq!(segments, ["root", "top", "V"]);
        assert_eq!(seg_spans.len(), segments.len());
        assert_eq!(&src[seg_spans[0].start..seg_spans[0].end], "root");
    }

    #[test]
    fn two_segment_path_in_call_position_keeps_segment_spans() {
        let src = "fun main() -> i64 { helpers::run() }\n";
        let Expr::Call { callee, .. } = main_tail(src) else {
            panic!("expected the tail to be a call");
        };
        let Expr::Path(segments, seg_spans, _) = *callee else {
            panic!("expected the callee to be an Expr::Path");
        };
        assert_eq!(segments, ["helpers", "run"]);
        assert_eq!(seg_spans.len(), 2);
        assert_eq!(&src[seg_spans[0].start..seg_spans[0].end], "helpers");
        assert_eq!(&src[seg_spans[1].start..seg_spans[1].end], "run");
    }
}
