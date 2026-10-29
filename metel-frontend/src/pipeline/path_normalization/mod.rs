//! Path normalization pass (#185).
//!
//! Rewrites `Expr::Path` nodes with module qualifiers to `Expr::ResolvedPath`.
//! Single-segment paths and type member accesses (e.g. `Color::Red`) are left as-is.
//!
//! A path `[s1, s2, ...]` is considered module-qualified when `s1` is:
//! - the reserved keyword `"root"`, `"self"`, or `"super"`, or
//! - the name of a loaded module in the `ModuleGraph`.
//!
//! Everything else (e.g. `Color::Red` where Color is a struct/enum) passes through
//! unchanged so the typechecker's existing type-member handling works unmodified.

use std::collections::HashSet;
use std::rc::Rc;

use crate::data::ast::Span;
use crate::data::ast::{
    Block, Decl, Expr, ForInit, FunDecl, ImplBlock, LetDecl, MatchArm, MutDecl, Stmt,
};
use crate::data::error::MetelError;
use crate::identity::symbols::{Namespace, SymbolId};
use crate::pipeline::name_resolution::name_resolver::{
    ImportBinding, ModuleScope, QualifiedPath, ResolvedNames,
};
use crate::pipeline::parsing::module_loader::{LoadedModule, ModuleGraph};

// ── Public API ────────────────────────────────────────────────────────────────

/// Opaque wrapper around `ModuleGraph` that proves the normalization pass has run.
/// `check_graph` requires this type; calling it with a raw `ModuleGraph` is a
/// compile-time error. See ADR-0021.
///
/// Also carries the `ResolvedNames` the normalization pass ran against, so
/// `coherence::check` and the typechecker's graph-level entry points read it
/// off this graph instead of taking it as a second, separately-threaded
/// parameter (metel-core#1250).
pub struct NormalizedModuleGraph {
    pub(crate) graph: ModuleGraph,
    pub(crate) names: Rc<ResolvedNames>,
}

impl NormalizedModuleGraph {
    #[must_use]
    pub fn modules(&self) -> &[LoadedModule] {
        &self.graph.modules
    }
}

/// What the rewrite needs to resolve a path: the canonical symbol table, and which enum variants
/// are unit variants (a variant with no fields is written as a bare path and used as a value).
struct PathSymbols<'a> {
    map: &'a crate::identity::symbols::SymbolMap,
    /// `(declaring module, enum name, variant name)` of every unit variant, with whether its enum
    /// is `public` (a path from another module may only name a public enum).
    unit_variants: std::collections::HashMap<(Vec<String>, String, String), bool>,
    /// `(declaring module, type name)` of every `public` struct, record and enum.
    public_types: HashSet<(Vec<String>, String)>,
    /// The `module::Type::member` paths rewritten so far, per module, for the type checker
    /// (`ModuleScope::qualified_paths`).
    qualified: std::cell::RefCell<Vec<(Vec<String>, Span, QualifiedPath)>>,
}

// arch-implements: ["arch.path-normalization.requirement-1"]
/// Run the path normalization pass on `graph`, rewriting qualified `Expr::Path`
/// nodes to `Expr::ResolvedPath` using the scope information in `names`.
///
/// Returns `NormalizedModuleGraph` — a newtype that downstream passes must accept
/// to enforce that normalization ran before typechecking. It carries `names`
/// forward so coherence checking and typechecking don't need it as a second
/// parameter of their own (metel-core#1250).
///
/// # Errors
/// Returns an error if a qualified path cannot be resolved against `names`
/// (e.g. references an unknown module or name).
pub fn normalize(
    mut graph: ModuleGraph,
    mut names: Rc<ResolvedNames>,
) -> Result<NormalizedModuleGraph, MetelError> {
    let module_names: HashSet<String> = graph
        .modules
        .iter()
        .filter_map(|m| m.module_path.first().cloned())
        .collect();

    let mut unit_variants = std::collections::HashMap::new();
    let mut public_types = HashSet::new();
    for loaded in &graph.modules {
        for decl in &loaded.program.decls {
            if let Decl::Struct(decl) = decl
                && matches!(decl.visibility, crate::data::ast::Visibility::Public)
            {
                public_types.insert((loaded.module_path.clone(), decl.name.clone()));
            }
            if let Decl::Enum(decl) = decl {
                let public = matches!(decl.visibility, crate::data::ast::Visibility::Public);
                if public {
                    public_types.insert((loaded.module_path.clone(), decl.name.clone()));
                }
                for variant in decl.variants.iter().filter(|v| v.fields.is_empty()) {
                    unit_variants.insert(
                        (
                            loaded.module_path.clone(),
                            decl.name.clone(),
                            variant.name.clone(),
                        ),
                        public,
                    );
                }
            }
        }
    }
    let qualified = {
        let symbols = PathSymbols {
            map: &names.symbols,
            unit_variants,
            public_types,
            qualified: std::cell::RefCell::new(Vec::new()),
        };
        for loaded in &mut graph.modules {
            let scope = names.scopes.get(&loaded.module_path);
            normalize_program_decls(
                &mut loaded.program.decls,
                scope,
                &loaded.module_path,
                &module_names,
                &symbols,
            )?;
        }
        symbols.qualified.into_inner()
    };
    if !qualified.is_empty() {
        let names_mut = Rc::make_mut(&mut names);
        for (module, span, path) in qualified {
            if let Some(scope) = names_mut.scopes.get_mut(&module) {
                scope.qualified_paths.insert(span, path);
            }
        }
    }
    Ok(NormalizedModuleGraph { graph, names })
}

// ── Internal helpers ──────────────────────────────────────────────────────────

fn normalize_program_decls(
    decls: &mut Vec<Decl>,
    scope: Option<&ModuleScope>,
    current_module: &[String],
    module_names: &HashSet<String>,
    symbols: &PathSymbols<'_>,
) -> Result<(), MetelError> {
    for decl in decls {
        normalize_decl(decl, scope, current_module, module_names, symbols)?;
    }
    Ok(())
}

fn normalize_decl(
    decl: &mut Decl,
    scope: Option<&ModuleScope>,
    current_module: &[String],
    module_names: &HashSet<String>,
    symbols: &PathSymbols<'_>,
) -> Result<(), MetelError> {
    match decl {
        Decl::Let(ld) => {
            normalize_expr(&mut ld.value, scope, current_module, module_names, symbols)
        }
        Decl::LetPattern(ld) => {
            normalize_expr(&mut ld.value, scope, current_module, module_names, symbols)
        }
        Decl::Mut(md) => {
            normalize_expr(&mut md.value, scope, current_module, module_names, symbols)
        }
        Decl::Fun(fd) => normalize_fun(fd, scope, current_module, module_names, symbols),
        Decl::Impl(ib) => normalize_impl(ib, scope, current_module, module_names, symbols),
        Decl::Stmt(s) => normalize_stmt(s, scope, current_module, module_names, symbols),
        Decl::Struct(_) | Decl::Enum(_) | Decl::Aspect(_) => Ok(()),
        Decl::TypeAlias(_) => {
            unreachable!("RFC-0160 type aliases are expanded before path normalization")
        }
    }
}

fn normalize_fun(
    fun: &mut FunDecl,
    scope: Option<&ModuleScope>,
    current_module: &[String],
    module_names: &HashSet<String>,
    symbols: &PathSymbols<'_>,
) -> Result<(), MetelError> {
    normalize_block(&mut fun.body, scope, current_module, module_names, symbols)
}

fn normalize_impl(
    ib: &mut ImplBlock,
    scope: Option<&ModuleScope>,
    current_module: &[String],
    module_names: &HashSet<String>,
    symbols: &PathSymbols<'_>,
) -> Result<(), MetelError> {
    for method in &mut ib.methods {
        normalize_fun(method, scope, current_module, module_names, symbols)?;
    }
    Ok(())
}

fn normalize_block(
    block: &mut Block,
    scope: Option<&ModuleScope>,
    current_module: &[String],
    module_names: &HashSet<String>,
    symbols: &PathSymbols<'_>,
) -> Result<(), MetelError> {
    for decl in &mut block.stmts {
        normalize_decl(decl, scope, current_module, module_names, symbols)?;
    }
    if let Some(tail) = &mut block.tail {
        normalize_expr(tail, scope, current_module, module_names, symbols)?;
    }
    Ok(())
}

fn normalize_stmt(
    stmt: &mut Stmt,
    scope: Option<&ModuleScope>,
    current_module: &[String],
    module_names: &HashSet<String>,
    symbols: &PathSymbols<'_>,
) -> Result<(), MetelError> {
    match stmt {
        Stmt::Expr(e) => normalize_expr(e, scope, current_module, module_names, symbols),
        Stmt::While(w) => {
            normalize_expr(
                &mut w.condition,
                scope,
                current_module,
                module_names,
                symbols,
            )?;
            normalize_block(&mut w.body, scope, current_module, module_names, symbols)
        }
        Stmt::For(f) => {
            if let Some(init) = &mut f.init {
                match init {
                    ForInit::Expr(e) => {
                        normalize_expr(e, scope, current_module, module_names, symbols)?;
                    }
                    ForInit::Let(ld) => {
                        normalize_let_decl(ld, scope, current_module, module_names, symbols)?;
                    }
                    ForInit::Mut(md) => {
                        normalize_mut_decl(md, scope, current_module, module_names, symbols)?;
                    }
                }
            }
            if let Some(cond) = &mut f.condition {
                normalize_expr(cond, scope, current_module, module_names, symbols)?;
            }
            if let Some(step) = &mut f.step {
                normalize_expr(step, scope, current_module, module_names, symbols)?;
            }
            normalize_block(&mut f.body, scope, current_module, module_names, symbols)
        }
        Stmt::ForIn(fi) => {
            normalize_expr(
                &mut fi.iterable,
                scope,
                current_module,
                module_names,
                symbols,
            )?;
            normalize_block(&mut fi.body, scope, current_module, module_names, symbols)
        }
    }
}

fn normalize_mut_decl(
    md: &mut MutDecl,
    scope: Option<&ModuleScope>,
    current_module: &[String],
    module_names: &HashSet<String>,
    symbols: &PathSymbols<'_>,
) -> Result<(), MetelError> {
    normalize_expr(&mut md.value, scope, current_module, module_names, symbols)
}

fn normalize_let_decl(
    ld: &mut LetDecl,
    scope: Option<&ModuleScope>,
    current_module: &[String],
    module_names: &HashSet<String>,
    symbols: &PathSymbols<'_>,
) -> Result<(), MetelError> {
    normalize_expr(&mut ld.value, scope, current_module, module_names, symbols)
}

// Exhaustive match over every AST/type-system variant; splitting it up would
// scatter one coherent dispatch table across many small functions with no
// real gain in clarity.
#[allow(clippy::too_many_lines)]
fn normalize_expr(
    expr: &mut Expr,
    scope: Option<&ModuleScope>,
    current_module: &[String],
    module_names: &HashSet<String>,
    symbols: &PathSymbols<'_>,
) -> Result<(), MetelError> {
    match expr {
        Expr::Literal(_, _) | Expr::Ident(_, _) | Expr::ResolvedPath { .. } | Expr::Continue(_) => {
            Ok(())
        }

        Expr::Path(segments, seg_spans, span) => {
            if let Some((path, type_id)) =
                try_normalize_unit_variant_path(segments, current_module, symbols)
            {
                *expr = Expr::StructLiteral {
                    path,
                    fields: Vec::new(),
                    symbol_id: Some(type_id),
                    span: span.clone(),
                };
                return Ok(());
            }
            if let Some((path, path_spans, type_id)) =
                try_normalize_static_member_path(segments, seg_spans, current_module, symbols)
            {
                symbols.qualified.borrow_mut().push((
                    current_module.to_vec(),
                    span.clone(),
                    QualifiedPath {
                        type_id,
                        original: segments.clone(),
                    },
                ));
                *expr = Expr::Path(path, path_spans, span.clone());
                return Ok(());
            }
            if let Some((resolved, symbol_id)) =
                try_resolve_path(segments, scope, current_module, module_names, symbols)
            {
                let original = std::mem::take(segments);
                *expr = Expr::ResolvedPath {
                    resolved,
                    symbol_id,
                    original,
                    span: span.clone(),
                };
            }
            Ok(())
        }

        Expr::Tuple(elems, _) | Expr::Array(elems, _) => {
            for e in elems {
                normalize_expr(e, scope, current_module, module_names, symbols)?;
            }
            Ok(())
        }
        Expr::RecordLiteral { fields, spread, .. } => {
            for (_, expr) in fields {
                normalize_expr(expr, scope, current_module, module_names, symbols)?;
            }
            if let Some((expr, _, _)) = spread {
                normalize_expr(expr, scope, current_module, module_names, symbols)?;
            }
            Ok(())
        }
        Expr::RepeatArray(elem, _, _) => {
            normalize_expr(elem, scope, current_module, module_names, symbols)
        }
        Expr::BinOp(lhs, _, rhs, _) => {
            normalize_expr(lhs, scope, current_module, module_names, symbols)?;
            normalize_expr(rhs, scope, current_module, module_names, symbols)
        }
        Expr::UnaryOp(_, operand, _) => {
            normalize_expr(operand, scope, current_module, module_names, symbols)
        }
        Expr::Cast { expr: inner, .. } | Expr::Ascribe { expr: inner, .. } => {
            normalize_expr(inner, scope, current_module, module_names, symbols)
        }
        Expr::Assign { value, .. } => {
            normalize_expr(value, scope, current_module, module_names, symbols)
        }
        Expr::Call { callee, args, .. } => {
            normalize_expr(callee, scope, current_module, module_names, symbols)?;
            for a in args {
                normalize_expr(a, scope, current_module, module_names, symbols)?;
            }
            Ok(())
        }
        Expr::MethodCall { receiver, args, .. } => {
            normalize_expr(receiver, scope, current_module, module_names, symbols)?;
            for a in args {
                normalize_expr(a, scope, current_module, module_names, symbols)?;
            }
            Ok(())
        }
        Expr::FieldAccess { object, .. } | Expr::TupleAccess { object, .. } => {
            normalize_expr(object, scope, current_module, module_names, symbols)
        }
        Expr::Index { object, index, .. } => {
            normalize_expr(object, scope, current_module, module_names, symbols)?;
            normalize_expr(index, scope, current_module, module_names, symbols)
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            normalize_expr(condition, scope, current_module, module_names, symbols)?;
            normalize_block(then_branch, scope, current_module, module_names, symbols)?;
            if let Some(eb) = else_branch {
                normalize_block(eb, scope, current_module, module_names, symbols)?;
            }
            Ok(())
        }
        Expr::Loop { body, .. } | Expr::Closure { body, .. } => {
            normalize_block(body, scope, current_module, module_names, symbols)
        }
        Expr::Match(m) => {
            normalize_expr(
                &mut m.scrutinee,
                scope,
                current_module,
                module_names,
                symbols,
            )?;
            for arm in &mut m.arms {
                normalize_arm(arm, scope, current_module, module_names, symbols)?;
            }
            Ok(())
        }
        Expr::StructLiteral {
            path,
            fields,
            symbol_id,
            ..
        } => {
            if let Some((local_path, type_id)) =
                try_normalize_struct_path(path, scope, module_names, symbols)
            {
                *path = local_path;
                *symbol_id = type_id;
            } else if let [only] = path.as_mut_slice() {
                // A single-segment path can still be an alias (#667): `import
                // lexer::Token as Tok;` then `Tok { .. }` needs to construct the
                // same `Token` a bare `Token { .. }` would, not go looking for a
                // never-declared type literally named `Tok`. Only item bindings
                // apply -- a `Module` binding here would mean `path` should have had
                // a second segment (`handle::Type`), a different, already-handled
                // shape.
                if let Some(binding) =
                    scope.and_then(|s| s.explicit.get(&(Namespace::Type, only.clone())))
                    && binding.kind
                        == crate::pipeline::name_resolution::name_resolver::BindingKind::Item
                {
                    *only = binding.source_name.clone();
                    *symbol_id = Some(binding.symbol_id);
                }
            }
            for (_, v) in fields {
                normalize_expr(v, scope, current_module, module_names, symbols)?;
            }
            Ok(())
        }
        Expr::RecordProjection { path, .. } => {
            if let Some((resolved, _symbol_id)) =
                try_resolve_path(path, scope, current_module, module_names, symbols)
            {
                *path = vec![resolved];
            }
            Ok(())
        }
        Expr::PropagateError { expr, .. } => {
            normalize_expr(expr, scope, current_module, module_names, symbols)
        }
        Expr::Return(r) => match &mut r.value {
            Some(v) => normalize_expr(v, scope, current_module, module_names, symbols),
            None => Ok(()),
        },
        Expr::Break(b) => match &mut b.value {
            Some(v) => normalize_expr(v, scope, current_module, module_names, symbols),
            None => Ok(()),
        },
    }
}

fn normalize_arm(
    arm: &mut MatchArm,
    scope: Option<&ModuleScope>,
    current_module: &[String],
    module_names: &HashSet<String>,
    symbols: &PathSymbols<'_>,
) -> Result<(), MetelError> {
    if let Some(guard) = &mut arm.guard {
        normalize_expr(guard, scope, current_module, module_names, symbols)?;
    }
    normalize_block(&mut arm.body, scope, current_module, module_names, symbols)
}

/// The symbol `module` declares under `name`, as a path segment would name it: a value (a
/// function, `let`, `var`) first, then a type (a unit struct), the order a single shared key gave
/// before the two namespaces were told apart.
fn lookup_symbol(
    symbols: &PathSymbols<'_>,
    module: &[String],
    name: &str,
) -> Option<crate::identity::symbols::SymbolId> {
    [Namespace::Value, Namespace::Type]
        .into_iter()
        .find_map(|ns| {
            symbols
                .map
                .get(&(module.to_vec(), ns, name.to_string()))
                .copied()
        })
}

/// The explicit import binding satisfying `pred`, with its local name. A name imported in both
/// namespaces is tried value-first, so the answer does not depend on map iteration order.
fn explicit_binding(
    scope: &ModuleScope,
    pred: impl Fn(&str, &ImportBinding) -> bool,
) -> Option<(&String, &ImportBinding)> {
    [Namespace::Value, Namespace::Type]
        .into_iter()
        .find_map(|ns| {
            let mut hits: Vec<_> = scope
                .explicit
                .iter()
                .filter(|((binding_ns, local), binding)| *binding_ns == ns && pred(local, binding))
                .map(|((_, local), binding)| (local, binding))
                .collect();
            // Several local names can import one source name; take the smallest for determinism.
            hits.sort_by(|a, b| a.0.cmp(b.0));
            hits.into_iter().next()
        })
}

// ── Path resolution logic ─────────────────────────────────────────────────────

/// Try to resolve a multi-segment path to a bare local name and its stable symbol identity.
///
/// Returns `Some((resolved_name, symbol_id))` if the path is module-qualified and can be
/// rewritten. Returns `None` to leave the path unchanged (type member access,
/// single-segment, or unresolvable).
// limit: ["LIMIT-PATH-NORMALIZATION-001"]
fn try_resolve_path(
    segments: &[String],
    scope: Option<&ModuleScope>,
    // The module this path appears in — needed to resolve `self::name` to its
    // own declaration's `SymbolId` (metel-core#1052b-3f / #1054): unlike an
    // import, there is no `ImportBinding` to read one from, since `self::`
    // refers to a same-module declaration rather than an imported name.
    current_module: &[String],
    module_names: &HashSet<String>,
    // An explicit import's `symbol_id` comes straight off the module scope's
    // binding; a glob-imported name has no such binding to read one from, so
    // it is looked up here instead (ADR-0054 / metel-core#1052) — a
    // glob-imported name is still a reference to its declaring module's own
    // canonical declaration.
    symbols: &PathSymbols<'_>,
) -> Option<(String, Option<SymbolId>)> {
    if segments.len() < 2 {
        return None; // single-segment paths are already Ident
    }

    let first = &segments[0];
    let declared_name = segments.last().unwrap();

    // Keywords: root/self/super — the declared name is the last segment
    if first == "root" || first == "self" || first == "super" {
        // Check the scope for an alias, otherwise use the declared name
        if let Some(s) = scope
            && let Some((local, binding)) =
                explicit_binding(s, |_, b| &b.source_name == declared_name)
        {
            return Some((local.clone(), Some(binding.symbol_id)));
        }
        // `self::name` with no explicit alias refers to this same module's own
        // declaration — look its `SymbolId` up directly rather than leaving it
        // `None` (which forced evaluation back onto the name map). `root`/
        // `super` aren't resolved to a module here (this pass doesn't track
        // module hierarchy), so they keep the pre-existing `None` and rely on
        // downstream name resolution, same as before.
        let symbol_id = if first == "self" {
            lookup_symbol(symbols, current_module, declared_name)
        } else {
            None
        };
        return Some((declared_name.clone(), symbol_id));
    }

    // Accept if `first` is either a loaded module name OR the first segment of a glob path
    // (handles virtual modules like `std` that have no physical file).
    let is_known_prefix = module_names.contains(first.as_str())
        || scope.is_some_and(|s| {
            s.globs
                .iter()
                .any(|(_, g)| g.first().map(std::string::String::as_str) == Some(first.as_str()))
        });

    if !is_known_prefix {
        return None; // e.g. Color::Red — Color is a type, not a module
    }

    // first is a known module prefix — find the local alias for this import
    if let Some(s) = scope {
        // 1. Explicit import with matching source
        if let Some((local_name, binding)) = explicit_binding(s, |_, binding| {
            binding
                .source_module
                .first()
                .map(std::string::String::as_str)
                == Some(first.as_str())
                && &binding.source_name == declared_name
        }) {
            return Some((local_name.clone(), Some(binding.symbol_id)));
        }
        // 2. Glob import from this module — local name == source name
        let source_module: Vec<String> = segments[..segments.len() - 1].to_vec();
        if s.globs.iter().any(|(_, g)| {
            g == &source_module
                || g.first().map(std::string::String::as_str) == Some(first.as_str())
        }) {
            let symbol_id = lookup_symbol(symbols, &source_module, declared_name);
            return Some((declared_name.clone(), symbol_id));
        }
    }

    // Module is known but no import binding found for this name — treat as bare name
    // (the typechecker will error if it's actually undefined)
    Some((declared_name.clone(), None))
}

/// A module-qualified path to a unit variant used as a value (`lib::Kind::A`,
/// `std::core::Option::None`), as the fieldless variant literal `Kind::A {}` stamped with the id of
/// the enum its module prefix names (metel-core#1680).
///
/// The typechecker finds `Kind::A` by the bare type name, which is the module's own enum when it
/// declares one, and needs `Kind` to be in scope at all; the qualified path means neither. Reading
/// the enum off the prefix is what the stamped id carries, as for a qualified struct literal
/// (`try_normalize_struct_path`). A fieldful variant, or an enum the current module may not name,
/// is left as it was.
fn try_normalize_unit_variant_path(
    segments: &[String],
    current_module: &[String],
    symbols: &PathSymbols<'_>,
) -> Option<(Vec<String>, SymbolId)> {
    // `[module.., Enum, Variant]`, with at least one module segment.
    if segments.len() < 3 {
        return None;
    }
    let (variant, rest) = segments.split_last()?;
    let (enum_name, module) = rest.split_last()?;
    let public =
        *symbols
            .unit_variants
            .get(&(module.to_vec(), enum_name.clone(), variant.clone()))?;
    if !public && module != current_module {
        return None;
    }
    let enum_id = *symbols
        .map
        .get(&(module.to_vec(), Namespace::Type, enum_name.clone()))?;
    Some((vec![enum_name.clone(), variant.clone()], enum_id))
}

/// A module-qualified path to a member of a type (`lib::Kind::make`, `std::core::List::new`), as the
/// two-segment `Type::member` the type checker resolves, plus the type its module prefix names
/// (metel-core#1683).
///
/// The two-segment form is looked up by the bare type name, which needs the type in scope and is
/// the current module's own type when it declares one; the qualified path means neither. The
/// returned id travels to the checker in `ModuleScope::qualified_paths`, keyed by the path's span.
/// A type the current module may not name (not `public`, from another module) is left alone.
fn try_normalize_static_member_path(
    segments: &[String],
    seg_spans: &[Span],
    current_module: &[String],
    symbols: &PathSymbols<'_>,
) -> Option<(Vec<String>, Vec<Span>, SymbolId)> {
    // `[module.., Type, member]`, with at least one module segment.
    if segments.len() < 3 {
        return None;
    }
    let (member, rest) = segments.split_last()?;
    let (type_name, module) = rest.split_last()?;
    let type_id = *symbols
        .map
        .get(&(module.to_vec(), Namespace::Type, type_name.clone()))?;
    if module != current_module
        && !symbols
            .public_types
            .contains(&(module.to_vec(), type_name.clone()))
    {
        return None;
    }
    let spans = if seg_spans.len() == segments.len() {
        seg_spans[segments.len() - 2..].to_vec()
    } else {
        Vec::new()
    };
    Some((vec![type_name.clone(), member.clone()], spans, type_id))
}

/// Resolve a struct-literal path by stripping a module prefix, returning the local
/// `type[+variant]` path and the constructed type's stable `SymbolId` (METEL-185).
/// For `["std", "core", "Option", "Some"]` returns `(["Option", "Some"], id_of(Option))`.
/// Returns `None` if the path starts with a type name, not a module.
fn try_normalize_struct_path(
    path: &[String],
    scope: Option<&ModuleScope>,
    module_names: &HashSet<String>,
    symbols: &PathSymbols<'_>,
) -> Option<(Vec<String>, Option<crate::identity::symbols::SymbolId>)> {
    if path.len() < 2 {
        return None;
    }
    let first = &path[0];
    // Only process if the first segment looks like a module, not a type.
    let is_known_prefix = module_names.contains(first.as_str())
        || scope.is_some_and(|s| {
            s.globs
                .iter()
                .any(|(_, g)| g.first().map(std::string::String::as_str) == Some(first.as_str()))
        });
    if !is_known_prefix {
        return None;
    }
    let s = scope?;
    // Find the longest glob prefix that matches the beginning of the path,
    // then return the remainder as the local type+variant path.
    let mut best: Option<usize> = None;
    for (_, glob_module) in &s.globs {
        if path.starts_with(glob_module.as_slice()) && path.len() > glob_module.len() {
            let len = glob_module.len();
            if best.is_none_or(|b| len > b) {
                best = Some(len);
            }
        }
    }
    let prefix_len = best?;
    // The stripped remainder is `[TypeName]` (struct) or `[EnumName, Variant]` (enum).
    // Either way the *type* is its first segment, declared in the matched module.
    let module = path[..prefix_len].to_vec();
    let type_name = &path[prefix_len];
    let type_id = symbols
        .map
        .get(&(module, Namespace::Type, type_name.clone()))
        .copied();
    Some((path[prefix_len..].to_vec(), type_id))
}

// ── Desugar ? operator ────────────────────────────────────────────────────────
//

#[cfg(test)]
mod tests;

#[cfg(test)]
mod architecture_evidence_tests {
    // arch-verifies: ["arch.path-normalization.requirement-1"]
    #[test]
    fn normalized_graph_can_only_be_built_inside_this_crate() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("src/pipeline/path_normalization/mod.rs");
        let source =
            std::fs::read_to_string(path).expect("pipeline/path_normalization/mod.rs readable");
        assert!(
            source.contains("pub(crate) graph: ModuleGraph,")
                && source.contains("pub(crate) names: Rc<ResolvedNames>,"),
            "NormalizedModuleGraph's fields must stay crate-private so only `normalize` can produce one"
        );
    }
}
