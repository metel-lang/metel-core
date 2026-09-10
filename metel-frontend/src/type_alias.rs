//! RFC-0160: transparent type aliases.
//!
//! `type Name<G> := T;` introduces a name that is **erased to its right-hand side
//! before any further reasoning** — name resolution, coherence, and the
//! typechecker never see an alias. This pass runs right after `module_loader`:
//! it collects every module's aliases, fully expands their targets against one
//! another (rejecting cycles), rewrites every `TypeExpr` in the graph, and drops
//! the alias declarations.
//!
//! Scope covered:
//! - **Module-level aliases**, parameterised, alias-of-alias.
//! - **Block / function-local aliases** (`type` inside a body), with lexical
//!   shadowing of an outer alias of the same name.
//! - **Cross-module aliases** — a `pub type` imported by name (`import m::{A};`),
//!   under a local rename (`import m::A as B;`), through a glob (`import m::*;`),
//!   re-exported by an intermediate module (`export m::{A};`, one hop), or
//!   referenced qualified in type position (`m::A`). Referencing another
//!   module's non-`public` alias is `T0009`.
//! - Every `TypeExpr` position: signatures, fields, generic / where bounds, and
//!   type annotations nested inside expressions (a closure parameter annotation,
//!   a cast, an ascription, a turbofish).
//! - A **value / pattern path** that leads with an alias for a plain named type:
//!   `P { … }`, `P.{ … }`, `P::Variant`, a `P { … }` match arm. A parameterised
//!   alias, or one whose target is not a bare `Named`, is left untouched.

use std::collections::{HashMap, HashSet};

use crate::ast::{
    AssignTarget, Block, Bound, BoundHead, Decl, Expr, ForInit, GenericParam, ImportDecl,
    ImportTree, Param, PathRoot, Program, Span, Stmt, TypeAliasDecl, TypeExpr, Visibility,
    WhereClause,
};
use crate::error::{MetelError, TypeErrorCode};
use crate::module_loader::{LoadedModule, ModuleGraph};
use crate::module_paths::resolve_path_root;
use crate::name_resolver::canonical_path;

type ModKey = Vec<String>;
type AliasKey = (ModKey, String);

/// A type alias as written, before its target has been expanded.
struct RawAlias {
    params: Vec<String>,
    target: TypeExpr,
    span: Span,
    is_pub: bool,
}

/// A type alias whose target is fully expanded — no remaining alias references.
#[derive(Clone)]
struct Alias {
    params: Vec<String>,
    target: TypeExpr,
    span: Span,
}

/// Which external alias names a module can see, and from where.
struct ImportScope {
    /// local name → `(source module, source name)`
    items: HashMap<String, AliasKey>,
    /// modules brought in wholesale by `import m::*;`
    globs: Vec<ModKey>,
    /// alias names this module re-exposes with `export other::{A};` → the true
    /// declaring `(module, name)`. One level only, matching `name_resolver`.
    re_exports: HashMap<String, AliasKey>,
}

/// Expand every type alias in the graph, in place.
///
/// # Errors
/// `T0003` for a recursive alias (direct or chained) or a duplicate alias name;
/// `T0004` for a generic-argument arity mismatch on an alias use; `T0009` for a
/// reference to an alias that is private to another module.
pub fn expand(graph: &mut ModuleGraph) -> Result<(), MetelError> {
    // 1. Collect every module's *module-level* raw aliases, keyed by (module,
    //    name). Block-local aliases are collected lazily during the step-4 walk.
    let mut raw: HashMap<ModKey, HashMap<String, RawAlias>> = HashMap::new();
    for m in &graph.modules {
        let mut per = HashMap::new();
        collect_aliases(&m.program, &mut per)?;
        if !per.is_empty() {
            raw.insert(m.module_path.clone(), per);
        }
    }

    let known_modules: HashSet<ModKey> = graph
        .modules
        .iter()
        .map(|m| m.module_path.clone())
        .collect();

    // 2. Per-module import scope — which external alias names are in view.
    let mut import_scopes: HashMap<ModKey, ImportScope> = HashMap::new();
    for m in &graph.modules {
        import_scopes.insert(
            m.module_path.clone(),
            module_import_scope(m, &known_modules, &graph.path_aliases, &raw),
        );
    }

    // 3. Fully resolve every alias's target (cross-module, cycle-checked).
    let mut resolved: HashMap<AliasKey, Alias> = HashMap::new();
    for (mk, per) in &raw {
        for name in per.keys() {
            let key = (mk.clone(), name.clone());
            if !resolved.contains_key(&key) {
                let mut chain = HashSet::new();
                resolve_alias(&key, &raw, &import_scopes, &mut chain, &mut resolved)?;
            }
        }
    }

    // 4. Rewrite every type expression in every module, drop the alias decls,
    //    and drop the now-dangling `import` / `export` leaves that named an
    //    erased alias.
    let path_aliases = graph.path_aliases.clone();
    for m in &mut graph.modules {
        let mut ex = Expander {
            current: m.module_path.clone(),
            scopes: Vec::new(),
            raw: &raw,
            import_scopes: &import_scopes,
            resolved: &resolved,
        };
        ex.walk_program(&mut m.program)?;
        prune_erased_alias_paths(
            &mut m.program,
            &m.module_path,
            &raw,
            &import_scopes,
            &path_aliases,
        );
    }
    Ok(())
}

/// Remove `import` / `export` tree leaves that named a type alias — the alias
/// declaration is gone, so the path would otherwise fail downstream as an
/// unknown item (or, for an `export`, a `T0009` re-export of a vanished name).
/// The local binding was already recorded in the module's [`ImportScope`] during
/// step 2, so alias expansion still works; this only tidies the AST.
fn prune_erased_alias_paths(
    program: &mut Program,
    module_path: &ModKey,
    raw: &HashMap<ModKey, HashMap<String, RawAlias>>,
    import_scopes: &HashMap<ModKey, ImportScope>,
    path_aliases: &HashMap<ModKey, ModKey>,
) {
    program.imports.retain_mut(|imp: &mut ImportDecl| {
        let base = resolve_path_root(&imp.path.root, module_path);
        !prune_alias_tree(&mut imp.path.tree, &base, raw, import_scopes, path_aliases)
    });
    program.exports.retain_mut(|exp| {
        let base = resolve_path_root(&exp.path.root, module_path);
        !prune_alias_tree(&mut exp.path.tree, &base, raw, import_scopes, path_aliases)
    });
}

/// Returns `true` if the whole subtree resolved only to erased aliases and
/// should be removed. A leaf counts as erased when it names a **public** alias
/// directly or through one `export` hop; a private-alias leaf is left in place
/// so `name_resolver` still raises its own `T0009`.
fn prune_alias_tree(
    tree: &mut ImportTree,
    base: &[String],
    raw: &HashMap<ModKey, HashMap<String, RawAlias>>,
    import_scopes: &HashMap<ModKey, ImportScope>,
    path_aliases: &HashMap<ModKey, ModKey>,
) -> bool {
    let canon = canonical_path(base, path_aliases);
    match tree {
        ImportTree::Glob => false,
        ImportTree::Name { name, .. } => resolve_in_module(&canon, name, raw, import_scopes)
            .is_some_and(|key| pub_alias(raw, &key)),
        ImportTree::Path { name, tree } => {
            let mut nested = canon.clone();
            nested.push(name.clone());
            prune_alias_tree(tree, &nested, raw, import_scopes, path_aliases)
        }
        ImportTree::Group(items) => {
            items.retain_mut(|t| !prune_alias_tree(t, &canon, raw, import_scopes, path_aliases));
            items.is_empty()
        }
    }
}

// ── Collection ───────────────────────────────────────────────────────────────

fn collect_aliases(
    program: &Program,
    out: &mut HashMap<String, RawAlias>,
) -> Result<(), MetelError> {
    for decl in &program.decls {
        if let Decl::TypeAlias(ta) = decl {
            let def = RawAlias {
                params: ta.generics.iter().map(|g| g.name.clone()).collect(),
                target: ta.target.clone(),
                span: ta.span.clone(),
                is_pub: ta.visibility == Visibility::Public,
            };
            if out.insert(ta.name.clone(), def).is_some() {
                return Err(err_t0003(
                    format!(
                        "type alias `{}` is declared more than once in this module",
                        ta.name
                    ),
                    &ta.span,
                ));
            }
        }
    }
    Ok(())
}

fn module_import_scope(
    loaded: &LoadedModule,
    known_modules: &HashSet<ModKey>,
    path_aliases: &HashMap<ModKey, ModKey>,
    raw: &HashMap<ModKey, HashMap<String, RawAlias>>,
) -> ImportScope {
    let mut scope = ImportScope {
        items: HashMap::new(),
        globs: Vec::new(),
        re_exports: HashMap::new(),
    };
    for import in &loaded.program.imports {
        let base = resolve_path_root(&import.path.root, &loaded.module_path);
        collect_import_tree(
            &base,
            &import.path.tree,
            known_modules,
            path_aliases,
            &mut scope,
        );
    }
    for export in &loaded.program.exports {
        let base = resolve_path_root(&export.path.root, &loaded.module_path);
        collect_export_tree(&base, &export.path.tree, path_aliases, raw, &mut scope);
    }
    scope
}

/// Record each alias name an `export` re-exposes, mapped to its true declaring
/// `(module, name)`. Only `public` aliases are recorded — re-exporting a private
/// one is `name_resolver`'s `T0009` to raise.
fn collect_export_tree(
    base: &[String],
    tree: &ImportTree,
    path_aliases: &HashMap<ModKey, ModKey>,
    raw: &HashMap<ModKey, HashMap<String, RawAlias>>,
    scope: &mut ImportScope,
) {
    let canon = canonical_path(base, path_aliases);
    match tree {
        ImportTree::Glob => {
            if let Some(per) = raw.get(&canon) {
                for (name, a) in per {
                    if a.is_pub {
                        scope
                            .re_exports
                            .insert(name.clone(), (canon.clone(), name.clone()));
                    }
                }
            }
        }
        ImportTree::Name { name, alias } => {
            let is_pub = raw
                .get(&canon)
                .is_some_and(|per| per.get(name).is_some_and(|a| a.is_pub));
            if is_pub {
                let local = alias.clone().unwrap_or_else(|| name.clone());
                scope.re_exports.insert(local, (canon, name.clone()));
            }
        }
        ImportTree::Path { name, tree } => {
            let mut nested = canon.clone();
            nested.push(name.clone());
            collect_export_tree(&nested, tree, path_aliases, raw, scope);
        }
        ImportTree::Group(trees) => {
            for t in trees {
                collect_export_tree(&canon, t, path_aliases, raw, scope);
            }
        }
    }
}

fn collect_import_tree(
    base: &[String],
    tree: &ImportTree,
    known_modules: &HashSet<ModKey>,
    path_aliases: &HashMap<ModKey, ModKey>,
    scope: &mut ImportScope,
) {
    let base = canonical_path(base, path_aliases);
    match tree {
        ImportTree::Glob => scope.globs.push(base),
        ImportTree::Name { name, alias } => {
            let mut candidate = base.clone();
            candidate.push(name.clone());
            if known_modules.contains(&candidate) {
                return; // a module handle, not an item
            }
            let local = alias.clone().unwrap_or_else(|| name.clone());
            scope.items.insert(local, (base, name.clone()));
        }
        ImportTree::Path { name, tree } => {
            let mut nested = base.clone();
            nested.push(name.clone());
            collect_import_tree(&nested, tree, known_modules, path_aliases, scope);
        }
        ImportTree::Group(trees) => {
            for t in trees {
                collect_import_tree(&base, t, known_modules, path_aliases, scope);
            }
        }
    }
}

// ── Cross-module name resolution ─────────────────────────────────────────────

/// The `AliasKey` a type name refers to when seen inside module `home`, or
/// `None` if the name is not an alias at all. Visibility is *not* checked here.
fn resolve_alias_name(
    name: &str,
    home: &ModKey,
    raw: &HashMap<ModKey, HashMap<String, RawAlias>>,
    import_scopes: &HashMap<ModKey, ImportScope>,
) -> Option<AliasKey> {
    if name.contains("::") {
        let (module, item) = split_qualified(name, home)?;
        return resolve_in_module(&module, &item, raw, import_scopes);
    }
    if raw.get(home).is_some_and(|per| per.contains_key(name)) {
        return Some((home.clone(), name.to_string()));
    }
    let scope = import_scopes.get(home)?;
    if let Some((src_mod, src_name)) = scope.items.get(name) {
        if let Some(key) = resolve_in_module(src_mod, src_name, raw, import_scopes) {
            return Some(key);
        }
    }
    for g in &scope.globs {
        // A glob only brings in the target module's *public* names.
        if raw
            .get(g)
            .is_some_and(|per| per.get(name).is_some_and(|a| a.is_pub))
        {
            return Some((g.clone(), name.to_string()));
        }
        if let Some(real) = import_scopes.get(g).and_then(|s| s.re_exports.get(name)) {
            if pub_alias(raw, real) {
                return Some(real.clone());
            }
        }
    }
    None
}

/// `(module, item)` as an alias key when `module` declares that alias directly,
/// or re-exports it (one `export` hop). Visibility of a *directly* declared alias
/// is the caller's to check; a re-exported one is only followed if `public`.
fn resolve_in_module(
    module: &ModKey,
    item: &str,
    raw: &HashMap<ModKey, HashMap<String, RawAlias>>,
    import_scopes: &HashMap<ModKey, ImportScope>,
) -> Option<AliasKey> {
    if raw.get(module).is_some_and(|per| per.contains_key(item)) {
        return Some((module.clone(), item.to_string()));
    }
    let real = import_scopes.get(module)?.re_exports.get(item)?;
    pub_alias(raw, real).then(|| real.clone())
}

fn pub_alias(raw: &HashMap<ModKey, HashMap<String, RawAlias>>, key: &AliasKey) -> bool {
    raw.get(&key.0)
        .is_some_and(|per| per.get(&key.1).is_some_and(|a| a.is_pub))
}

/// Split a `::`-qualified type name into the module it names and the final
/// segment, resolving the path root relative to `current`.
fn split_qualified(name: &str, current: &ModKey) -> Option<AliasKey> {
    let segs: Vec<&str> = name.split("::").collect();
    if segs.len() < 2 {
        return None;
    }
    let root = match segs[0] {
        "root" => PathRoot::Root,
        "std" => PathRoot::Std,
        "self" => PathRoot::Self_,
        "super" => PathRoot::Super,
        other => PathRoot::Name(other.to_string()),
    };
    let mut base = resolve_path_root(&root, current);
    base.extend(segs[1..segs.len() - 1].iter().map(|s| (*s).to_string()));
    Some((base, segs[segs.len() - 1].to_string()))
}

// ── Global target resolution ────────────────────────────────────────────────

/// Fully expand an alias's target, memoising the result in `memo`.
fn resolve_alias(
    key: &AliasKey,
    raw: &HashMap<ModKey, HashMap<String, RawAlias>>,
    import_scopes: &HashMap<ModKey, ImportScope>,
    chain: &mut HashSet<AliasKey>,
    memo: &mut HashMap<AliasKey, Alias>,
) -> Result<Alias, MetelError> {
    if let Some(a) = memo.get(key) {
        return Ok(a.clone());
    }
    let (home, name) = key;
    let raw_alias = &raw[home][name];
    if !chain.insert(key.clone()) {
        return Err(err_t0003(
            format!(
                "recursive type alias `{name}` — a transparent alias must expand to a finite type; \
                 use a `struct` or `enum` for a genuinely recursive shape"
            ),
            &raw_alias.span,
        ));
    }
    let local: HashSet<&str> = raw_alias.params.iter().map(String::as_str).collect();
    let mut target = raw_alias.target.clone();
    expand_refs(&mut target, home, &local, raw, import_scopes, chain, memo)?;
    chain.remove(key);
    let alias = Alias {
        params: raw_alias.params.clone(),
        target,
        span: raw_alias.span.clone(),
    };
    memo.insert(key.clone(), alias.clone());
    Ok(alias)
}

/// Replace every alias reference inside `te` (which lives in module `home`).
/// `local` names are the enclosing alias's own generic parameters — left as-is.
fn expand_refs(
    te: &mut TypeExpr,
    home: &ModKey,
    local: &HashSet<&str>,
    raw: &HashMap<ModKey, HashMap<String, RawAlias>>,
    import_scopes: &HashMap<ModKey, ImportScope>,
    chain: &mut HashSet<AliasKey>,
    memo: &mut HashMap<AliasKey, Alias>,
) -> Result<(), MetelError> {
    for child in children_mut(te) {
        expand_refs(child, home, local, raw, import_scopes, chain, memo)?;
    }
    let TypeExpr::Named(name, args) = te else {
        return Ok(());
    };
    if local.contains(name.as_str()) {
        return Ok(());
    }
    let Some(key) = resolve_alias_name(name, home, raw, import_scopes) else {
        return Ok(());
    };
    if &key.0 != home && !raw[&key.0][&key.1].is_pub {
        return Err(err_t0009(&key, raw));
    }
    let alias = resolve_alias(&key, raw, import_scopes, chain, memo)?;
    check_arity(&key.1, alias.params.len(), args.len(), &alias.span)?;
    let subst = zip_params(alias.params.iter().map(String::as_str), args);
    *te = subst_params(&alias.target, &subst);
    Ok(())
}

// ── Per-module rewrite ───────────────────────────────────────────────────────

struct Expander<'a> {
    current: ModKey,
    /// block-local alias frames, innermost last; targets already fully expanded
    scopes: Vec<HashMap<String, Alias>>,
    raw: &'a HashMap<ModKey, HashMap<String, RawAlias>>,
    import_scopes: &'a HashMap<ModKey, ImportScope>,
    resolved: &'a HashMap<AliasKey, Alias>,
}

impl Expander<'_> {
    fn local_lookup(&self, name: &str) -> Option<Alias> {
        self.scopes.iter().rev().find_map(|f| f.get(name).cloned())
    }

    /// Resolve a type name to its fully-expanded alias, or `None` if the name is
    /// not an alias. Errors only for a reference to another module's private
    /// alias.
    fn resolve_named(&self, name: &str) -> Result<Option<Alias>, MetelError> {
        if let Some(a) = self.local_lookup(name) {
            return Ok(Some(a));
        }
        let Some(key) = resolve_alias_name(name, &self.current, self.raw, self.import_scopes)
        else {
            return Ok(None);
        };
        if key.0 != self.current && !self.raw[&key.0][&key.1].is_pub {
            return Err(err_t0009(&key, self.raw));
        }
        Ok(self.resolved.get(&key).cloned())
    }

    /// Substitute alias references throughout a single type expression.
    fn subst_type(&self, te: &mut TypeExpr) -> Result<(), MetelError> {
        for child in children_mut(te) {
            self.subst_type(child)?;
        }
        let TypeExpr::Named(name, args) = te else {
            return Ok(());
        };
        let Some(alias) = self.resolve_named(name)? else {
            return Ok(());
        };
        check_arity(name, alias.params.len(), args.len(), &alias.span)?;
        let subst = zip_params(alias.params.iter().map(String::as_str), args);
        *te = subst_params(&alias.target, &subst);
        Ok(())
    }

    /// Rewrite the leading segment of a value / pattern path (`P { … }`, `P.{ … }`,
    /// `P::Variant`, a `P { … }` match arm) when `P` is an alias for a plain named
    /// type. A parameterised alias, or one whose target is a tuple / function /
    /// reference type, is left untouched — it is meaningless in value position and
    /// the later passes will say so.
    fn rewrite_value_path(&self, segs: &mut Vec<String>) -> Result<(), MetelError> {
        let Some(head) = segs.first() else {
            return Ok(());
        };
        let Some(alias) = self.resolve_named(head)? else {
            return Ok(());
        };
        if !alias.params.is_empty() {
            return Ok(());
        }
        let TypeExpr::Named(real, real_args) = &alias.target else {
            return Ok(());
        };
        if !real_args.is_empty() {
            return Ok(());
        }
        let rest = segs.split_off(1);
        *segs = real.split("::").map(str::to_string).collect();
        segs.extend(rest);
        Ok(())
    }

    fn walk_pattern(&self, pat: &mut crate::ast::Pattern) -> Result<(), MetelError> {
        use crate::ast::Pattern;
        match pat {
            Pattern::EnumVariant { path, .. } => self.rewrite_value_path(path)?,
            Pattern::Tuple(elems, _) | Pattern::Array { elems, .. } => {
                for p in elems {
                    self.walk_pattern(p)?;
                }
            }
            Pattern::Wildcard(_)
            | Pattern::Literal(..)
            | Pattern::Binding(..)
            | Pattern::Struct { .. }
            | Pattern::Record { .. } => {}
        }
        Ok(())
    }

    // -- declarations --

    fn walk_program(&mut self, program: &mut Program) -> Result<(), MetelError> {
        for decl in &mut program.decls {
            self.walk_decl(decl)?;
        }
        program.decls.retain(|d| !matches!(d, Decl::TypeAlias(_)));
        Ok(())
    }

    fn walk_decl(&mut self, decl: &mut Decl) -> Result<(), MetelError> {
        match decl {
            Decl::TypeAlias(_) => {}
            Decl::Fun(fd) => {
                self.walk_generics(&mut fd.generics)?;
                if let Some(wc) = &mut fd.where_clause {
                    self.walk_where(wc)?;
                }
                self.walk_params(&mut fd.params)?;
                if let Some(rt) = &mut fd.return_type {
                    self.subst_type(rt)?;
                }
                self.walk_block(&mut fd.body)?;
            }
            Decl::Struct(sd) => {
                self.walk_generics(&mut sd.generics)?;
                if let Some(wc) = &mut sd.where_clause {
                    self.walk_where(wc)?;
                }
                for f in &mut sd.fields {
                    self.subst_type(&mut f.type_ann)?;
                }
            }
            Decl::Enum(ed) => {
                self.walk_generics(&mut ed.generics)?;
                if let Some(wc) = &mut ed.where_clause {
                    self.walk_where(wc)?;
                }
                for v in &mut ed.variants {
                    for f in &mut v.fields {
                        self.subst_type(&mut f.type_ann)?;
                    }
                }
            }
            Decl::Impl(ib) => {
                self.walk_generics(&mut ib.generics)?;
                self.subst_type(&mut ib.target_type)?;
                for a in &mut ib.aspect_type_args {
                    self.subst_type(a)?;
                }
                for atd in &mut ib.assoc_type_defs {
                    self.subst_type(&mut atd.ty)?;
                }
                if let Some(wc) = &mut ib.where_clause {
                    self.walk_where(wc)?;
                }
                for m in &mut ib.methods {
                    self.walk_generics(&mut m.generics)?;
                    if let Some(wc) = &mut m.where_clause {
                        self.walk_where(wc)?;
                    }
                    self.walk_params(&mut m.params)?;
                    if let Some(rt) = &mut m.return_type {
                        self.subst_type(rt)?;
                    }
                    self.walk_block(&mut m.body)?;
                }
            }
            Decl::Aspect(ad) => {
                for m in &mut ad.methods {
                    self.walk_generics(&mut m.generics)?;
                    self.walk_params(&mut m.params)?;
                    if let Some(rt) = &mut m.return_type {
                        self.subst_type(rt)?;
                    }
                    if let Some(body) = &mut m.default_body {
                        self.walk_block(body)?;
                    }
                }
            }
            Decl::Let(ld) => {
                if let Some(t) = &mut ld.type_ann {
                    self.subst_type(t)?;
                }
                self.walk_expr(&mut ld.value)?;
            }
            Decl::Mut(md) => {
                if let Some(t) = &mut md.type_ann {
                    self.subst_type(t)?;
                }
                self.walk_expr(&mut md.value)?;
            }
            Decl::Stmt(s) => self.walk_stmt(s)?,
        }
        Ok(())
    }

    fn walk_params(&self, params: &mut [Param]) -> Result<(), MetelError> {
        for p in params {
            if let Some(t) = &mut p.type_ann {
                self.subst_type(t)?;
            }
        }
        Ok(())
    }

    fn walk_generics(&self, generics: &mut [GenericParam]) -> Result<(), MetelError> {
        for g in generics {
            for b in &mut g.bounds {
                self.walk_bound(b)?;
            }
        }
        Ok(())
    }

    fn walk_where(&self, wc: &mut WhereClause) -> Result<(), MetelError> {
        for c in &mut wc.constraints {
            for b in &mut c.bounds {
                self.walk_bound(b)?;
            }
        }
        Ok(())
    }

    fn walk_bound(&self, b: &mut Bound) -> Result<(), MetelError> {
        match &mut b.head {
            BoundHead::Aspect(te) => self.subst_type(te)?,
            BoundHead::Row(row) => {
                for f in &mut row.fields {
                    if let Some(t) = &mut f.ty {
                        self.subst_type(t)?;
                    }
                }
            }
        }
        for (_, te) in &mut b.assoc_bindings {
            self.subst_type(te)?;
        }
        Ok(())
    }

    // -- blocks & block-local aliases --

    fn walk_block(&mut self, block: &mut Block) -> Result<(), MetelError> {
        let frame = self.collect_local_frame(block)?;
        self.scopes.push(frame);
        for decl in &mut block.stmts {
            self.walk_decl(decl)?;
        }
        if let Some(tail) = &mut block.tail {
            self.walk_expr(tail)?;
        }
        self.scopes.pop();
        block.stmts.retain(|d| !matches!(d, Decl::TypeAlias(_)));
        Ok(())
    }

    /// Resolve this block's own `type` declarations against the enclosing
    /// environment (outer frames + module / import scope) plus each other.
    fn collect_local_frame(&self, block: &Block) -> Result<HashMap<String, Alias>, MetelError> {
        let mut siblings: HashMap<String, &TypeAliasDecl> = HashMap::new();
        for decl in &block.stmts {
            if let Decl::TypeAlias(ta) = decl {
                if siblings.insert(ta.name.clone(), ta).is_some() {
                    return Err(err_t0003(
                        format!(
                            "type alias `{}` is declared more than once in this block",
                            ta.name
                        ),
                        &ta.span,
                    ));
                }
            }
        }
        if siblings.is_empty() {
            return Ok(HashMap::new());
        }
        let mut frame = HashMap::new();
        for (name, ta) in &siblings {
            let mut chain = HashSet::new();
            let target = self.resolve_local_target(ta, &siblings, &mut chain)?;
            frame.insert(
                name.clone(),
                Alias {
                    params: ta.generics.iter().map(|g| g.name.clone()).collect(),
                    target,
                    span: ta.span.clone(),
                },
            );
        }
        Ok(frame)
    }

    fn resolve_local_target(
        &self,
        ta: &TypeAliasDecl,
        siblings: &HashMap<String, &TypeAliasDecl>,
        chain: &mut HashSet<String>,
    ) -> Result<TypeExpr, MetelError> {
        if !chain.insert(ta.name.clone()) {
            return Err(err_t0003(
                format!(
                    "recursive type alias `{}` — a transparent alias must expand to a finite type; \
                     use a `struct` or `enum` for a genuinely recursive shape",
                    ta.name
                ),
                &ta.span,
            ));
        }
        let local_params: HashSet<&str> = ta.generics.iter().map(|g| g.name.as_str()).collect();
        let mut target = ta.target.clone();
        self.expand_local_refs(&mut target, &local_params, siblings, chain)?;
        chain.remove(&ta.name);
        Ok(target)
    }

    fn expand_local_refs(
        &self,
        te: &mut TypeExpr,
        local_params: &HashSet<&str>,
        siblings: &HashMap<String, &TypeAliasDecl>,
        chain: &mut HashSet<String>,
    ) -> Result<(), MetelError> {
        for child in children_mut(te) {
            self.expand_local_refs(child, local_params, siblings, chain)?;
        }
        let TypeExpr::Named(name, args) = te else {
            return Ok(());
        };
        if local_params.contains(name.as_str()) {
            return Ok(());
        }
        if let Some(sib) = siblings.get(name.as_str()) {
            let body = self.resolve_local_target(sib, siblings, chain)?;
            check_arity(name, sib.generics.len(), args.len(), &sib.span)?;
            let params: Vec<&str> = sib.generics.iter().map(|g| g.name.as_str()).collect();
            let subst = zip_params(params.iter().copied(), args);
            *te = subst_params(&body, &subst);
            return Ok(());
        }
        if let Some(alias) = self.resolve_named(name)? {
            check_arity(name, alias.params.len(), args.len(), &alias.span)?;
            let subst = zip_params(alias.params.iter().map(String::as_str), args);
            *te = subst_params(&alias.target, &subst);
        }
        Ok(())
    }

    // -- statements & expressions --

    fn walk_stmt(&mut self, stmt: &mut Stmt) -> Result<(), MetelError> {
        match stmt {
            Stmt::Expr(e) => self.walk_expr(e)?,
            Stmt::While(w) => {
                self.walk_expr(&mut w.condition)?;
                self.walk_block(&mut w.body)?;
            }
            Stmt::For(f) => {
                if let Some(init) = &mut f.init {
                    match init {
                        ForInit::Expr(e) => self.walk_expr(e)?,
                        ForInit::Let(ld) => {
                            if let Some(t) = &mut ld.type_ann {
                                self.subst_type(t)?;
                            }
                            self.walk_expr(&mut ld.value)?;
                        }
                        ForInit::Mut(md) => {
                            if let Some(t) = &mut md.type_ann {
                                self.subst_type(t)?;
                            }
                            self.walk_expr(&mut md.value)?;
                        }
                    }
                }
                if let Some(c) = &mut f.condition {
                    self.walk_expr(c)?;
                }
                if let Some(s) = &mut f.step {
                    self.walk_expr(s)?;
                }
                self.walk_block(&mut f.body)?;
            }
            Stmt::ForIn(fi) => {
                self.walk_expr(&mut fi.iterable)?;
                self.walk_block(&mut fi.body)?;
            }
        }
        Ok(())
    }

    // clippy-allow: one exhaustive `Expr` dispatch table; splitting it scatters
    // the traversal with no clarity gain (mirrors `path_normalizer::normalize_expr`).
    #[allow(clippy::too_many_lines)]
    fn walk_expr(&mut self, expr: &mut Expr) -> Result<(), MetelError> {
        match expr {
            Expr::Literal(..) | Expr::Ident(..) | Expr::ResolvedPath { .. } | Expr::Continue(_) => {
            }
            // A value path (`E::Variant`, `Alias::assoc()`) or a record
            // projection (`P.{ f }`) may lead with a type-alias name.
            Expr::Path(segs, _, _) => self.rewrite_value_path(segs)?,
            Expr::RecordProjection { path, .. } => self.rewrite_value_path(path)?,
            Expr::Tuple(elems, _) | Expr::Array(elems, _) => {
                for e in elems {
                    self.walk_expr(e)?;
                }
            }
            Expr::RecordLiteral { fields, .. } => {
                for (_, e) in fields {
                    self.walk_expr(e)?;
                }
            }
            Expr::StructLiteral { path, fields, .. } => {
                self.rewrite_value_path(path)?;
                for (_, e) in fields {
                    self.walk_expr(e)?;
                }
            }
            Expr::RepeatArray(e, _, _) | Expr::UnaryOp(_, e, _) => self.walk_expr(e)?,
            Expr::BinOp(l, _, r, _) => {
                self.walk_expr(l)?;
                self.walk_expr(r)?;
            }
            Expr::Assign { target, value, .. } => {
                self.walk_assign_target(target)?;
                self.walk_expr(value)?;
            }
            Expr::Call {
                callee,
                type_args,
                args,
                ..
            }
            | Expr::MethodCall {
                receiver: callee,
                type_args,
                args,
                ..
            } => {
                self.walk_expr(callee)?;
                for t in type_args {
                    self.subst_type(t)?;
                }
                for a in args {
                    self.walk_expr(a)?;
                }
            }
            Expr::FieldAccess { object, .. } | Expr::TupleAccess { object, .. } => {
                self.walk_expr(object)?;
            }
            Expr::PropagateError { expr, .. } => self.walk_expr(expr)?,
            Expr::Index { object, index, .. } => {
                self.walk_expr(object)?;
                self.walk_expr(index)?;
            }
            Expr::Cast {
                expr: inner,
                target_type,
                ..
            } => {
                self.walk_expr(inner)?;
                self.subst_type(target_type)?;
            }
            Expr::Ascribe {
                expr: inner, ann, ..
            } => {
                self.walk_expr(inner)?;
                self.subst_type(ann)?;
            }
            Expr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                self.walk_expr(condition)?;
                self.walk_block(then_branch)?;
                if let Some(eb) = else_branch {
                    self.walk_block(eb)?;
                }
            }
            Expr::Loop { body, .. } => self.walk_block(body)?,
            Expr::Closure {
                params,
                return_type,
                body,
                ..
            } => {
                self.walk_params(params)?;
                if let Some(rt) = return_type {
                    self.subst_type(rt)?;
                }
                self.walk_block(body)?;
            }
            Expr::Match(m) => {
                self.walk_expr(&mut m.scrutinee)?;
                for arm in &mut m.arms {
                    self.walk_pattern(&mut arm.pattern)?;
                    if let Some(g) = &mut arm.guard {
                        self.walk_expr(g)?;
                    }
                    self.walk_block(&mut arm.body)?;
                }
            }
            Expr::Return(r) => {
                if let Some(v) = &mut r.value {
                    self.walk_expr(v)?;
                }
            }
            Expr::Break(b) => {
                if let Some(v) = &mut b.value {
                    self.walk_expr(v)?;
                }
            }
        }
        Ok(())
    }

    fn walk_assign_target(&mut self, target: &mut AssignTarget) -> Result<(), MetelError> {
        match target {
            AssignTarget::Ident(..) => {}
            AssignTarget::FieldAccess { object, .. }
            | AssignTarget::TupleAccess { object, .. }
            | AssignTarget::Deref { object, .. } => self.walk_expr(object)?,
            AssignTarget::Index { object, index, .. } => {
                self.walk_expr(object)?;
                self.walk_expr(index)?;
            }
        }
        Ok(())
    }
}

// ── Shared helpers ───────────────────────────────────────────────────────────

fn zip_params<'t>(
    params: impl IntoIterator<Item = &'t str>,
    args: &'t [TypeExpr],
) -> HashMap<&'t str, &'t TypeExpr> {
    params.into_iter().zip(args.iter()).collect()
}

/// A copy of `body` with every bare `Named(param, [])` replaced by its bound type.
fn subst_params(body: &TypeExpr, subst: &HashMap<&str, &TypeExpr>) -> TypeExpr {
    let mut out = body.clone();
    subst_params_in_place(&mut out, subst);
    out
}

fn subst_params_in_place(te: &mut TypeExpr, subst: &HashMap<&str, &TypeExpr>) {
    if let TypeExpr::Named(name, args) = te {
        if args.is_empty() {
            if let Some(replacement) = subst.get(name.as_str()) {
                *te = (*replacement).clone();
                return;
            }
        }
    }
    for child in children_mut(te) {
        subst_params_in_place(child, subst);
    }
}

/// Mutable references to the directly-nested `TypeExpr` children of `te`
/// (including a `Named`'s type arguments).
fn children_mut(te: &mut TypeExpr) -> Vec<&mut TypeExpr> {
    match te {
        TypeExpr::Named(_, args) | TypeExpr::Tuple(args) => args.iter_mut().collect(),
        TypeExpr::Record(fields) => fields.iter_mut().map(|(_, t)| t).collect(),
        TypeExpr::Array(inner)
        | TypeExpr::SizedArray(inner, _)
        | TypeExpr::Reference(inner)
        | TypeExpr::MutReference(inner)
        | TypeExpr::ImplAspect { bound: inner, .. }
        | TypeExpr::DynAspect { bound: inner, .. }
        | TypeExpr::Projection { base: inner, .. } => vec![inner.as_mut()],
        TypeExpr::Fun {
            params,
            return_type,
            ..
        } => {
            let mut v: Vec<&mut TypeExpr> = params.iter_mut().collect();
            if let Some(rt) = return_type {
                v.push(rt.as_mut());
            }
            v
        }
        TypeExpr::Unit | TypeExpr::RecordProjection { .. } => vec![],
    }
}

fn check_arity(name: &str, want: usize, got: usize, span: &Span) -> Result<(), MetelError> {
    if want == got {
        Ok(())
    } else {
        Err(MetelError::type_error(
            TypeErrorCode::T0004,
            format!("type alias `{name}` takes {want} type argument(s), but {got} were supplied"),
            span,
        ))
    }
}

fn err_t0003(msg: String, span: &Span) -> MetelError {
    MetelError::type_error(TypeErrorCode::T0003, msg, span)
}

fn err_t0009(key: &AliasKey, raw: &HashMap<ModKey, HashMap<String, RawAlias>>) -> MetelError {
    MetelError::type_error(
        TypeErrorCode::T0009,
        format!(
            "type alias `{}` is private to module `{}`",
            key.1,
            key.0.join("::")
        ),
        &raw[&key.0][&key.1].span,
    )
}
