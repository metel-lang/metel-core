use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::data::ast::{Decl, ImportTree, PathRoot, Span, TypeExpr, Visibility};
use crate::data::error::{MetelError, TypeErrorCode};
use crate::identity::symbols::SymbolId;
use crate::pipeline::parsing::module_loader::{LoadedModule, ModuleGraph};

// ── Public types ──────────────────────────────────────────────────────────────

/// Priority tier for glob imports.
/// Higher tiers win over lower tiers without a conflict error.
/// T0011 fires only when two globs of the **same** tier export the same name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GlobTier {
    /// Auto-inserted by the runtime (e.g. `std::core`). Lowest priority.
    Std,
    /// Explicit `import module::*` in user source. Wins over `Std` silently.
    User,
}

/// A single resolved import binding within a module's scope.
#[derive(Debug, Clone)]
pub struct ImportBinding {
    /// Canonical module path of the module that provides this name.
    pub source_module: Vec<String>,
    /// The name as declared in the source module.
    pub source_name: String,
    pub kind: BindingKind,
    /// Stable identity for the `(source_module, source_name)` declaration.
    /// Two bindings with the same `symbol_id` refer to the same declaration,
    /// regardless of local alias or path spelling.
    pub symbol_id: SymbolId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BindingKind {
    /// A specific item (type, function, constant, …).
    Item,
    /// A whole module imported as a handle (`import std::math;` → `math::sin()`).
    Module,
}

/// The resolved import scope for a single module.
#[derive(Debug, Clone)]
pub struct ModuleScope {
    /// Explicit bindings: `local_name` → `ImportBinding`.
    /// Two explicit bindings with the same `local_name` are a compile error.
    pub explicit: HashMap<String, ImportBinding>,
    /// Glob-imported module paths (`import path::*`), tagged with their priority tier.
    /// Names from these modules are in scope at lower priority than explicit imports.
    /// T0011 fires only for same-tier conflicts; `User` silently wins over `Std`.
    pub globs: Vec<(GlobTier, Vec<String>)>,
    /// Re-exported names: `local_name` → source binding.
    /// These names are part of this module's public API surface for callers.
    pub re_exports: HashMap<String, ImportBinding>,
}

/// The output of the name resolution pass: one scope per loaded module.
#[derive(Debug, Clone)]
pub struct ResolvedNames {
    pub scopes: HashMap<Vec<String>, ModuleScope>,
    /// Combined public surface per module: local declarations + re-exports.
    /// Used by callers to check import visibility.
    pub pub_surface: HashMap<Vec<String>, HashSet<String>>,
    /// All top-level declared names per module, regardless of visibility.
    /// Used by the typechecker to distinguish T0009 (private) from T0003 (absent).
    pub declared_names: HashMap<Vec<String>, HashSet<String>>,
    /// Canonical symbol table: `(source_module, source_name)` → stable `SymbolId`.
    /// Every `ImportBinding` carries an id drawn from this table; two bindings with the
    /// same id refer to the same declaration.
    pub symbols: HashMap<(Vec<String>, String), SymbolId>,
    /// Maps each top-level declared `SymbolId` to the span of its declaration.
    /// Used by diagnostics and tooling (e.g. LSP goto-definition) to locate the
    /// definition site of any resolved symbol. See RFC-0059.
    pub definitions: HashMap<SymbolId, Span>,
    /// Resolved bare-`Ident` references: reference-site span → referent `SymbolId`.
    /// Populated by the reference resolver (METEL-187 / ADR-0041). A reference whose
    /// span is absent is a true local (or unresolved). Multi-segment paths are not
    /// recorded here — they carry their `symbol_id` on `Expr::ResolvedPath` after
    /// path normalization.
    pub references: crate::pipeline::name_resolution::reference_resolver::ReferenceTable,
}

// ── Symbol interning ──────────────────────────────────────────────────────────

// The interning table is `crate::identity::symbols::SymbolTable`, which pre-seeds the builtin
// `std::core` types and aspects with their well-known `SYM_*` ids and allocates
// user declarations from `USER_SYM_START`. Using it here (rather than a private
// counter from 1) makes the `SYM_TYPE_*` / `SYM_ASPECT_*` constants the *actual*
// ids that flow through the pipeline, so runtime seeding can register builtin
// impls under those same ids. See METEL-185 / ADR-0041.
use crate::identity::symbols::SymbolTable;

// ── Path alias dereferencing ──────────────────────────────────────────────────

/// Resolve a module path to its canonical form by dereferencing any alias. See ADR-0031.
/// Handles prefix aliases: if `["a", "b"]` → `["x", "y"]`, then
/// `["a", "b", "c"]` → `["x", "y", "c"]`.
pub(crate) fn canonical_path(
    path: &[String],
    aliases: &HashMap<Vec<String>, Vec<String>>,
) -> Vec<String> {
    for len in (1..=path.len()).rev() {
        if let Some(prefix_canon) = aliases.get(&path[..len]) {
            let mut result = prefix_canon.clone();
            result.extend_from_slice(&path[len..]);
            return result;
        }
    }
    path.to_vec()
}

// ── Entry point ───────────────────────────────────────────────────────────────

/// Returns an `Rc` since every later pipeline stage (path normalization,
/// coherence, typechecking, elaboration) reads the same `ResolvedNames` --
/// wrapping it once here, at its one real construction site, lets each stage's
/// own graph type carry a cheap clone forward instead of a raw `&ResolvedNames`
/// side parameter reaching back to this pass (metel-core#1250).
///
/// # Errors
/// Returns an error if an import or export cannot be resolved (e.g. an unknown
/// module or name) or if a glob-import conflict cannot be settled.
pub fn resolve(graph: &ModuleGraph) -> Result<Rc<ResolvedNames>, MetelError> {
    let path_aliases = &graph.path_aliases;
    let known_modules: HashSet<Vec<String>> = graph
        .modules
        .iter()
        .map(|m| m.module_path.clone())
        .collect();

    // First pass: collect locally-declared names per module (public and all).
    let mut pub_surface: HashMap<Vec<String>, HashSet<String>> = graph
        .modules
        .iter()
        .map(|m| {
            let names = m.program.decls.iter().filter_map(decl_pub_name).collect();
            (m.module_path.clone(), names)
        })
        .collect();

    let declared_names: HashMap<Vec<String>, HashSet<String>> = graph
        .modules
        .iter()
        .map(|m| {
            let names = m.program.decls.iter().filter_map(decl_any_name).collect();
            (m.module_path.clone(), names)
        })
        .collect();

    // Names declared via more than one `fn` in the same module — overload sets. Purely
    // syntactic (arity/type-based selection happens later, in the typechecker); this
    // is only used to keep the reference resolver from treating an overloaded name as
    // an ordinary single-declaration reference (ADR-0042).
    let overloaded_names: HashMap<Vec<String>, HashSet<String>> = graph
        .modules
        .iter()
        .map(|m| {
            let mut counts: HashMap<&str, u32> = HashMap::new();
            for decl in &m.program.decls {
                if let Decl::Fun(d) = decl {
                    *counts.entry(d.name.as_str()).or_insert(0) += 1;
                }
            }
            let overloaded = counts
                .into_iter()
                .filter(|(_, count)| *count > 1)
                .map(|(name, _)| name.to_string())
                .collect();
            (m.module_path.clone(), overloaded)
        })
        .collect();

    // Assign SymbolIds to all top-level declarations in their home modules.
    // This ensures every declaration has a stable id even if it is never imported.
    // The intern call is idempotent, so import-site ids (assigned below) will match.
    // While interning, record each declaration's definition span (RFC-0059).
    // See `intern_all_symbols`'s own doc for why this is a sort-then-intern pass,
    // not a direct interning loop over `graph.modules`.
    let (mut sym, definitions) = intern_all_symbols(graph);

    // Second pass: process re-exports and extend pub_surface. Keep the full bindings
    // (not just the names) — an import of a re-exported name (third pass) must reuse
    // the re-export's own `symbol_id` (chased to its real source module), not mint a
    // fresh one under the re-exporting module's own path. Simple single-pass (no
    // support for transitive re-export chains — a re-export of a re-export; that's
    // future work, same as before).
    let mut all_re_exports: HashMap<Vec<String>, HashMap<String, ImportBinding>> = HashMap::new();
    for loaded in &graph.modules {
        let re_exported =
            collect_re_exports(loaded, &known_modules, &pub_surface, path_aliases, &mut sym)?;
        pub_surface
            .entry(loaded.module_path.clone())
            .or_default()
            .extend(re_exported.keys().cloned());
        all_re_exports.insert(loaded.module_path.clone(), re_exported);
    }

    // Third pass: resolve imports using the final pub_surface.
    let mut scopes = HashMap::new();
    for loaded in &graph.modules {
        let scope = resolve_module(
            loaded,
            &known_modules,
            &all_re_exports,
            path_aliases,
            &mut sym,
        )?;
        scopes.insert(loaded.module_path.clone(), scope);
    }

    // Fourth pass: resolve every bare-`Ident` reference to its declaration's SymbolId,
    // tracking lexical scopes so true locals stay name-keyed (METEL-187 / ADR-0041).
    let module_decls: Vec<(Vec<String>, &[Decl])> = graph
        .modules
        .iter()
        .map(|m| (m.module_path.clone(), m.program.decls.as_slice()))
        .collect();
    let references = crate::pipeline::name_resolution::reference_resolver::collect_references(
        &module_decls,
        &crate::pipeline::name_resolution::reference_resolver::ResolveInputs {
            scopes: &scopes,
            pub_surface: &pub_surface,
            declared_names: &declared_names,
            symbols: &sym.map,
            overloaded_names: &overloaded_names,
        },
    );

    Ok(Rc::new(ResolvedNames {
        scopes,
        pub_surface,
        declared_names,
        symbols: sym.map,
        definitions,
        references,
    }))
}

/// Build the canonical symbol-table name for an `impl`/`aspect` method (METEL-185).
///
/// These keys live in the same `(module, name)` symbol namespace as ordinary
/// declarations but are disambiguated by their `::`-joined shape so they never
/// collide with a plain declaration name:
///
/// - inherent impl method: `Target::method`
/// - aspect impl method:   `Target::Aspect::method`
/// - aspect-declared method (default/abstract): `Aspect::method`
///
/// Both the resolver (which assigns the id) and later consumers (which look it up)
/// must build keys through this function so the identities agree.
#[must_use]
// limit: ["LIMIT-NAME-RESOLUTION-005"]
pub fn method_symbol_name(target: &str, aspect: Option<&str>, method: &str) -> String {
    match aspect {
        Some(aspect) => format!("{target}::{aspect}::{method}"),
        None => format!("{target}::{method}"),
    }
}

/// Resolve `name` as *provided* by `module` — either declared there directly, or
/// re-exported from elsewhere via `export path::name;` (`ModuleScope::re_exports`).
///
/// A glob import (`import module::*;`) must see everything `module`'s own public
/// surface includes, and a re-export is as much a part of that surface as a local
/// declaration — `pub_surface` already counts it as visible (see its own doc), but
/// naming its `SymbolId` needs this extra hop through `module`'s own scope, since
/// `symbols` is keyed by where a name is *declared*, not everywhere it's *visible*.
/// Without it, a glob-imported re-export typechecks (visibility says it's there) but
/// resolves to no identity at all, which is silently indistinguishable from "not
/// actually bound" downstream (#668). Shared by every glob-resolution site — value
/// names in `reference_resolver`, type names in `TypeDefinitionRegistry` — since both
/// hit the exact same gap for the exact same reason.
#[must_use]
pub(crate) fn resolve_name_provided_by_module(
    module: &[String],
    name: &str,
    symbols: &HashMap<(Vec<String>, String), SymbolId>,
    scopes: &HashMap<Vec<String>, ModuleScope>,
) -> Option<SymbolId> {
    symbols
        .get(&(module.to_vec(), name.to_string()))
        .copied()
        .or_else(|| {
            scopes
                .get(module)
                .and_then(|s| s.re_exports.get(name))
                .map(|binding| binding.symbol_id)
        })
}

/// Extract the surface type name of an impl target (`extend Foo { … }` → `Foo`).
/// Returns `None` for non-named targets (which the typechecker rejects elsewhere).
fn impl_target_name(target: &TypeExpr) -> Option<&str> {
    match target {
        TypeExpr::Named(name, _) => Some(name.as_str()),
        // `extend<T> T[]: Aspect { ... }` — the structural array-pattern
        // target, keyed under a synthetic owner name (metel-core#1101).
        // This SymbolId is never surfaced for dispatch (impl methods still
        // carry no top-level identity, same as a named-type impl's own
        // methods — see `method_fun_decl`); it exists only so the identity
        // walk has a real owner to hash each method body's locals against,
        // instead of silently skipping these bodies the way it used to.
        //
        // Deliberately NOT the bare string "Array": that collided with a
        // literal `extend Array: Aspect { ... }` (a real, reachable nominal
        // impl target — Metel accepts `Array` as a type name in written-type
        // position, see `conversions.rs`'s `("Array", 1)` case), which
        // `TypeExpr::Named(name, _) => Some(name.as_str())` above also maps
        // to the identical string "Array" (metel-core#1121). `[]` can't
        // appear in a Metel identifier, so no `TypeExpr::Named` target can
        // ever collide with this one; `identity/allocate.rs`'s `Decl::Impl`
        // arm must keep computing this exact same string.
        TypeExpr::Array(_) => Some("[]Array"),
        _ => None,
    }
}

/// Assign `SymbolId`s to every top-level declaration and impl/aspect method
/// across `graph`, and record each one's definition span (RFC-0059).
///
/// ADR-0054's structural-allocation amendment requires the *numeric*
/// `SymbolId` to be deterministic for one resolved module graph "regardless
/// of file iteration order" (metel-core#1048) -- `SymbolTable::intern`'s
/// underlying counter is order-of-first-call dependent, so interning
/// directly in `graph.modules`'s own (load-order-dependent) sequence would
/// let two runs over the identical set of declarations hand out different
/// ids to the same declaration. This collects every `(module path, key)`
/// pair first, sorts canonically, and only then interns -- the resulting ids
/// depend on the *set* of declarations, not the order this function happened
/// to visit them in (metel-core#1129's own "verify empirically" repro:
/// reversing `graph.modules` and re-resolving used to change `SymbolId`s; a
/// regression test pins this).
// limit: ["LIMIT-NAME-RESOLUTION-005"]
fn intern_all_symbols(graph: &ModuleGraph) -> (SymbolTable, HashMap<SymbolId, Span>) {
    let mut pending: Vec<(Vec<String>, String, Option<Span>)> = Vec::new();
    for loaded in &graph.modules {
        for decl in &loaded.program.decls {
            if let Some(name) = decl_any_name(decl) {
                pending.push((loaded.module_path.clone(), name, decl_span(decl).cloned()));
            }
            // METEL-185 step 3a: give every impl/aspect method a stable SymbolId so
            // later passes can dispatch method selection by id rather than by name.
            collect_method_symbol_keys(decl, &loaded.module_path, &mut pending);
        }
    }
    pending.sort_by(|(am, an, _), (bm, bn, _)| am.cmp(bm).then_with(|| an.cmp(bn)));

    let mut sym = SymbolTable::new();
    let mut definitions: HashMap<SymbolId, Span> = HashMap::new();
    for (module_path, name, span) in pending {
        let id = sym.intern(&module_path, &name);
        if let Some(span) = span {
            definitions.entry(id).or_insert(span);
        }
    }
    (sym, definitions)
}

/// Collect the `(module path, key, span)` triples that will need a `SymbolId`
/// for every method declared in an `impl` or `aspect` declaration. No-op for
/// other declarations. See METEL-185.
///
/// Collection only -- interning happens in `intern_all_symbols`'s own
/// canonically-sorted pass, not here, so the id a method ends up with does
/// not depend on this declaration's position among its siblings.
fn collect_method_symbol_keys(
    decl: &Decl,
    module_path: &[String],
    out: &mut Vec<(Vec<String>, String, Option<Span>)>,
) {
    match decl {
        Decl::Impl(ib) => {
            let Some(target) = impl_target_name(&ib.target_type) else {
                return;
            };
            for method in &ib.methods {
                let key = method_symbol_name(target, ib.aspect_name.as_deref(), &method.name);
                out.push((module_path.to_vec(), key, Some(method.span.clone())));
            }
        }
        Decl::Aspect(ad) => {
            for method in &ad.methods {
                let key = method_symbol_name(&ad.name, None, &method.name);
                out.push((module_path.to_vec(), key, Some(method.span.clone())));
            }
        }
        _ => {}
    }
}

/// Returns the declaration span for a named top-level declaration, if it has one.
/// Used to populate the [`ResolvedNames::definitions`] index (RFC-0059).
fn decl_span(decl: &Decl) -> Option<&Span> {
    match decl {
        Decl::Fun(d) => Some(&d.span),
        Decl::Struct(d) => Some(&d.span),
        Decl::Enum(d) => Some(&d.span),
        Decl::Aspect(d) => Some(&d.span),
        Decl::Let(d) => Some(&d.span),
        Decl::Mut(d) => Some(&d.span),
        Decl::TypeAlias(d) => Some(&d.span),
        Decl::Impl(_) | Decl::Stmt(_) => None,
    }
}

/// Returns the name of a declaration if it is public.
fn decl_pub_name(decl: &Decl) -> Option<String> {
    match decl {
        Decl::Fun(d) if d.visibility == Visibility::Public => Some(d.name.clone()),
        Decl::Struct(d) if d.visibility == Visibility::Public => Some(d.name.clone()),
        Decl::Enum(d) if d.visibility == Visibility::Public => Some(d.name.clone()),
        Decl::Aspect(d) if d.visibility == Visibility::Public => Some(d.name.clone()),
        _ => None,
    }
}

/// Returns the name of a declaration regardless of visibility.
// limit: ["LIMIT-NAME-RESOLUTION-005"]
fn decl_any_name(decl: &Decl) -> Option<String> {
    match decl {
        Decl::Fun(d) => Some(d.name.clone()),
        Decl::Struct(d) => Some(d.name.clone()),
        Decl::Enum(d) => Some(d.name.clone()),
        Decl::Aspect(d) => Some(d.name.clone()),
        Decl::Let(d) => Some(d.name.clone()),
        Decl::Mut(d) => Some(d.name.clone()),
        Decl::TypeAlias(d) => Some(d.name.clone()),
        Decl::Impl(_) | Decl::Stmt(_) => None,
    }
}

// ── Per-module resolution ─────────────────────────────────────────────────────

// arch-implements: ["arch.name-resolution.requirement-2"]
fn resolve_module(
    loaded: &LoadedModule,
    known_modules: &HashSet<Vec<String>>,
    all_re_exports: &HashMap<Vec<String>, HashMap<String, ImportBinding>>,
    path_aliases: &HashMap<Vec<String>, Vec<String>>,
    sym: &mut SymbolTable,
) -> Result<ModuleScope, MetelError> {
    // Reuse this module's own re-exports (already computed in `resolve`'s second
    // pass) rather than recomputing them — same result, one fewer pass over the
    // export tree.
    let re_exports = all_re_exports
        .get(&loaded.module_path)
        .cloned()
        .unwrap_or_default();
    let mut scope = ModuleScope {
        explicit: HashMap::new(),
        globs: Vec::new(),
        re_exports,
    };

    for import in &loaded.program.imports {
        let base = absolute_base(&import.path.root, &loaded.module_path);
        process_tree(
            &base,
            &import.path.tree,
            known_modules,
            all_re_exports,
            path_aliases,
            &mut scope,
            &import.span,
            sym,
        )?;
    }

    // Auto-import std::core at lowest (Std) priority — RFC-0030. See ADR-0026 (glob tiers)
    // and ADR-0027 (virtual module). Every module sees core names without an explicit import.
    scope
        .globs
        .push((GlobTier::Std, vec!["std".to_string(), "core".to_string()]));

    Ok(scope)
}

/// Collect re-exported names from a module's `export` declarations.
/// Returns a map of `local_name` → binding for each successfully resolved export.
fn collect_re_exports(
    loaded: &LoadedModule,
    known_modules: &HashSet<Vec<String>>,
    pub_surface: &HashMap<Vec<String>, HashSet<String>>,
    path_aliases: &HashMap<Vec<String>, Vec<String>>,
    sym: &mut SymbolTable,
) -> Result<HashMap<String, ImportBinding>, MetelError> {
    let mut re_exports: HashMap<String, ImportBinding> = HashMap::new();

    for export in &loaded.program.exports {
        let base = absolute_base(&export.path.root, &loaded.module_path);
        process_export_tree(
            &base,
            &export.path.tree,
            known_modules,
            pub_surface,
            path_aliases,
            &mut re_exports,
            &export.span,
            sym,
        )?;
    }

    Ok(re_exports)
}

/// Walk an export path tree and populate the `re_exports` map.
#[allow(clippy::too_many_arguments)] // recursive walker threading full resolution context
fn process_export_tree(
    base: &[String],
    tree: &ImportTree,
    known_modules: &HashSet<Vec<String>>,
    pub_surface: &HashMap<Vec<String>, HashSet<String>>,
    path_aliases: &HashMap<Vec<String>, Vec<String>>,
    re_exports: &mut HashMap<String, ImportBinding>,
    export_span: &Span,
    sym: &mut SymbolTable,
) -> Result<(), MetelError> {
    let canon_base = canonical_path(base, path_aliases);
    let base = canon_base.as_slice();

    match tree {
        ImportTree::Glob => {
            // Re-export all public names from the base module.
            if let Some(names) = pub_surface.get(base) {
                for name in names {
                    let symbol_id = sym.intern(base, name);
                    re_exports.insert(
                        name.clone(),
                        ImportBinding {
                            source_module: base.to_vec(),
                            source_name: name.clone(),
                            kind: BindingKind::Item,
                            symbol_id,
                        },
                    );
                }
            }
        }

        ImportTree::Name { name, alias } => {
            let local = alias.as_deref().unwrap_or(name.as_str()).to_string();
            let mut module_candidate = base.to_vec();
            module_candidate.push(name.clone());

            if known_modules.contains(&module_candidate) {
                // Re-exporting a module handle (unusual but allowed).
                let symbol_id = sym.intern(&module_candidate, name);
                re_exports.insert(
                    local,
                    ImportBinding {
                        source_module: module_candidate,
                        source_name: name.clone(),
                        kind: BindingKind::Module,
                        symbol_id,
                    },
                );
            } else {
                // Item re-export: verify it's public in the source module.
                if let Some(surface) = pub_surface.get(base)
                    && !surface.contains(name.as_str())
                {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0009,
                        format!(
                            "visibility error: cannot re-export `{name}` — it is not public in module `{}`",
                            base.join("::")
                        ),
                        export_span,
                    ));
                }
                let symbol_id = sym.intern(base, name);
                re_exports.insert(
                    local,
                    ImportBinding {
                        source_module: base.to_vec(),
                        source_name: name.clone(),
                        kind: BindingKind::Item,
                        symbol_id,
                    },
                );
            }
        }

        ImportTree::Path { name, tree } => {
            let mut new_base = base.to_vec();
            new_base.push(name.clone());
            process_export_tree(
                &new_base,
                tree,
                known_modules,
                pub_surface,
                path_aliases,
                re_exports,
                export_span,
                sym,
            )?;
        }

        ImportTree::Group(items) => {
            for item in items {
                process_export_tree(
                    base,
                    item,
                    known_modules,
                    pub_surface,
                    path_aliases,
                    re_exports,
                    export_span,
                    sym,
                )?;
            }
        }
    }
    Ok(())
}

/// Compute the absolute path prefix corresponding to a path root,
/// given the importing module's own path. Delegates to the canonical
/// implementation in [`crate::data::ast::PathRoot::resolve`]. See ADR-0023.
fn absolute_base(root: &PathRoot, current: &[String]) -> Vec<String> {
    root.resolve(current)
}

#[allow(clippy::too_many_arguments)] // recursive walker threading full resolution context
fn process_tree(
    base: &[String],
    tree: &ImportTree,
    known_modules: &HashSet<Vec<String>>,
    all_re_exports: &HashMap<Vec<String>, HashMap<String, ImportBinding>>,
    path_aliases: &HashMap<Vec<String>, Vec<String>>,
    scope: &mut ModuleScope,
    import_span: &Span,
    sym: &mut SymbolTable,
) -> Result<(), MetelError> {
    let canon_base = canonical_path(base, path_aliases);
    let base = canon_base.as_slice();

    match tree {
        ImportTree::Glob => {
            scope.globs.push((GlobTier::User, base.to_vec()));
        }

        ImportTree::Name { name, alias } => {
            let local = alias.as_deref().unwrap_or(name.as_str()).to_string();

            // Determine whether `base + name` is a known module path —
            // if so this is a module-handle import, not an item import.
            let mut module_candidate = base.to_vec();
            module_candidate.push(name.clone());

            let binding = if known_modules.contains(&module_candidate) {
                ImportBinding {
                    symbol_id: sym.intern(&module_candidate, name),
                    source_module: module_candidate,
                    source_name: name.clone(),
                    kind: BindingKind::Module,
                }
            } else if let Some(re_export) =
                all_re_exports.get(base).and_then(|m| m.get(name.as_str()))
            {
                // `base` re-exports `name` rather than declaring it directly — reuse
                // the re-export's own binding (already chased to its real source
                // module/id by `collect_re_exports`) instead of minting a fresh
                // symbol under `(base, name)`, which would never match anything
                // Pass 1b actually registers a runtime value under.
                re_export.clone()
            } else {
                // Record the binding regardless of visibility. See ADR-0024.
                // Visibility (T0009) and existence (T0003) are checked by the typechecker
                // in build_import_schemes, which has access to the full graph and GlobalExports.
                ImportBinding {
                    symbol_id: sym.intern(base, name),
                    source_module: base.to_vec(),
                    source_name: name.clone(),
                    kind: BindingKind::Item,
                }
            };

            add_explicit(scope, local, binding, import_span)?;
        }

        ImportTree::Path { name, tree } => {
            let mut new_base = base.to_vec();
            new_base.push(name.clone());
            process_tree(
                &new_base,
                tree,
                known_modules,
                all_re_exports,
                path_aliases,
                scope,
                import_span,
                sym,
            )?;
        }

        ImportTree::Group(items) => {
            for item in items {
                process_tree(
                    base,
                    item,
                    known_modules,
                    all_re_exports,
                    path_aliases,
                    scope,
                    import_span,
                    sym,
                )?;
            }
        }
    }

    Ok(())
}

// arch-implements: ["arch.name-resolution.requirement-2"]
fn add_explicit(
    scope: &mut ModuleScope,
    local_name: String,
    binding: ImportBinding,
    import_span: &Span,
) -> Result<(), MetelError> {
    if let Some(existing) = scope.explicit.get(&local_name) {
        return Err(MetelError::type_error(
            TypeErrorCode::T0011,
            format!(
                "import conflict: `{local_name}` is imported from both `{}` and `{}`; \
                 use an explicit import to disambiguate: `import {}::{}` or `import {}::{}`",
                existing.source_module.join("::"),
                binding.source_module.join("::"),
                existing.source_module.join("::"),
                existing.source_name,
                binding.source_module.join("::"),
                binding.source_name,
            ),
            import_span,
        ));
    }
    scope.explicit.insert(local_name, binding);
    Ok(())
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests;
