use std::collections::{HashMap, HashSet};

use crate::ast::{Decl, ImportTree, PathRoot, Span, TypeExpr, Visibility};
use crate::error::{MetelError, TypeErrorCode};
use crate::module_loader::{LoadedModule, ModuleGraph};
use crate::module_paths::resolve_path_root;
use crate::symbols::SymbolId;

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
    pub references: crate::reference_resolver::ReferenceTable,
}

// ── Symbol interning ──────────────────────────────────────────────────────────

// The interning table is `crate::symbols::SymbolTable`, which pre-seeds the builtin
// `std::core` types and aspects with their well-known `SYM_*` ids and allocates
// user declarations from `USER_SYM_START`. Using it here (rather than a private
// counter from 1) makes the `SYM_TYPE_*` / `SYM_ASPECT_*` constants the *actual*
// ids that flow through the pipeline, so runtime seeding can register builtin
// impls under those same ids. See METEL-185 / ADR-0041.
use crate::symbols::SymbolTable;

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

/// # Errors
/// Returns an error if an import or export cannot be resolved (e.g. an unknown
/// module or name) or if a glob-import conflict cannot be settled.
pub fn resolve(graph: &ModuleGraph) -> Result<ResolvedNames, MetelError> {
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
    let references = crate::reference_resolver::collect_references(
        &module_decls,
        &crate::reference_resolver::ResolveInputs {
            scopes: &scopes,
            pub_surface: &pub_surface,
            declared_names: &declared_names,
            symbols: &sym.map,
            overloaded_names: &overloaded_names,
        },
    );

    Ok(ResolvedNames {
        scopes,
        pub_surface,
        declared_names,
        symbols: sym.map,
        definitions,
        references,
    })
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
                if let Some(surface) = pub_surface.get(base) {
                    if !surface.contains(name.as_str()) {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0009,
                            format!(
                                "visibility error: cannot re-export `{name}` — it is not public in module `{}`",
                                base.join("::")
                            ),
                            export_span,
                        ));
                    }
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
/// implementation in [`crate::module_paths::resolve_path_root`]. See ADR-0023.
fn absolute_base(root: &PathRoot, current: &[String]) -> Vec<String> {
    resolve_path_root(root, current)
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
mod tests {
    use super::*;
    use crate::ast::{
        Block, Decl, FunDecl, ImportDecl, ImportPath, ImportTree, PathRoot, Program, Span,
        Visibility,
    };
    use crate::module_loader::{LoadedModule, ModuleGraph};
    use std::path::PathBuf;

    fn span() -> Span {
        Span::new(0, 0, "test")
    }

    fn make_import(root: PathRoot, tree: ImportTree) -> ImportDecl {
        ImportDecl {
            path: ImportPath { root, tree },
            span: span(),
        }
    }

    fn make_program(imports: Vec<ImportDecl>) -> Program {
        Program {
            imports,
            exports: vec![],
            decls: vec![],
        }
    }

    fn make_program_with_pubs(imports: Vec<ImportDecl>, pub_names: &[&str]) -> Program {
        let decls = pub_names
            .iter()
            .map(|n| {
                Decl::Fun(FunDecl {
                    visibility: Visibility::Public,
                    name: (*n).into(),
                    generics: vec![],
                    where_clause: None,
                    params: vec![],
                    return_type: None,
                    native: None,
                    body: Block {
                        stmts: vec![],
                        tail: None,
                        span: span(),
                    },
                    span: span(),
                })
            })
            .collect();
        Program {
            imports,
            exports: vec![],
            decls,
        }
    }

    fn make_graph(modules: Vec<(Vec<String>, Program)>) -> ModuleGraph {
        let root = if modules.is_empty() {
            PathBuf::new()
        } else {
            PathBuf::from("root.mtl")
        };
        let modules = modules
            .into_iter()
            .map(|(path, program)| LoadedModule {
                module_path: path,
                file_path: PathBuf::from("test.mtl"),
                program,
            })
            .collect();
        ModuleGraph {
            root,
            modules,
            path_aliases: std::collections::HashMap::new(),
        }
    }

    #[test]
    fn resolves_explicit_item_import() {
        // import parser::Token;
        let graph = make_graph(vec![
            (
                vec![],
                make_program(vec![make_import(
                    PathRoot::Name("parser".into()),
                    ImportTree::Name {
                        name: "Token".into(),
                        alias: None,
                    },
                )]),
            ),
            (
                vec!["parser".into()],
                make_program_with_pubs(vec![], &["Token"]),
            ),
        ]);

        let names = resolve(&graph).unwrap();
        let root_scope = &names.scopes[&vec![]];
        let binding = root_scope
            .explicit
            .get("Token")
            .expect("Token should be bound");
        assert_eq!(binding.source_module, vec!["parser"]);
        assert_eq!(binding.source_name, "Token");
        assert_eq!(binding.kind, BindingKind::Item);
    }

    #[test]
    fn resolves_alias_import() {
        // import parser::Token as Tok;
        let graph = make_graph(vec![
            (
                vec![],
                make_program(vec![make_import(
                    PathRoot::Name("parser".into()),
                    ImportTree::Name {
                        name: "Token".into(),
                        alias: Some("Tok".into()),
                    },
                )]),
            ),
            (
                vec!["parser".into()],
                make_program_with_pubs(vec![], &["Token"]),
            ),
        ]);

        let names = resolve(&graph).unwrap();
        let root_scope = &names.scopes[&vec![]];
        assert!(
            root_scope.explicit.contains_key("Tok"),
            "alias Tok should be bound"
        );
        assert!(
            !root_scope.explicit.contains_key("Token"),
            "original name Token should not be bound"
        );
        let binding = &root_scope.explicit["Tok"];
        assert_eq!(binding.source_name, "Token");
    }

    #[test]
    fn resolves_group_import() {
        // import parser::{Ast, Token};
        let graph = make_graph(vec![
            (
                vec![],
                make_program(vec![make_import(
                    PathRoot::Name("parser".into()),
                    ImportTree::Group(vec![
                        ImportTree::Name {
                            name: "Ast".into(),
                            alias: None,
                        },
                        ImportTree::Name {
                            name: "Token".into(),
                            alias: None,
                        },
                    ]),
                )]),
            ),
            (
                vec!["parser".into()],
                make_program_with_pubs(vec![], &["Ast", "Token"]),
            ),
        ]);

        let names = resolve(&graph).unwrap();
        let root_scope = &names.scopes[&vec![]];
        assert!(root_scope.explicit.contains_key("Ast"));
        assert!(root_scope.explicit.contains_key("Token"));
    }

    #[test]
    fn resolves_glob_import() {
        // import parser::*;
        let graph = make_graph(vec![
            (
                vec![],
                make_program(vec![make_import(
                    PathRoot::Name("parser".into()),
                    ImportTree::Glob,
                )]),
            ),
            (vec!["parser".into()], make_program(vec![])),
        ]);

        let names = resolve(&graph).unwrap();
        let root_scope = &names.scopes[&vec![]];
        assert!(
            root_scope.explicit.is_empty(),
            "glob should not add explicit bindings"
        );
        assert_eq!(
            root_scope.globs,
            vec![
                (GlobTier::User, vec!["parser".to_string()]),
                (GlobTier::Std, vec!["std".to_string(), "core".to_string()]),
            ]
        );
    }

    #[test]
    fn resolves_module_handle_import() {
        // import parser; — parser is a known module, so this is a handle import
        let graph = make_graph(vec![
            (
                vec![],
                make_program(vec![make_import(
                    PathRoot::Root,
                    ImportTree::Name {
                        name: "parser".into(),
                        alias: None,
                    },
                )]),
            ),
            (vec!["parser".into()], make_program(vec![])),
        ]);

        let names = resolve(&graph).unwrap();
        let root_scope = &names.scopes[&vec![]];
        let binding = root_scope
            .explicit
            .get("parser")
            .expect("parser handle should be bound");
        assert_eq!(binding.kind, BindingKind::Module);
        assert_eq!(binding.source_module, vec!["parser"]);
    }

    #[test]
    fn rejects_duplicate_explicit_import() {
        // import parser::Token;
        // import lexer::Token;  ← conflict
        let graph = make_graph(vec![
            (
                vec![],
                make_program(vec![
                    make_import(
                        PathRoot::Name("parser".into()),
                        ImportTree::Name {
                            name: "Token".into(),
                            alias: None,
                        },
                    ),
                    make_import(
                        PathRoot::Name("lexer".into()),
                        ImportTree::Name {
                            name: "Token".into(),
                            alias: None,
                        },
                    ),
                ]),
            ),
            (
                vec!["parser".into()],
                make_program_with_pubs(vec![], &["Token"]),
            ),
            (
                vec!["lexer".into()],
                make_program_with_pubs(vec![], &["Token"]),
            ),
        ]);

        let err = resolve(&graph).expect_err("duplicate import should fail");
        assert!(
            err.to_string().contains("Token"),
            "error should mention Token"
        );
    }

    #[test]
    fn private_item_import_is_recorded_for_typechecker() {
        // import parser::Token; where Token is private in parser.
        // The name_resolver records the binding; visibility enforcement (T0009)
        // happens in the typechecker's build_import_schemes which has access to
        // the full NormalizedModuleGraph to distinguish private from absent.
        let graph = make_graph(vec![
            (
                vec![],
                make_program(vec![make_import(
                    PathRoot::Name("parser".into()),
                    ImportTree::Name {
                        name: "Token".into(),
                        alias: None,
                    },
                )]),
            ),
            (vec!["parser".into()], make_program(vec![])), // no pub declarations
        ]);

        let names = resolve(&graph).expect("name_resolver should not reject private imports");
        let root_scope = names.scopes.get(&vec![]).expect("root scope should exist");
        assert!(
            root_scope.explicit.contains_key("Token"),
            "Token binding should be recorded so the typechecker can produce T0009"
        );
    }

    #[test]
    fn resolves_root_absolute_path() {
        // import root::parser::Ast;
        let graph = make_graph(vec![
            (
                vec![],
                make_program(vec![make_import(
                    PathRoot::Root,
                    ImportTree::Path {
                        name: "parser".into(),
                        tree: Box::new(ImportTree::Name {
                            name: "Ast".into(),
                            alias: None,
                        }),
                    },
                )]),
            ),
            (
                vec!["parser".into()],
                make_program_with_pubs(vec![], &["Ast"]),
            ),
        ]);

        let names = resolve(&graph).unwrap();
        let root_scope = &names.scopes[&vec![]];
        let binding = root_scope.explicit.get("Ast").expect("Ast should be bound");
        assert_eq!(binding.source_module, vec!["parser"]);
    }

    #[test]
    fn resolves_self_relative_path() {
        // In module ["parser"], import self::child::Thing;
        let graph = make_graph(vec![
            (
                vec!["parser".into()],
                make_program(vec![make_import(
                    PathRoot::Self_,
                    ImportTree::Path {
                        name: "child".into(),
                        tree: Box::new(ImportTree::Name {
                            name: "Thing".into(),
                            alias: None,
                        }),
                    },
                )]),
            ),
            (
                vec!["parser".into(), "child".into()],
                make_program_with_pubs(vec![], &["Thing"]),
            ),
        ]);

        let names = resolve(&graph).unwrap();
        let parser_scope = &names.scopes[&vec!["parser".to_string()]];
        let binding = parser_scope
            .explicit
            .get("Thing")
            .expect("Thing should be bound");
        assert_eq!(binding.source_module, vec!["parser", "child"]);
    }

    #[test]
    fn resolves_super_relative_path() {
        // In module ["parser", "child"], import super::Token;
        let graph = make_graph(vec![
            (
                vec!["parser".into(), "child".into()],
                make_program(vec![make_import(
                    PathRoot::Super,
                    ImportTree::Name {
                        name: "Token".into(),
                        alias: None,
                    },
                )]),
            ),
            (
                vec!["parser".into()],
                make_program_with_pubs(vec![], &["Token"]),
            ),
        ]);

        let names = resolve(&graph).unwrap();
        let child_scope = &names.scopes[&vec!["parser".to_string(), "child".to_string()]];
        let binding = child_scope
            .explicit
            .get("Token")
            .expect("Token should be bound");
        assert_eq!(binding.source_module, vec!["parser"]);
    }

    fn make_export(root: PathRoot, tree: ImportTree) -> crate::ast::ExportDecl {
        use crate::ast::ExportDecl;
        ExportDecl {
            path: ImportPath { root, tree },
            span: span(),
        }
    }

    #[test]
    fn facade_re_exports_item_for_callers() {
        // parser.mln: export ast::Ast;
        // Caller can import parser::Ast even though Ast is defined in ast.
        let ast_module_prog = make_program_with_pubs(vec![], &["Ast"]);
        let parser_prog = Program {
            imports: vec![],
            exports: vec![make_export(
                PathRoot::Name("ast".into()),
                ImportTree::Name {
                    name: "Ast".into(),
                    alias: None,
                },
            )],
            decls: vec![],
        };
        let root_prog = make_program(vec![make_import(
            PathRoot::Name("parser".into()),
            ImportTree::Name {
                name: "Ast".into(),
                alias: None,
            },
        )]);
        let graph = make_graph(vec![
            (vec![], root_prog),
            (vec!["parser".into()], parser_prog),
            // ast is imported by parser, so its path is ["parser", "ast"]
            (vec!["parser".into(), "ast".into()], ast_module_prog),
        ]);

        let names = resolve(&graph).unwrap();
        // parser's re_exports should include Ast
        let parser_scope = &names.scopes[&vec!["parser".to_string()]];
        assert!(
            parser_scope.re_exports.contains_key("Ast"),
            "parser should re-export Ast"
        );
        // root should have imported Ast from parser — but the binding's real identity
        // (ADR-0042) chases through the re-export to Ast's actual declaring module,
        // `["parser", "ast"]`, not the facade's own path. This is what makes the
        // binding's `symbol_id` match the same id `ast`'s own module registers a
        // runtime value under, instead of an orphaned id nothing ever populates.
        let root_scope = &names.scopes[&vec![]];
        let binding = root_scope
            .explicit
            .get("Ast")
            .expect("Ast should be importable from facade");
        assert_eq!(binding.source_module, vec!["parser", "ast"]);
        // The real regression check (ADR-0042): this binding's id must be the *same*
        // id `Ast`'s own declaration was interned under — not a fresh id minted for
        // `(["parser"], "Ast")`, which nothing would ever register a runtime value
        // under, since `Ast` isn't actually declared in `parser` itself.
        let real_id = names.symbols[&(
            vec!["parser".to_string(), "ast".to_string()],
            "Ast".to_string(),
        )];
        assert_eq!(
            binding.symbol_id, real_id,
            "an import of a re-exported name must reuse its real declaration's id"
        );
    }

    #[test]
    fn re_export_alias_is_visible_not_original() {
        // parser.mln: export ast::Ast as Tree;
        let ast_module_prog = make_program_with_pubs(vec![], &["Ast"]);
        let parser_prog = Program {
            imports: vec![],
            exports: vec![make_export(
                PathRoot::Name("ast".into()),
                ImportTree::Name {
                    name: "Ast".into(),
                    alias: Some("Tree".into()),
                },
            )],
            decls: vec![],
        };
        let graph = make_graph(vec![
            (vec!["parser".into()], parser_prog),
            // ast is imported by parser, so its path is ["parser", "ast"]
            (vec!["parser".into(), "ast".into()], ast_module_prog),
        ]);

        let names = resolve(&graph).unwrap();
        let parser_scope = &names.scopes[&vec!["parser".to_string()]];
        assert!(
            parser_scope.re_exports.contains_key("Tree"),
            "aliased re-export Tree should appear"
        );
        assert!(
            !parser_scope.re_exports.contains_key("Ast"),
            "original name Ast should not appear"
        );
    }

    #[test]
    fn rejects_re_export_of_private_item() {
        // parser.mln: export ast::Hidden; where Hidden is private in ast
        let ast_module_prog = make_program(vec![]); // no pub declarations
        let parser_prog = Program {
            imports: vec![],
            exports: vec![make_export(
                PathRoot::Name("ast".into()),
                ImportTree::Name {
                    name: "Hidden".into(),
                    alias: None,
                },
            )],
            decls: vec![],
        };
        let graph = make_graph(vec![
            (vec!["parser".into()], parser_prog),
            // ast is imported by parser, so its path is ["parser", "ast"]
            (vec!["parser".into(), "ast".into()], ast_module_prog),
        ]);

        let err = resolve(&graph).expect_err("re-exporting private item should fail");
        let msg = err.to_string();
        assert!(msg.contains("Hidden"), "error should mention Hidden");
        assert!(
            msg.contains("visibility"),
            "error should mention visibility"
        );
    }

    #[test]
    fn glob_re_export_includes_all_public_names() {
        // parser.mln: export ast::*;
        let ast_module_prog = make_program_with_pubs(vec![], &["Ast", "Token"]);
        let parser_prog = Program {
            imports: vec![],
            exports: vec![make_export(PathRoot::Name("ast".into()), ImportTree::Glob)],
            decls: vec![],
        };
        let root_prog = make_program(vec![make_import(
            PathRoot::Name("parser".into()),
            ImportTree::Name {
                name: "Ast".into(),
                alias: None,
            },
        )]);
        let graph = make_graph(vec![
            (vec![], root_prog),
            (vec!["parser".into()], parser_prog),
            // ast is imported by parser, so its path is ["parser", "ast"]
            (vec!["parser".into(), "ast".into()], ast_module_prog),
        ]);

        let names = resolve(&graph).unwrap();
        let parser_scope = &names.scopes[&vec!["parser".to_string()]];
        assert!(parser_scope.re_exports.contains_key("Ast"));
        assert!(parser_scope.re_exports.contains_key("Token"));
        // root can import Ast from parser
        let root_scope = &names.scopes[&vec![]];
        assert!(root_scope.explicit.contains_key("Ast"));
    }

    // ── SymbolId consistency ──────────────────────────────────────────────────

    #[test]
    fn same_declaration_gets_same_symbol_id_regardless_of_importer() {
        // root and other both import parser::Token (via absolute root:: path).
        // Both must get the same SymbolId for parser::Token.
        let root_prog = make_program(vec![make_import(
            PathRoot::Root,
            ImportTree::Path {
                name: "parser".into(),
                tree: Box::new(ImportTree::Name {
                    name: "Token".into(),
                    alias: None,
                }),
            },
        )]);
        let other_prog = make_program(vec![make_import(
            PathRoot::Root,
            ImportTree::Path {
                name: "parser".into(),
                tree: Box::new(ImportTree::Name {
                    name: "Token".into(),
                    alias: None,
                }),
            },
        )]);
        let graph = make_graph(vec![
            (vec![], root_prog),
            (vec!["other".into()], other_prog),
            (
                vec!["parser".into()],
                make_program_with_pubs(vec![], &["Token"]),
            ),
        ]);

        let names = resolve(&graph).unwrap();
        let root_id = names.scopes[&vec![]].explicit["Token"].symbol_id;
        let other_id = names.scopes[&vec!["other".to_string()]].explicit["Token"].symbol_id;
        assert_eq!(
            root_id, other_id,
            "same declaration must get same SymbolId in both importers"
        );
    }

    #[test]
    fn aliased_import_has_same_symbol_id_as_direct_import() {
        // root imports parser::Token as Tok; other imports parser::Token directly.
        // Both must resolve to the same SymbolId — alias must not change identity.
        let root_prog = make_program(vec![make_import(
            PathRoot::Root,
            ImportTree::Path {
                name: "parser".into(),
                tree: Box::new(ImportTree::Name {
                    name: "Token".into(),
                    alias: Some("Tok".into()),
                }),
            },
        )]);
        let other_prog = make_program(vec![make_import(
            PathRoot::Root,
            ImportTree::Path {
                name: "parser".into(),
                tree: Box::new(ImportTree::Name {
                    name: "Token".into(),
                    alias: None,
                }),
            },
        )]);
        let graph = make_graph(vec![
            (vec![], root_prog),
            (vec!["other".into()], other_prog),
            (
                vec!["parser".into()],
                make_program_with_pubs(vec![], &["Token"]),
            ),
        ]);

        let names = resolve(&graph).unwrap();
        let alias_id = names.scopes[&vec![]].explicit["Tok"].symbol_id;
        let direct_id = names.scopes[&vec!["other".to_string()]].explicit["Token"].symbol_id;
        assert_eq!(
            alias_id, direct_id,
            "aliased import should have same SymbolId as direct import"
        );
    }

    #[test]
    fn distinct_declarations_get_distinct_symbol_ids() {
        // parser::Token and parser::Ast must have different SymbolIds.
        let graph = make_graph(vec![
            (
                vec![],
                make_program(vec![make_import(
                    PathRoot::Name("parser".into()),
                    ImportTree::Group(vec![
                        ImportTree::Name {
                            name: "Token".into(),
                            alias: None,
                        },
                        ImportTree::Name {
                            name: "Ast".into(),
                            alias: None,
                        },
                    ]),
                )]),
            ),
            (
                vec!["parser".into()],
                make_program_with_pubs(vec![], &["Token", "Ast"]),
            ),
        ]);

        let names = resolve(&graph).unwrap();
        let root_scope = &names.scopes[&vec![]];
        let token_id = root_scope.explicit["Token"].symbol_id;
        let ast_id = root_scope.explicit["Ast"].symbol_id;
        assert_ne!(
            token_id, ast_id,
            "distinct declarations must have distinct SymbolIds"
        );
    }

    #[test]
    fn definitions_index_maps_symbol_to_declaration_span() {
        // A module with a public function `foo`. Its SymbolId must map to a
        // definition span in ResolvedNames.definitions (RFC-0059).
        let graph = make_graph(vec![(
            vec!["lib".into()],
            make_program_with_pubs(vec![], &["foo"]),
        )]);

        let names = resolve(&graph).unwrap();
        let foo_id = names.symbols[&(vec!["lib".to_string()], "foo".to_string())];
        assert!(
            names.definitions.contains_key(&foo_id),
            "definitions should contain the SymbolId of `foo`"
        );
    }

    #[test]
    fn definitions_index_covers_every_declared_symbol() {
        // Every top-level declared name in a module should have a definition span.
        let graph = make_graph(vec![(
            vec!["lib".into()],
            make_program_with_pubs(vec![], &["a", "b", "c"]),
        )]);

        let names = resolve(&graph).unwrap();
        for name in ["a", "b", "c"] {
            let id = names.symbols[&(vec!["lib".to_string()], name.to_string())];
            assert!(
                names.definitions.contains_key(&id),
                "definitions should contain `{name}`"
            );
        }
    }

    #[test]
    fn interns_impl_and_aspect_method_symbols() {
        // Inherent, aspect-impl, and aspect-declared methods each get a distinct
        // SymbolId under their structured key, with a recorded definition span
        // (METEL-185 step 3a).
        let src = "struct Foo { x: i64 }\n\
                   extend Foo { fun bar(self) -> i64 { self.x } }\n\
                   aspect Greet { fun hi(self) -> i64; }\n\
                   extend Foo: Greet { fun hi(self) -> i64 { 1 } }";
        let program = crate::parser::parse(src, "t.mtl").expect("parse");
        let graph = make_graph(vec![(vec![], program)]);
        let names = resolve(&graph).unwrap();

        let inherent = names.symbols[&(vec![], "Foo::bar".to_string())];
        let aspect_impl = names.symbols[&(vec![], "Foo::Greet::hi".to_string())];
        let aspect_decl = names.symbols[&(vec![], "Greet::hi".to_string())];

        for id in [inherent, aspect_impl, aspect_decl] {
            assert!(
                names.definitions.contains_key(&id),
                "method symbol {id:?} should have a definition span"
            );
        }
        assert_ne!(
            inherent, aspect_impl,
            "an inherent method and an aspect-impl method on the same type must differ"
        );
        assert_ne!(aspect_impl, aspect_decl);
    }

    #[test]
    fn symbol_id_is_stable_in_symbol_table() {
        // names.symbols should contain the same (module, name) → id mapping.
        let graph = make_graph(vec![
            (
                vec![],
                make_program(vec![make_import(
                    PathRoot::Name("parser".into()),
                    ImportTree::Name {
                        name: "Token".into(),
                        alias: None,
                    },
                )]),
            ),
            (
                vec!["parser".into()],
                make_program_with_pubs(vec![], &["Token"]),
            ),
        ]);

        let names = resolve(&graph).unwrap();
        let binding_id = names.scopes[&vec![]].explicit["Token"].symbol_id;
        let table_id = names.symbols[&(vec!["parser".to_string()], "Token".to_string())];
        assert_eq!(
            binding_id, table_id,
            "SymbolId in binding must match entry in names.symbols"
        );
    }

    #[test]
    fn symbol_id_is_independent_of_module_resolution_order() {
        // ADR-0054's structural-allocation amendment (metel-core#1048): a
        // SymbolId must be a function of (module path, name), never of
        // traversal order. Resolving the identical set of modules in reverse
        // order must hand every declaration the same id it got in forward
        // order. Confirmed to fail before this fix: `graph.modules`'s own
        // load-order fed `SymbolTable::intern`'s allocation counter directly,
        // so `a::A` and `b::B` got their ids swapped when the module list was
        // reversed.
        let a = (
            vec!["a".to_string()],
            make_program_with_pubs(vec![], &["A"]),
        );
        let b = (
            vec!["b".to_string()],
            make_program_with_pubs(vec![], &["B"]),
        );

        let forward = resolve(&make_graph(vec![a.clone(), b.clone()])).unwrap();
        let reversed = resolve(&make_graph(vec![b, a])).unwrap();

        let a_key = (vec!["a".to_string()], "A".to_string());
        let b_key = (vec!["b".to_string()], "B".to_string());
        assert_eq!(
            forward.symbols[&a_key], reversed.symbols[&a_key],
            "a::A's SymbolId changed when module resolution order was reversed"
        );
        assert_eq!(
            forward.symbols[&b_key], reversed.symbols[&b_key],
            "b::B's SymbolId changed when module resolution order was reversed"
        );
    }
}
