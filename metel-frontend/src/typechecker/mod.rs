use std::collections::{HashMap, HashSet};
use std::time::Instant;

use serde::Serialize;

use crate::ast::{Decl, Program, Visibility};
use crate::error::MetelError;
use crate::error::TypeErrorCode;
use crate::identity::FrozenIdentity;
use crate::module_loader::LoadedModule;
use crate::name_resolver::{GlobTier, ResolvedNames};
use crate::path_normalizer::NormalizedModuleGraph;
use crate::symbols::SymbolId;
use crate::typed_ast::{ResolvedImportRef, TypedDecl, TypedModule, TypedModuleGraph};
use crate::typeinference::{
    generalize_with_names, unify, GenericBound, InferContext, InferType, Substitution,
    TypeDefinitionRegistry, TypeScheme, TypeVar, TypeVarGenerator,
};

mod construction;
mod conversions;
mod handoff;
mod inference;
mod object_safety;
mod overload;
mod projections;
pub use overload::core_native_symbol;
mod registry;

type SchemeEnv = HashMap<String, TypeScheme>;
type DeferredGlobConflicts = HashMap<String, Vec<Vec<String>>>;

#[derive(Debug, Clone, Copy, Default, Serialize)]
pub struct TypecheckPhaseTimings {
    pub registry_ns: u64,
    pub inference_ns: u64,
    pub solve_ns: u64,
    pub scheme_env_ns: u64,
    pub construction_ns: u64,
    pub finalize_ns: u64,
    pub solve_calls: u64,
    pub constraints_processed: u64,
}

#[derive(Debug, Clone)]
struct CheckImplReport {
    typed_decls: Vec<TypedDecl>,
    scheme_env: SchemeEnv,
    registry: TypeDefinitionRegistry,
    timings: TypecheckPhaseTimings,
}

#[allow(dead_code)] // public profiling API for benchmark workflows
#[derive(Debug)]
pub struct CheckGraphReport {
    pub graph: TypedModuleGraph,
    pub timings: TypecheckPhaseTimings,
    /// Non-fatal diagnostics emitted while checking the graph.
    pub warnings: Vec<String>,
}

// ── ScopedEnv ─────────────────────────────────────────────────────────────────

/// A single resolved import binding, tracking the source module for conflict
/// reporting. Used by `ScopedEnv` and by #177 (T0011 conflict detection).
#[allow(dead_code, clippy::large_enum_variant)]
enum Binding {
    /// Unambiguous: one scheme from one source module.
    Single {
        scheme: TypeScheme,
        source: ModulePath,
    },
    /// Conflicting glob imports both export the same name.
    /// Deferred error: T0011 fires when the name is looked up.
    Conflict { sources: Vec<ModulePath> },
}

/// Per-module import scope, seeded imports-first then local declarations.
/// Used to build the `SchemeEnv` passed to `check_impl`. (#177 will use this.)
#[allow(dead_code)]
type ScopedEnv = HashMap<String, Binding>;

struct FunGeneralization {
    name: String,
    fun_ty: InferType,
    env_fvs: HashSet<TypeVar>,
    /// Maps `TypeVar` ID → source-level generic param name, for scheme `param_names`.
    name_map: HashMap<TypeVar, String>,
    /// Maps `TypeVar` ID → aspect bounds, attached to the re-generalized scheme
    /// so bounds survive prelude/export scheme propagation.
    bounds: HashMap<TypeVar, Vec<GenericBound>>,
    /// Maps `TypeVar` ID → negative aspect bounds (RFC-0072, issue #243).
    neg_bounds: HashMap<TypeVar, Vec<GenericBound>>,
    /// Maps `TypeVar` ID → whether the parameter is record-kinded.
    record_kinds: HashMap<TypeVar, bool>,
    /// Maps final (post-solve) `TypeVar` ID → associated-type projection metadata
    /// (RFC-0082, issue #242), attached to the re-generalized scheme so a function
    /// returning `T::AssocType` still resolves correctly when called through the
    /// re-exported `scheme_env` (which is what the construction pass actually
    /// reads, not the local scheme bound during inference).
    assoc_projections: HashMap<TypeVar, (usize, String, String, TypeVar)>,
    /// Maps `TypeVar` ID → associated-type equality constraints (RFC-0082 §4,
    /// issue #242), same re-export rationale as `assoc_projections` above.
    assoc_eq: HashMap<TypeVar, Vec<(String, String, InferType)>>,
    /// Maps `TypeVar` ID → opaque-return metadata (RFC-0037, issue #240):
    /// `(aspect_name, concrete_type)`. Attached to the re-generalized scheme so
    /// the opaque-return identity survives the rebuild into `scheme_env` (which
    /// is what the construction pass actually reads), and through
    /// `refresh_scheme_for_export` for cross-module calls.
    opaque_returns: HashMap<TypeVar, (String, crate::types::Type)>,
}

// ── CorePrelude ────────────────────────────────────────────────────────────────

/// The `std::core` scheme surface, derived entirely by parsing the embedded
/// `stdlib/core.mtl` (METEL-181): free native functions plus the joined-key
/// static constructors (`List::new`). Seeded into every module's scheme env so
/// the single-program pipeline (which performs no module loading) sees the
/// same names the module-graph path gets from the real `std::core` module.
pub struct CorePrelude {
    schemes: SchemeEnv,
}

impl CorePrelude {
    /// No standard library names pre-loaded. Use in tests that do not need std.
    #[allow(dead_code)] // public API used by module-loading test harness
    #[must_use]
    pub fn empty() -> Self {
        Self {
            schemes: HashMap::new(),
        }
    }

    pub(super) fn schemes(&self) -> &SchemeEnv {
        &self.schemes
    }

    pub(super) fn contains(&self, name: &str) -> bool {
        self.schemes.contains_key(name)
    }
}

impl Default for CorePrelude {
    /// All built-in function schemes (print, assert, `List::new`, …), derived
    /// from the embedded `std::core` source.
    ///
    /// The generator starts at 10000 so that prelude `TypeVars` never collide
    /// with the registry `TypeVars` allocated by `build_registry` (which starts
    /// at 0 and typically allocates fewer than 100 vars). See ADR-0027.
    fn default() -> Self {
        let mut schemes = HashMap::new();
        let mut gen = TypeVarGenerator::with_counter(10000);
        registry::populate_std_schemes(&mut schemes, &mut gen);
        Self { schemes }
    }
}

// ── GlobalExports ─────────────────────────────────────────────────────────────

type ModulePath = Vec<String>;

struct ModuleExports {
    pub_schemes: SchemeEnv,
}

struct GlobalExports {
    modules: HashMap<ModulePath, ModuleExports>,
}

impl GlobalExports {
    fn new() -> Self {
        Self {
            modules: HashMap::new(),
        }
    }

    fn insert(&mut self, path: ModulePath, exports: ModuleExports) {
        self.modules.insert(path, exports);
    }

    fn get_scheme(&self, module_path: &[String], name: &str) -> Option<&TypeScheme> {
        self.modules.get(module_path)?.pub_schemes.get(name)
    }

    fn all_pub_schemes(&self, module_path: &[String]) -> Option<&SchemeEnv> {
        Some(&self.modules.get(module_path)?.pub_schemes)
    }
}

/// Alpha-rename a scheme's quantified vars (and their occurrences in the body)
/// into the dedicated export `TypeVar` range. Sound for the closed schemes that
/// cross module boundaries (T0010 guarantees pub functions are fully annotated;
/// native signatures are annotation-derived). See `export_gen` in `check_graph`.
fn refresh_scheme_for_export(scheme: &TypeScheme, gen: &mut TypeVarGenerator) -> TypeScheme {
    if scheme.quantified_vars.is_empty() {
        return scheme.clone();
    }
    let (ty, renaming) = crate::typeinference::instantiate_with_renaming(scheme, gen);
    let quantified_vars = scheme.quantified_vars.iter().map(|v| renaming[v]).collect();
    TypeScheme {
        quantified_vars,
        param_names: scheme.param_names.clone(),
        // Order is preserved by the renaming, so positional bounds stay valid.
        bounds: scheme.bounds.clone(),
        neg_bounds: scheme.neg_bounds.clone(),
        record_kinds: scheme.record_kinds.clone(),
        assoc_projections: vec![],
        assoc_eq_constraints: vec![],
        // RFC-0037 opaque-return metadata is positional (index-aligned with
        // `quantified_vars`) and stores fully-concrete `Type` values with no
        // TypeVar references, so the renaming doesn't affect it. Must NOT be
        // dropped here the way `assoc_projections`/`assoc_eq_constraints` are
        // above (issue #242's cross-module landmine) — a `pub fun` returning
        // `impl Aspect` called from another module silently loses its
        // concrete-type backfill if this is zeroed.
        opaque_returns: scheme.opaque_returns.clone(),
        ty,
    }
}

// ── check_pub_annotations ─────────────────────────────────────────────────────

/// Enforce T0010: every `pub` function must have explicit return type and
/// explicit parameter type annotations. Runs before inference so errors are
/// surfaced early with clear messages rather than cryptic inference failures
/// when downstream modules attempt to import the function.
fn check_pub_annotations(loaded: &LoadedModule, names: &ResolvedNames) -> Result<(), MetelError> {
    let Some(pub_surface) = names.pub_surface.get(&loaded.module_path) else {
        return Ok(());
    };

    for decl in &loaded.program.decls {
        match decl {
            Decl::Fun(fd) if fd.visibility == Visibility::Public => {
                if !pub_surface.contains(fd.name.as_str()) {
                    continue;
                }
                // Native (stdlib host-backed) functions are exempt: their
                // signature is validated by `native_fun_ty` (which requires
                // parameter annotations), and an omitted return type is unit.
                if fd.native.is_some() {
                    continue;
                }
                if fd.return_type.is_none() {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0010,
                        format!(
                            "public declaration `{}` requires an explicit return type annotation; \
                             add `-> <Type>` after the parameter list",
                            fd.name
                        ),
                        &fd.span,
                    ));
                }
                for param in &fd.params {
                    if param.type_ann.is_none() {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0010,
                            format!(
                                "public declaration `{}` requires explicit type annotations on \
                                 all parameters; add `: <Type>` to parameter `{}`",
                                fd.name, param.name
                            ),
                            &param.span,
                        ));
                    }
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Warn about field visibility that cannot have any cross-module effect because
/// the enclosing struct is private (RFC-0032 D3).
fn inert_public_field_warnings(loaded: &LoadedModule) -> Vec<String> {
    loaded
        .program
        .decls
        .iter()
        .filter_map(|decl| match decl {
            Decl::Struct(sd) if sd.visibility == Visibility::Private => Some(sd),
            _ => None,
        })
        .flat_map(|sd| {
            sd.fields
                .iter()
                .filter(|field| field.visibility == Visibility::Public)
                .map(move |field| {
                    format!(
                        "field `{}.{}` is marked public, but enclosing struct `{}` is private; \
                         the field cannot be reached across a module boundary, so the annotation is inert",
                        sd.name, field.name, sd.name
                    )
                })
        })
        .collect()
}

// ── check_graph ───────────────────────────────────────────────────────────────

/// Typecheck a normalized module graph. Processes modules in topological order
/// (dependencies before dependents); each module is typechecked against its
/// declared imports, with results accumulated into `GlobalExports`. See
/// ADR-0022 for the `GlobalExports` accumulator pattern and the invariant that
/// `imported_schemes` must reach both inference and construction.
///
/// # Errors
/// Returns an error if any module fails to typecheck.
pub fn check_graph(
    graph: &NormalizedModuleGraph,
    names: &ResolvedNames,
    std_prelude: &CorePrelude,
) -> Result<TypedModuleGraph, MetelError> {
    Ok(check_graph_with_report(graph, names, std_prelude, None)?.graph)
}

/// # Errors
/// Returns an error if any module fails to typecheck.
///
/// `identity` bundles the frozen-identity tables (ADR-0054): the member table
/// (#1051), so construction stamps field accesses / enum-variant literals with
/// their `FieldId` / `VariantId` (#1062), and the span → `BindingId` bridge
/// (#1052), so `TypedExpr::Ident` carries its resolved binding. `None` — the
/// move-check and diagnostic-tool entry points — leaves every id `None`.
pub fn check_graph_with_report(
    graph: &NormalizedModuleGraph,
    names: &ResolvedNames,
    std_prelude: &CorePrelude,
    identity: Option<FrozenIdentity<'_>>,
) -> Result<CheckGraphReport, MetelError> {
    // std::core is a real module in the graph (synthesized ahead of user code),
    // so its exports land in GlobalExports through the normal per-module loop —
    // no seeding needed (METEL-181).
    let mut global_exports = GlobalExports::new();

    let mut typed_modules: Vec<TypedModule> = Vec::new();
    // Accumulated resolved type definitions from already-checked modules.
    // Passed to check_impl so cross-module struct/enum field references are visible.
    // See ADR-0032.
    let mut type_registry = TypeDefinitionRegistry::new();
    let mut timings = TypecheckPhaseTimings::default();
    let mut warnings = Vec::new();
    // Exported schemes are alpha-renamed into a dedicated high TypeVar range so
    // their ids can never collide with any module's local generator (which
    // restarts near 0 per module). Without this, an imported scheme whose
    // quantified var id matches a live local var can produce a cyclic
    // substitution and hang `Substitution::apply` (METEL-181; see ADR-0027 for
    // the 10000-offset precedent and construct_generic_body's 1_000_000 range).
    let mut export_gen = TypeVarGenerator::with_counter(2_000_000);

    for loaded in graph.modules() {
        check_pub_annotations(loaded, names)?;
        warnings.extend(inert_public_field_warnings(loaded));
        let (imported_schemes, deferred_conflicts) =
            build_import_schemes(loaded, names, &global_exports, graph)?;
        let report = check_impl_with_report(
            &loaded.program,
            &imported_schemes,
            deferred_conflicts,
            &type_registry,
            std_prelude,
            &loaded.module_path,
            Some(&names.symbols),
            Some(&names.references),
            Some(&names.scopes),
            identity,
        )?;
        accumulate_typecheck_timings(&mut timings, report.timings);
        type_registry = report.registry;

        // Export pub names from this module's scheme_env, plus re-exported names
        // pulled from their source modules in GlobalExports (#178).
        let pub_schemes = filter_pub_schemes(&report.scheme_env, loaded, names, &global_exports);
        let pub_schemes = pub_schemes
            .into_iter()
            .map(|(name, scheme)| (name, refresh_scheme_for_export(&scheme, &mut export_gen)))
            .collect();
        global_exports.insert(loaded.module_path.clone(), ModuleExports { pub_schemes });

        // Populate imported_names: local_name → (source_module, canonical_name).
        // Used by evaluate_graph to seed each module's isolated Environment. See ADR-0029.
        let (import_aliases, imported_names) = names
            .scopes
            .get(&loaded.module_path)
            .map(|scope| {
                let aliases = scope
                    .explicit
                    .iter()
                    .filter(|(local, binding)| *local != &binding.source_name)
                    .map(|(local, binding)| (local.clone(), binding.source_name.clone()))
                    .collect();

                let mut imports: HashMap<String, ResolvedImportRef> = HashMap::new();

                // Glob imports (lower priority — added first so explicit can override).
                // Process Std then User, mirroring build_import_schemes tier ordering.
                // std::core names are always registered via builtins, so skipping the
                // Std glob here is safe — but we still process User globs for cross-module names.
                let ordered_globs = scope
                    .globs
                    .iter()
                    .filter(|(t, _)| *t == GlobTier::Std)
                    .chain(scope.globs.iter().filter(|(t, _)| *t == GlobTier::User));
                for (_, glob_module) in ordered_globs {
                    let Some(pub_schemes) = global_exports.all_pub_schemes(glob_module) else {
                        continue;
                    };
                    for name in pub_schemes.keys() {
                        imports.insert(
                            name.clone(),
                            ResolvedImportRef {
                                source_module: glob_module.clone(),
                                canonical_name: name.clone(),
                                // A glob-imported name is still a reference to
                                // its declaring module's own canonical
                                // declaration (ADR-0054 / metel-core#1052) —
                                // look its SymbolId up the same way an
                                // explicit import's binding already carries
                                // one, instead of leaving it `None`.
                                symbol_id: names
                                    .symbols
                                    .get(&(glob_module.clone(), name.clone()))
                                    .copied(),
                            },
                        );
                    }
                }

                // Explicit imports (higher priority — overwrite globs).
                for (local, binding) in &scope.explicit {
                    if binding.kind == crate::name_resolver::BindingKind::Item {
                        imports.insert(
                            local.clone(),
                            ResolvedImportRef {
                                source_module: binding.source_module.clone(),
                                canonical_name: binding.source_name.clone(),
                                symbol_id: Some(binding.symbol_id),
                            },
                        );
                    }
                }

                (aliases, imports)
            })
            .unwrap_or_default();

        // Add builtin schemes so construction-at-call-time can resolve builtins
        // like `array_len` inside generic function bodies.
        let mut full_scheme_env = report.scheme_env;
        registry::register_builtin_schemes(&mut full_scheme_env, std_prelude);
        typed_modules.push(TypedModule {
            module_path: loaded.module_path.clone(),
            decls: report.typed_decls,
            import_aliases,
            imported_names,
            scheme_env: full_scheme_env,
        });
    }

    Ok(CheckGraphReport {
        graph: TypedModuleGraph {
            modules: typed_modules,
            type_registry,
        },
        timings,
        warnings,
    })
}

/// Build the set of imported name→scheme bindings for a module, drawn from
/// `GlobalExports`. Explicit imports take precedence over glob imports.
///
/// For explicit imports: if the name is absent from `GlobalExports`, checks
/// `names.declared_names` to distinguish T0009 (private item — declared but
/// not pub) from T0003 (name does not exist). See #191.
/// Returns the resolved import schemes plus a map of deferred same-tier glob conflicts.
/// Conflicts are not rejected here; T0011 fires at the use site. (METEL-98)
fn build_import_schemes(
    loaded: &LoadedModule,
    names: &ResolvedNames,
    global_exports: &GlobalExports,
    graph: &NormalizedModuleGraph,
) -> Result<(SchemeEnv, DeferredGlobConflicts), MetelError> {
    let mut env: SchemeEnv = HashMap::new();
    let mut deferred_conflicts: HashMap<String, Vec<Vec<String>>> = HashMap::new();
    let Some(scope) = names.scopes.get(&loaded.module_path) else {
        return Ok((env, deferred_conflicts));
    };

    // Glob imports (lower priority — added first so explicit can override).
    // Process Std globs before User globs so User silently wins cross-tier conflicts.
    // T0011 fires only when two globs of the **same** tier export the same name. See ADR-0026.
    let mut glob_source: HashMap<String, (Vec<String>, GlobTier)> = HashMap::new();
    let ordered_globs = scope
        .globs
        .iter()
        .filter(|(t, _)| *t == GlobTier::Std)
        .chain(scope.globs.iter().filter(|(t, _)| *t == GlobTier::User));
    for (tier, glob_module) in ordered_globs {
        let Some(all_schemes) = global_exports.all_pub_schemes(glob_module) else {
            continue;
        };
        for (name, scheme) in all_schemes {
            let conflict = glob_source
                .get(name.as_str())
                .map(|(s, t)| (s.clone(), t.clone()));
            match conflict {
                Some((prior_source, ref prior_tier)) if prior_tier == tier => {
                    // Same-tier conflict — defer T0011 to the use site. (METEL-98)
                    // Remove the name from env so a use site that sees None gets our error,
                    // not a spurious T0003.
                    env.remove(name.as_str());
                    let entry = deferred_conflicts.entry(name.clone()).or_default();
                    if !entry.contains(&prior_source) {
                        entry.push(prior_source.clone());
                    }
                    if !entry.contains(&glob_module.clone()) {
                        entry.push(glob_module.clone());
                    }
                }
                Some((_, GlobTier::User)) => {
                    // Prior User glob claimed this name; current Std glob cannot override.
                }
                _ => {
                    // Either no prior claim, or current User tier overrides a prior Std.
                    glob_source.insert(name.clone(), (glob_module.clone(), tier.clone()));
                    env.insert(name.clone(), scheme.clone());
                }
            }
        }
    }

    // Explicit imports (higher priority — overwrite globs).
    for (local_name, binding) in &scope.explicit {
        if let Some(scheme) =
            global_exports.get_scheme(&binding.source_module, &binding.source_name)
        {
            env.insert(local_name.clone(), scheme.clone());
        } else {
            // No function scheme — check if it is a public struct/enum/aspect (type-only import).
            let is_pub_type = names
                .pub_surface
                .get(&binding.source_module)
                .is_some_and(|surface| surface.contains(binding.source_name.as_str()));
            if is_pub_type {
                // Valid public struct/enum/aspect import — no scheme needed; type registry
                // handles these via type_context. Skip silently.
                continue;
            }
            // Check if the source module is in the graph (not std, which is not file-loaded).
            let src_in_graph = graph
                .modules()
                .iter()
                .any(|m| m.module_path == binding.source_module);
            if src_in_graph {
                let span = find_import_span(loaded, &binding.source_module, &binding.source_name);
                let name_exists = names
                    .declared_names
                    .get(&binding.source_module)
                    .is_some_and(|s| s.contains(binding.source_name.as_str()));
                if name_exists {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0009,
                        format!(
                            "visibility error: `{}` is not public in module `{}`",
                            binding.source_name,
                            binding.source_module.join("::")
                        ),
                        &span,
                    ));
                }
                return Err(MetelError::type_error(
                    TypeErrorCode::T0003,
                    format!(
                        "cannot import `{}` from module `{}`: name does not exist",
                        binding.source_name,
                        binding.source_module.join("::")
                    ),
                    &span,
                ));
            }
            // Source not in graph (std or future external crate) — skip silently.
        }
    }

    Ok((env, deferred_conflicts))
}

/// Find the span of the import declaration in `loaded` that references `source_name`
/// from `source_module`. Falls back to a file-level span if no match is found.
fn find_import_span(
    loaded: &LoadedModule,
    source_module: &[String],
    source_name: &str,
) -> crate::ast::Span {
    use crate::ast::{ImportTree, PathRoot};

    fn tree_contains(tree: &ImportTree, name: &str) -> bool {
        match tree {
            ImportTree::Name { name: n, alias } => n == name || alias.as_deref() == Some(name),
            ImportTree::Path { tree, .. } => tree_contains(tree, name),
            ImportTree::Group(items) => items.iter().any(|t| tree_contains(t, name)),
            ImportTree::Glob => false,
        }
    }

    for import in &loaded.program.imports {
        let root_matches = match &import.path.root {
            PathRoot::Name(n) => source_module.first().is_some_and(|s| s == n),
            PathRoot::Self_ => source_module == loaded.module_path,
            PathRoot::Root | PathRoot::Super => true,
            PathRoot::Std => false,
        };
        if root_matches && tree_contains(&import.path.tree, source_name) {
            return import.span.clone();
        }
    }
    crate::ast::Span::new(0, 0, loaded.file_path.display().to_string())
}

/// Build the public scheme export for a module: pub-declared names from its
/// own `scheme_env`, plus any re-exported names pulled from `global_exports`.
fn filter_pub_schemes(
    scheme_env: &SchemeEnv,
    loaded: &LoadedModule,
    names: &ResolvedNames,
    global_exports: &GlobalExports,
) -> SchemeEnv {
    let Some(pub_names) = names.pub_surface.get(&loaded.module_path) else {
        return HashMap::new();
    };

    // Locally-declared pub names from this module's inference output.
    let mut result: SchemeEnv = scheme_env
        .iter()
        .filter(|(name, _)| pub_names.contains(name.as_str()))
        .map(|(name, scheme)| (name.clone(), scheme.clone()))
        .collect();

    // Re-exported names: present in pub_surface but not in scheme_env.
    // Pull their schemes from the source module's GlobalExports entry.
    if let Some(scope) = names.scopes.get(&loaded.module_path) {
        for (local_name, binding) in &scope.re_exports {
            if pub_names.contains(local_name.as_str()) && !result.contains_key(local_name) {
                if let Some(scheme) =
                    global_exports.get_scheme(&binding.source_module, &binding.source_name)
                {
                    result.insert(local_name.clone(), scheme.clone());
                }
            }
        }
    }

    result
}

/// Run the type checker over an untyped AST, producing a fully typed AST.
/// `native` declarations may appear only in standard-library modules (those
/// whose path begins with `std`). Reject them anywhere else (METEL-182).
fn enforce_native_stdlib_only(program: &Program, module_path: &[String]) -> Result<(), MetelError> {
    fn check_fun(fun: &crate::ast::FunDecl) -> Result<(), MetelError> {
        match &fun.native {
            Some(binding) => Err(MetelError::type_error(
                TypeErrorCode::T0003,
                "`native` functions are only allowed in standard-library modules",
                &binding.span,
            )),
            None => Ok(()),
        }
    }
    if module_path.first().map(String::as_str) == Some("std") {
        return Ok(());
    }
    for decl in &program.decls {
        match decl {
            crate::ast::Decl::Fun(fun) => check_fun(fun)?,
            crate::ast::Decl::Impl(ib) => {
                for m in &ib.methods {
                    check_fun(m)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Construct a `TypedBlock` for a generic (polymorphic) function body at call time.
/// The nominal head of an `extend` block's target, or `None` when the target is
/// structural — `T[]`, a tuple, a `fun` type, an anonymous record (RFC-0061,
/// RFC-0116 §3).
///
/// Both the inference and construction passes need this decision, and both used
/// to make it inline. They disagreed: construction kept the whole path while
/// inference took the last segment, and each carried its own copy of the
/// "is this structural" test. Only the *classification* is shared here — how a
/// pass spells the name it gets back is still its own business, because
/// collapsing that difference would silently change what the registries are
/// keyed on.
pub(crate) fn impl_target_head(target: &crate::ast::TypeExpr) -> Option<&str> {
    match target {
        crate::ast::TypeExpr::Named(name, _) => Some(name),
        _ => None,
    }
}

/// Whether an `extend` block has no single concrete `self` type to construct its
/// method bodies against, so they must be deferred to `FunBody::Generic` and
/// checked per instantiation instead.
///
/// True for two reasons that are really one: the impl declares its own generics
/// (`extend<T> Box<T>: …`), or the target is structural and so has no nominal
/// type to resolve `self` to (`extend i64[]: …`). Treating only the first as a
/// reason is what made a structural target with no generics reach an internal
/// error — it fell through to eager construction against a type named `""`
/// (metel-core#581).
pub(crate) fn impl_defers_method_bodies(ib: &crate::ast::ImplBlock) -> bool {
    !ib.generics.is_empty() || impl_target_head(&ib.target_type).is_none()
}

/// Reject an `extend` on a structural target that has nowhere to register
/// (metel-core#581, metel-core#239).
///
/// RFC-0061 grants aspect impls for structural types and RFC-0116 §3 relies on
/// it for records, but only one form is actually implemented:
/// `extend<T> T[]: Display` registers via `array_target_generic_name` and
/// dispatches. Everything else — a concrete array, and a tuple, record or `fun`
/// target in *either* form — is accepted by the parser and then invisible to
/// both method dispatch and bound satisfaction.
///
/// All of it is an error rather than silent acceptance. A declaration that
/// compiles and does nothing is the failure mode RFC-0071 §9c exists to prevent,
/// and the same judgement was applied to inert `Drop` impls in metel-core#601.
/// Rejecting the generic tuple/record form costs nothing: nobody can depend on
/// the current behaviour, because the current behaviour is that the impl has no
/// effect.
///
/// # Errors
/// Returns `T0003` naming the target kind and the way forward for it.
pub(crate) fn reject_unregisterable_impl_target(
    ib: &crate::ast::ImplBlock,
) -> Result<(), crate::error::MetelError> {
    use crate::ast::TypeExpr;
    if impl_target_head(&ib.target_type).is_some() {
        return Ok(());
    }
    // The one structural target that is genuinely implemented: a generic array
    // impl whose *element* is one of the impl's own type parameters —
    // `extend<T> T[]: Aspect`, which is what `registry::array_target_generic_name`
    // actually registers. `extend<T> i64[]: Aspect` also matches
    // `Array(_) && !generics.is_empty()` but has an unused `T` and a concrete
    // element, so it registers nothing and is exactly as inert as the targets
    // this function rejects — found by adversarial review of the first cut,
    // which checked only "is an array with generics" and not this.
    if registry::array_target_generic_name(ib).is_some() {
        return Ok(());
    }
    let fix = match &ib.target_type {
        TypeExpr::Array(_) => {
            "write it as `extend<T> T[]: Aspect { … }`, where `T` is the \
             array's own element type, or use a named struct"
        }
        _ => "use a named struct",
    };
    let kind = match &ib.target_type {
        // Same message for "no generics" and "generics that do not name the
        // element" — both fail the one check that actually registers an array
        // impl (`registry::array_target_generic_name`), so the fix is the same.
        TypeExpr::Array(_) => {
            "an array type whose element is not one of the impl's own type parameters"
        }
        TypeExpr::Tuple(_) => "a tuple type",
        TypeExpr::Record(_) => "an anonymous record type",
        TypeExpr::Fun { .. } => "a function type",
        TypeExpr::SizedArray(_, _) => "a fixed-size array type",
        TypeExpr::Reference(_) | TypeExpr::MutReference(_) => "a reference type",
        TypeExpr::Unit => "the unit type",
        TypeExpr::Projection { .. } => "an associated-type projection",
        TypeExpr::ImplAspect { .. } => "an `extends Aspect` type",
        // RFC-0116's row projection (`Handle.{ fd }`) — a residual, not a fresh
        // nominal type, so it has no registry key of its own either.
        TypeExpr::RecordProjection { .. } => "a record projection",
        // `dyn Aspect` is existential -- there is no one concrete type to
        // register an impl against, the same reason `impl Aspect` can't be an
        // impl target either.
        TypeExpr::DynAspect { .. } => "a `dyn Aspect` type",
        TypeExpr::Named(_, _) => unreachable!("nominal targets returned early"),
    };
    // T0001, not T0003 — T0003 is "undefined name", and nothing here is
    // undefined. T0001 is what `coherence.rs` already uses for the structurally
    // identical "anonymous records cannot implement `Drop`" rejection, and what
    // metel-core#601 used for an inert `drop` body: this impl is not allowed.
    //
    // Deliberately no issue-number/tracking-link suffix in the message text
    // itself (only in this function's own doc comment, for maintainers): a
    // diagnostic a user pastes into a bug report or reads with no access to
    // this project's tracker should be fully actionable on its own, and an
    // embedded number is exactly the kind of thing that goes stale — this
    // function used to append " (metel-core#239)" here, which cited the wrong
    // repo's issue numbering for weeks after the Codeberg->GitHub migration
    // before anyone noticed, because nothing forces a diagnostic string to be
    // checked the way a doc comment or spec page would be.
    Err(crate::error::MetelError::type_error(
        crate::error::TypeErrorCode::T0001,
        format!(
            "cannot `extend` {kind}: this block's methods could never be found. To fix it, {fix}"
        ),
        &ib.span,
    ))
}

///
/// Called by the evaluator when it encounters `ClosureBody::Untyped` with a `type_ctx`.
/// Instantiates the function's `TypeScheme` using the runtime argument types, builds
/// a `ConstructCtx`, and runs the typechecker's construction pass on the raw block.
///
/// `expected_ret`, when available, is the call site's own already-resolved return type
/// (metel-core#716) — the only source of information for a type parameter that appears
/// solely in return position, since a no-argument generic call gives `arg_types` nothing
/// to recover it from.
///
/// # Errors
///
/// Returns a typechecking error when the body cannot be constructed for the supplied
/// runtime argument types.
pub fn construct_generic_body(
    scheme: &TypeScheme,
    params: &[crate::ast::Param],
    arg_types: &[crate::types::Type],
    body: &crate::ast::Block,
    span: &crate::ast::Span,
    type_ctx: &crate::typeinference::TypeCtx,
    expected_ret: Option<&crate::types::Type>,
) -> Result<crate::typed_ast::TypedBlock, MetelError> {
    construction::construct_generic_body(
        scheme,
        params,
        arg_types,
        body,
        span,
        type_ctx,
        expected_ret,
    )
}

pub(crate) fn symbolic_aspect_method_type(
    registry: &crate::typeinference::TypeDefinitionRegistry,
    aspect: &str,
    method: &crate::ast::AspectMethod,
    placeholder: &str,
) -> Option<crate::typeinference::InferType> {
    construction::symbolic_aspect_method_type(registry, aspect, method, placeholder)
}

pub(crate) fn symbolic_aspect_method_scheme(
    registry: &crate::typeinference::TypeDefinitionRegistry,
    aspect: &str,
    method: &crate::ast::AspectMethod,
    placeholder: &str,
    gen: &mut crate::typeinference::TypeVarGenerator,
) -> Option<crate::typeinference::TypeScheme> {
    construction::symbolic_aspect_method_scheme(registry, aspect, method, placeholder, gen)
}

pub(crate) fn symbolic_impl_method_scheme(
    registry: &crate::typeinference::TypeDefinitionRegistry,
    impl_generics: &[crate::ast::GenericParam],
    method_generics: &[crate::ast::GenericParam],
    target_type: &crate::ast::TypeExpr,
    aspect_name: Option<&str>,
    params: &[crate::ast::Param],
    return_type: Option<&crate::ast::TypeExpr>,
) -> Option<crate::typeinference::TypeScheme> {
    construction::symbolic_impl_method_scheme(
        registry,
        impl_generics,
        method_generics,
        target_type,
        aspect_name,
        params,
        return_type,
    )
}

/// Recover concrete type arguments for a generic struct/enum instance, given the
/// already-computed `Type` of each of its fields (issue #267).
///
/// Runtime `Value::Struct`/`Value::Enum` carry no type-argument info themselves —
/// `Wrapper { value: 5 }`'s runtime type tag is bare `Named("Wrapper", [])`, with no
/// record that `T = i64` for this particular instance. Left alone, that erasure
/// means `construct_generic_body`'s unification of a generic receiver's own type
/// against its (type-arg-erased) runtime-derived type always fails on an arity
/// mismatch (1 declared param vs. 0 recovered), silently defaulting the type
/// param to `Unit` — so any use of a `T`-typed field inside a reconstructed
/// generic method body (e.g. calling a `Display`-bounded method on it) sees `T`
/// as `Unit` instead, which has no such method.
///
/// This reconstructs the type arguments from the other direction: unify each
/// field's *declared* (possibly generic) type template against that field's
/// *actual* type (as the evaluator already computed it from the live value),
/// then read off each of the type's own quantified type variables from the
/// resulting substitution. Best-effort, matching `construct_generic_body`'s own
/// tolerance for the same underlying reason — a field that doesn't mention a
/// given type param at all (e.g. `Perhaps::None`, no payload) leaves it
/// unresolved, defaulted to `Unit` exactly as before this fix for that case.
#[must_use]
#[allow(clippy::implicit_hasher)]
pub fn infer_named_type_args(
    name: &str,
    variant: Option<&str>,
    field_types: &HashMap<String, crate::types::Type>,
    registry: &TypeDefinitionRegistry,
    span: &crate::ast::Span,
) -> Vec<crate::types::Type> {
    use conversions::{infer_type_to_type, type_to_infer};

    let (type_params, field_templates): (&[TypeVar], &[crate::typeinference::FieldEntry]) =
        match variant {
            Some(variant_name) => match registry.enum_info_by_decl_name(name) {
                Some(info) => match info.variants.iter().find(|v| v.name == variant_name) {
                    Some(v) => (&info.type_params, &v.fields),
                    None => return vec![],
                },
                None => return vec![],
            },
            None => match registry.type_id_for_decl_name(name).and_then(|id| {
                Some((
                    registry.struct_type_params_by_id(id)?,
                    registry.struct_fields_by_id(id)?,
                ))
            }) {
                Some((tp, f)) => (tp, f),
                _ => return vec![],
            },
        };

    if type_params.is_empty() {
        return vec![];
    }

    let mut subst = Substitution::new();
    for entry in field_templates {
        let Some(actual_ty) = field_types.get(&entry.name) else {
            continue;
        };
        let actual_it = type_to_infer(actual_ty);
        if let Ok(s) = unify(&subst.apply(&entry.ty), &actual_it) {
            subst = subst.compose(&s);
        }
    }

    type_params
        .iter()
        .map(|&tv| {
            let resolved = subst.apply(&InferType::Var(tv));
            infer_type_to_type(&resolved, span).unwrap_or(crate::types::Type::Unit)
        })
        .collect()
}

/// Core typechecking pipeline.
///
/// - `imported_schemes`: type schemes from imported modules, seeded into the
///   inference context so imported names are visible.
/// - `base_registry`: resolved type definitions accumulated from already-checked
///   dependency modules. Merged into the freshly-built registry so that cross-module
///   type references in struct fields and method signatures are visible. See ADR-0032.
///
/// Returns `(typed_decls, scheme_env, registry)` where `registry` carries this
/// module's type definitions merged with the base, for the next module to use.
#[allow(dead_code)] // retained as a tuple-returning internal helper for existing call patterns
#[allow(clippy::too_many_arguments)] // thin forwarding wrapper around check_impl_with_report
fn check_impl(
    program: &Program,
    imported_schemes: &SchemeEnv,
    deferred_conflicts: HashMap<String, Vec<Vec<String>>>,
    base_registry: &TypeDefinitionRegistry,
    std_prelude: &CorePrelude,
    current_module_path: &[String],
    symbols: Option<&HashMap<(Vec<String>, String), SymbolId>>,
    references: Option<&crate::reference_resolver::ReferenceTable>,
) -> Result<(Vec<TypedDecl>, SchemeEnv, TypeDefinitionRegistry), MetelError> {
    let report = check_impl_with_report(
        program,
        imported_schemes,
        deferred_conflicts,
        base_registry,
        std_prelude,
        current_module_path,
        symbols,
        references,
        None,
        None,
    )?;
    Ok((report.typed_decls, report.scheme_env, report.registry))
}

#[allow(clippy::too_many_arguments)]
fn check_impl_with_report(
    program: &Program,
    imported_schemes: &SchemeEnv,
    deferred_conflicts: HashMap<String, Vec<Vec<String>>>,
    base_registry: &TypeDefinitionRegistry,
    std_prelude: &CorePrelude,
    current_module_path: &[String],
    symbols: Option<&HashMap<(Vec<String>, String), SymbolId>>,
    references: Option<&crate::reference_resolver::ReferenceTable>,
    scopes: Option<&HashMap<Vec<String>, crate::name_resolver::ModuleScope>>,
    identity: Option<FrozenIdentity<'_>>,
) -> Result<CheckImplReport, MetelError> {
    // `native` declarations are stdlib-only: reject them outside `std::…`.
    enforce_native_stdlib_only(program, current_module_path)?;

    // Lowering pass: desugar `impl Aspect` params to fresh anonymous type params.
    let program = inference::lower_impl_aspects_in_program(program.clone());
    // Lowering pass: recognize `T::AssocType` projections (RFC-0082 SS3) among
    // known generic parameter names.
    let program = inference::lower_projections_in_program(program);
    let program = &program;

    let started = Instant::now();
    let mut gen = TypeVarGenerator::new();
    let mut reg = registry::build_registry(program, &mut gen, current_module_path, symbols, scopes);
    // Merge dependency type definitions so cross-module struct/enum refs resolve.
    reg.merge_from(base_registry);
    // Stamp entries with their interned identity (#1068); no-op without context.
    reg.stamp_member_ids(identity.map(|i| i.members));
    // Diagnose bad record projections (RFC-0116 §4) now that the registry is complete:
    // the conversion path is infallible and can only leave a stand-in behind, so precise
    // "unknown type / not a struct / no such field" reporting has to happen here.
    projections::check(program, &reg, current_module_path)?;
    let mut ctx = InferContext::new(reg, gen, imported_schemes, current_module_path.to_vec());
    ctx.seed_glob_conflicts(deferred_conflicts);

    // Pre-pass: register built-in value bindings, build the overload table, and
    // hoist function names. The overload table must be installed before hoisting
    // so hoisting can skip overloaded names (they are dispatched by SymbolId).
    registry::register_primitive_type_bindings(&mut ctx, std_prelude);
    let overloads =
        overload::build_overload_table(&program.decls, ctx.registry(), current_module_path)?;
    ctx.set_overloads(overloads.clone());
    inference::hoist_fun_decls(&program.decls, &mut ctx);
    let registry_ns = elapsed_ns(started);

    // Pass 1: walk AST, emit constraints, collect function generalizations.
    let started = Instant::now();
    let mut fun_generalizations: Vec<FunGeneralization> = vec![];
    inference::infer_program(program, &mut ctx, &mut fun_generalizations)?;
    let infer_total_ns = elapsed_ns(started);
    let solve_after_inference = ctx.solve_stats();

    let started = Instant::now();
    let solved = ctx.solve()?;
    let final_solve_ns = elapsed_ns(started);
    let subst = ctx.default_literal_vars(&solved);
    // metel-core#285: a bare variant that never resolved. Pass 2 only resolves these
    // where an expected type exists, so one still unresolved here is a name that means
    // nothing — reachable when it sits somewhere pass 2 never constructs, such as the
    // body of a closure that is never called.
    if let Some((span, name)) = ctx.unresolved_variant_deferrals(&subst).into_iter().next() {
        return Err(MetelError::type_error(
            crate::error::TypeErrorCode::T0002,
            format!(
                "cannot tell which enum `{name}` belongs to here; there is no expected \
                 type at this position — qualify it (`Enum::{name}`) or annotate the \
                 enclosing declaration"
            ),
            &span,
        ));
    }
    let solve_stats = ctx.solve_stats();
    let solve_ns = solve_after_inference.solve_ns + final_solve_ns;
    let inference_ns = infer_total_ns.saturating_sub(solve_after_inference.solve_ns);

    // Build SchemeEnv from user functions, then add all built-in schemes.
    let started = Instant::now();
    let gen = ctx.split_gen();
    let mut scheme_env: SchemeEnv = HashMap::new();
    for fg in fun_generalizations {
        // fg.fun_ty is already post-inline-solve (resolved_ty from infer_fun_decl).
        // Applying the final module-level subst would collapse generic TypeVars that
        // happened to appear in other functions' constraints. (METEL-137)
        let scheme = generalize_with_names(fg.fun_ty, &fg.env_fvs, &fg.name_map)
            .with_bounds(&fg.bounds)
            .with_neg_bounds(&fg.neg_bounds)
            .with_record_kinds(&fg.record_kinds)
            .with_assoc_projections(&fg.assoc_projections)
            .with_assoc_eq_constraints(&fg.assoc_eq)
            .with_opaque_returns(&fg.opaque_returns);
        scheme_env.insert(fg.name, scheme);
    }
    // Imported schemes must be visible in the construction pass so calls to imported
    // functions can be constructed. Use or_insert so locally-defined names shadow imports.
    // INVARIANT: imported_schemes must be seeded into BOTH InferContext (above, via
    // bind_poly) AND scheme_env (here). Missing either breaks one of the two passes.
    // See ADR-0022.
    for (name, scheme) in imported_schemes {
        scheme_env
            .entry(name.clone())
            .or_insert_with(|| scheme.clone());
    }
    registry::register_builtin_schemes(&mut scheme_env, std_prelude);
    let scheme_env_ns = elapsed_ns(started);

    // Freeze decisions made by inference before construction starts. The typed-AST
    // pass receives concrete facts rather than mutable inference representation.
    let resolved_facts = handoff::ResolvedInferenceFacts::resolve(&ctx, &subst)?;

    // Pass 2: construct typed AST for the current module only.
    // The registry owns all type definitions; ConstructCtx derives concrete envs from it.
    let started = Instant::now();
    let typed_decls = construction::construct_program(
        program,
        &subst,
        &scheme_env,
        ctx.registry(),
        gen,
        symbols,
        &overloads,
        current_module_path,
        references,
        &resolved_facts,
        identity,
    )?;
    let construction_ns = elapsed_ns(started);

    // Return only user-defined names. Builtins (from CorePrelude) are available to
    // every module via the auto-glob and don't need to be in GlobalExports.
    let started = Instant::now();
    let local_value_names = top_level_value_names(program);
    let user_scheme_env: SchemeEnv = scheme_env
        .into_iter()
        .filter(|(name, _)| !std_prelude.contains(name) || local_value_names.contains(name))
        .collect();
    let finalize_ns = elapsed_ns(started);

    let final_registry = ctx.into_registry();
    Ok(CheckImplReport {
        typed_decls,
        scheme_env: user_scheme_env,
        registry: final_registry,
        timings: TypecheckPhaseTimings {
            registry_ns,
            inference_ns,
            solve_ns,
            scheme_env_ns,
            construction_ns,
            finalize_ns,
            solve_calls: solve_stats.solve_calls,
            constraints_processed: solve_stats.constraints_processed,
        },
    })
}

fn accumulate_typecheck_timings(target: &mut TypecheckPhaseTimings, source: TypecheckPhaseTimings) {
    target.registry_ns += source.registry_ns;
    target.inference_ns += source.inference_ns;
    target.solve_ns += source.solve_ns;
    target.scheme_env_ns += source.scheme_env_ns;
    target.construction_ns += source.construction_ns;
    target.finalize_ns += source.finalize_ns;
    target.solve_calls += source.solve_calls;
    target.constraints_processed += source.constraints_processed;
}

fn elapsed_ns(started: Instant) -> u64 {
    started.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64
}

fn top_level_value_names(program: &Program) -> HashSet<String> {
    program
        .decls
        .iter()
        .filter_map(|decl| match decl {
            Decl::Fun(d) => Some(d.name.clone()),
            Decl::Let(d) => Some(d.name.clone()),
            Decl::Mut(d) => Some(d.name.clone()),
            _ => None,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The prelude's free-function schemes are derived from the embedded
    /// std::core source (METEL-181); this asserts the derivation covers every
    /// `native` declaration in core.mtl, so a new stdlib function can never
    /// typecheck differently between the graph path (real module) and the
    /// single-program path (prelude). Replaces the old hand-list parity test —
    /// there is no longer a duplicated set to keep in sync.
    #[test]
    fn prelude_schemes_cover_embedded_core_natives() {
        let prelude = CorePrelude::default();
        let core_path = ["std".to_string(), "core".to_string()];
        let source = crate::stdlib::lookup(&core_path).expect("std::core is embedded");
        let program =
            crate::parser::parse(source, "<embedded std::core>").expect("core.mtl parses");

        let mut native_count = 0usize;
        for decl in &program.decls {
            if let Decl::Fun(fun) = decl {
                if fun.native.is_some() {
                    native_count += 1;
                    // Overloaded core natives (the assert pair) are dispatched
                    // by SymbolId via the seeded overload table — they must
                    // NOT appear in the name-keyed prelude.
                    if overload::core_overload_table().contains_key(&fun.name) {
                        assert!(
                            !prelude.contains(&fun.name),
                            "overloaded std::core native `{}` must not be name-keyed in the prelude",
                            fun.name
                        );
                        assert!(
                            overload::core_native_symbol(fun).is_some(),
                            "overloaded std::core native `{}` must have a canonical SymbolId",
                            fun.name
                        );
                        continue;
                    }
                    assert!(
                        prelude.contains(&fun.name),
                        "prelude is missing a scheme for std::core native `{}`",
                        fun.name
                    );
                }
            }
        }
        assert!(native_count > 0, "core.mtl should declare native functions");
    }

    /// metel-core#1052 (Option A): `construct_generic_body`'s runtime
    /// reconstruction of a generic function body gets real `BindingId`s too,
    /// not just the ahead-of-time construction pass — because `body` is the
    /// exact same `ast::Block` the identity walk already processed, so its
    /// `binding_spans` entries apply unchanged regardless of which concrete
    /// type this particular call instantiates.
    #[test]
    fn construct_generic_body_stamps_a_real_local_id() {
        use crate::identity::{self, BindingId, FrozenIdentity};
        use crate::module_loader::{self, InMemorySourceProvider};
        use crate::typed_ast::TypedExpr;
        use crate::types::Type;
        use std::rc::Rc;

        let root = "generic.mtl";
        let source = "fun pick<T>(a: T, b: T) -> T {\n\tlet r := a;\n\tr\n}\n";
        let provider = InMemorySourceProvider::new(root, source);
        let graph =
            module_loader::load_virtual_root_with(root, &provider).expect("in-memory root loads");
        let names = crate::name_resolver::resolve(&graph).expect("resolves");
        let members = identity::collect_members_for_graph(&graph, &names);
        let allocation = identity::allocate_for_graph(&graph, &names);
        let normalized = crate::path_normalizer::normalize(graph, &names).expect("normalizes");
        crate::coherence::check(&normalized, &names).expect("coheres");
        let typed_report = check_graph_with_report(
            &normalized,
            &names,
            &CorePrelude::default(),
            Some(FrozenIdentity {
                members: &members,
                binding_spans: &allocation.binding_spans,
            }),
        )
        .expect("typechecks");

        // The raw (untyped) declaration — `construct_generic_body` takes the
        // same `ast::Block` the identity walk already saw. std::core is a
        // synthesized module ahead of the user's root, so find `pick` by name
        // rather than assuming module order.
        let module = normalized
            .modules()
            .iter()
            .find(|m| {
                m.program
                    .decls
                    .iter()
                    .any(|d| matches!(d, Decl::Fun(f) if f.name == "pick"))
            })
            .expect("the module declaring `fun pick`");
        let Decl::Fun(fun) = module
            .program
            .decls
            .iter()
            .find(|d| matches!(d, Decl::Fun(f) if f.name == "pick"))
            .expect("`fun pick` in the raw graph")
        else {
            unreachable!()
        };
        let typed_module = typed_report
            .graph
            .modules
            .iter()
            .find(|m| m.module_path == module.module_path)
            .expect("the matching typed module");
        let scheme = typed_module
            .scheme_env
            .get("pick")
            .expect("a scheme for `pick`")
            .clone();

        let type_ctx = crate::typeinference::TypeCtx {
            scheme_env: typed_module.scheme_env.clone(),
            registry: typed_report.graph.type_registry.clone(),
            members: Some(Rc::new(members)),
            binding_spans: Some(Rc::new(allocation.binding_spans)),
        };

        let typed_block = construct_generic_body(
            &scheme,
            &fun.params,
            &[Type::I64, Type::I64],
            &fun.body,
            &fun.span,
            &type_ctx,
            None,
        )
        .expect("reconstructs for i64 args");

        let r_id = typed_block
            .stmts
            .iter()
            .find_map(|d| match d {
                TypedDecl::Let(ld) if ld.name == "r" => ld.local_id,
                _ => None,
            })
            .expect("a local in a runtime-reconstructed generic body carries a LocalId");
        let TypedExpr::Ident(_, Some(BindingId::Local(used)), _, _) =
            typed_block.tail.as_deref().unwrap()
        else {
            panic!("the tail `r` should be a resolved local reference");
        };
        assert_eq!(
            *used, r_id,
            "the reconstructed body's `r` use resolves to the same LocalId as its `let`"
        );

        // Reconstructing the same generic body for a *different* concrete
        // instantiation yields the same `LocalId` for `r` — a binding's
        // lexical identity does not depend on which type parameterized this
        // particular call (relevant to go-to-definition / find-references
        // across monomorphizations).
        let typed_block_str = construct_generic_body(
            &scheme,
            &fun.params,
            &[Type::Str, Type::Str],
            &fun.body,
            &fun.span,
            &type_ctx,
            None,
        )
        .expect("reconstructs for str args");
        let r_id_str = typed_block_str
            .stmts
            .iter()
            .find_map(|d| match d {
                TypedDecl::Let(ld) if ld.name == "r" => ld.local_id,
                _ => None,
            })
            .expect("`let r` carries a LocalId in the str instantiation too");
        assert_eq!(
            r_id, r_id_str,
            "the same source binding keeps one LocalId across monomorphizations"
        );
    }

    /// metel-core#1098: `expr?` desugars (in `construct_propagate_error`) into
    /// a synthesized match with an `Ok`-arm `value` binding and an `Err`-arm
    /// `error` binding — neither has a source pattern to hang an id off, so
    /// the identity walk binds one synthetic id at the `?`'s own span
    /// (`allocate.rs`'s `PropagateError` case) and construction shares it
    /// between both arms, since they're mutually exclusive at runtime.
    #[test]
    fn propagate_error_desugar_shares_one_local_id_between_arms() {
        use crate::identity::{self, FrozenIdentity};
        use crate::module_loader::{self, InMemorySourceProvider};
        use crate::typed_ast::{FunBody, TypedExpr, TypedPattern};

        let root = "prop.mtl";
        let source = "fun get_id() -> Result<i64, i64> { Result::Ok { value = 5 } }\n\
                       fun use_it() -> Result<i64, i64> {\n\
                       \tlet v := get_id()?;\n\
                       \tResult::Ok { value = v }\n\
                       }\n";
        let provider = InMemorySourceProvider::new(root, source);
        let graph =
            module_loader::load_virtual_root_with(root, &provider).expect("in-memory root loads");
        let names = crate::name_resolver::resolve(&graph).expect("resolves");
        let members = identity::collect_members_for_graph(&graph, &names);
        let allocation = identity::allocate_for_graph(&graph, &names);
        let normalized = crate::path_normalizer::normalize(graph, &names).expect("normalizes");
        crate::coherence::check(&normalized, &names).expect("coheres");
        let typed_report = check_graph_with_report(
            &normalized,
            &names,
            &CorePrelude::default(),
            Some(FrozenIdentity {
                members: &members,
                binding_spans: &allocation.binding_spans,
            }),
        )
        .expect("typechecks");

        let module = typed_report
            .graph
            .modules
            .iter()
            .find(|m| {
                m.decls
                    .iter()
                    .any(|d| matches!(d, TypedDecl::Fun(f) if f.name == "use_it"))
            })
            .expect("the module declaring `use_it`");
        let TypedDecl::Fun(fun) = module
            .decls
            .iter()
            .find(|d| matches!(d, TypedDecl::Fun(f) if f.name == "use_it"))
            .expect("`use_it`")
        else {
            unreachable!()
        };
        let FunBody::Typed(body) = &fun.body else {
            panic!("use_it should have a typed body");
        };
        let match_expr = body
            .stmts
            .iter()
            .find_map(|d| match d {
                TypedDecl::Let(ld) if ld.name == "v" => match &ld.value {
                    TypedExpr::Match(m) => Some(m),
                    _ => None,
                },
                _ => None,
            })
            .expect("the `?` desugars to a match assigned to `v`");

        let ok_id = match &match_expr.arms[0].pattern {
            TypedPattern::EnumVariant { fields, .. } => fields[0].2,
            other => panic!("expected the Ok-arm's EnumVariant pattern, got {other:?}"),
        };
        let err_id = match &match_expr.arms[1].pattern {
            TypedPattern::EnumVariant { fields, .. } => fields[0].2,
            other => panic!("expected the Err-arm's EnumVariant pattern, got {other:?}"),
        };
        assert!(
            ok_id.is_some(),
            "the `?` desugar's Ok-arm binding should carry a LocalId"
        );
        assert_eq!(
            ok_id, err_id,
            "the Ok-arm value and Err-arm error share one LocalId \
             (mutually exclusive match arms, safe to share one frame slot)"
        );
    }

    /// metel-core#1100: a top-level `let`/`mut`'s own initializer expression
    /// is now walked by the identity allocator (`allocate.rs`'s
    /// `walk_value_body`, wired into `allocate_module`'s top-level loop) —
    /// previously only `Decl::Fun`/`Impl`/`Aspect` bodies were, so a
    /// reference *inside* a top-level initializer (e.g. `let apply_fn :=
    /// add_one;`) never got a `PositionHit::Reference` entry to promote and
    /// stayed `BindingId`-less. This also fixed metel-core#1099 as a side
    /// effect: a top-level `let`-bound closure literal's own parameters are
    /// inside that same never-walked initializer.
    #[test]
    fn toplevel_let_initializer_reference_carries_a_symbol_id() {
        use crate::identity::{self, BindingId, FrozenIdentity};
        use crate::module_loader::{self, InMemorySourceProvider};
        use crate::typed_ast::{FunBody, TypedExpr};

        let root = "toplevel_init.mtl";
        let source = "fun add_one(x: i64) -> i64 { x + 1 }\n\
                       let apply_fn := add_one;\n\
                       fun main() -> i64 {\n\
                       \tapply_fn(41)\n\
                       }\n";
        let provider = InMemorySourceProvider::new(root, source);
        let graph =
            module_loader::load_virtual_root_with(root, &provider).expect("in-memory root loads");
        let names = crate::name_resolver::resolve(&graph).expect("resolves");
        let members = identity::collect_members_for_graph(&graph, &names);
        let allocation = identity::allocate_for_graph(&graph, &names);
        let normalized = crate::path_normalizer::normalize(graph, &names).expect("normalizes");
        crate::coherence::check(&normalized, &names).expect("coheres");
        let typed_report = check_graph_with_report(
            &normalized,
            &names,
            &CorePrelude::default(),
            Some(FrozenIdentity {
                members: &members,
                binding_spans: &allocation.binding_spans,
            }),
        )
        .expect("typechecks");

        let module = typed_report
            .graph
            .modules
            .iter()
            .find(|m| {
                m.decls
                    .iter()
                    .any(|d| matches!(d, TypedDecl::Let(ld) if ld.name == "apply_fn"))
            })
            .expect("the module declaring `apply_fn`");
        let TypedDecl::Let(apply_fn) = module
            .decls
            .iter()
            .find(|d| matches!(d, TypedDecl::Let(ld) if ld.name == "apply_fn"))
            .expect("`let apply_fn`")
        else {
            unreachable!()
        };
        let TypedExpr::Ident(name, binding, ..) = &apply_fn.value else {
            panic!(
                "apply_fn's initializer should be a bare Ident reference to `add_one`, got {:?}",
                apply_fn.value
            );
        };
        assert_eq!(name, "add_one");
        assert!(
            matches!(binding, Some(BindingId::Global(_))),
            "the `add_one` reference inside apply_fn's own initializer should \
             carry its declaration's SymbolId, not stay identity-less"
        );

        // The call inside `main` still resolves through `Call::callee_id`, as
        // it did before this fix (this file's earlier check makes sure the
        // fix didn't regress the already-working case).
        let TypedDecl::Fun(main) = module
            .decls
            .iter()
            .find(|d| matches!(d, TypedDecl::Fun(f) if f.name == "main"))
            .expect("`main`")
        else {
            unreachable!()
        };
        let FunBody::Typed(body) = &main.body else {
            panic!("main should have a typed body");
        };
        let TypedExpr::Call { callee_id, .. } = body.tail.as_deref().unwrap() else {
            panic!(
                "main's tail should be the apply_fn(41) call, got {:?}",
                body.tail
            );
        };
        assert!(
            callee_id.is_some(),
            "apply_fn(41) should still dispatch via Call::callee_id"
        );
    }

    /// metel-core#1096: an implicit (no `[...]` list) closure's free
    /// `Copy`-typed variables are materialized as `CaptureSpec::Clone`
    /// entries (`verify_closure_capture_list`'s new return value), each
    /// carrying the same `LocalId` as its enclosing binding — here,
    /// `make_adder`'s own parameter `x`, captured implicitly by the closure
    /// it returns.
    #[test]
    fn implicit_copy_capture_carries_the_enclosing_local_id() {
        use crate::identity::{self, FrozenIdentity};
        use crate::module_loader::{self, InMemorySourceProvider};
        use crate::typed_ast::{FunBody, TypedExpr};

        let root = "implicit_capture.mtl";
        let source = "fun make_adder(x: i64) -> |i64| -> i64 {\n\
                       \t|y: i64| -> i64 { x + y }\n\
                       }\n\
                       fun main() -> i64 {\n\
                       \tlet add5 := make_adder(5);\n\
                       \tadd5(3)\n\
                       }\n";
        let provider = InMemorySourceProvider::new(root, source);
        let graph =
            module_loader::load_virtual_root_with(root, &provider).expect("in-memory root loads");
        let names = crate::name_resolver::resolve(&graph).expect("resolves");
        let members = identity::collect_members_for_graph(&graph, &names);
        let allocation = identity::allocate_for_graph(&graph, &names);
        let normalized = crate::path_normalizer::normalize(graph, &names).expect("normalizes");
        crate::coherence::check(&normalized, &names).expect("coheres");
        let typed_report = check_graph_with_report(
            &normalized,
            &names,
            &CorePrelude::default(),
            Some(FrozenIdentity {
                members: &members,
                binding_spans: &allocation.binding_spans,
            }),
        )
        .expect("typechecks");

        let module = typed_report
            .graph
            .modules
            .iter()
            .find(|m| {
                m.decls
                    .iter()
                    .any(|d| matches!(d, TypedDecl::Fun(f) if f.name == "make_adder"))
            })
            .expect("the module declaring `make_adder`");
        let TypedDecl::Fun(fun) = module
            .decls
            .iter()
            .find(|d| matches!(d, TypedDecl::Fun(f) if f.name == "make_adder"))
            .expect("`make_adder`")
        else {
            unreachable!()
        };
        let FunBody::Typed(body) = &fun.body else {
            panic!("make_adder should have a typed body");
        };
        let TypedExpr::Closure {
            captures,
            capture_ids,
            ..
        } = body.tail.as_deref().unwrap()
        else {
            panic!(
                "make_adder's tail should be the inner closure, got {:?}",
                body.tail
            );
        };
        assert_eq!(
            captures.len(),
            1,
            "the implicit closure should materialize one capture for `x`, got {captures:?}"
        );
        assert!(
            matches!(&captures[0], crate::ast::CaptureSpec::Clone { name, .. } if name == "x"),
            "the materialized capture should be a Clone of `x`, got {:?}",
            captures[0]
        );
        assert_eq!(
            capture_ids, &fun.param_ids,
            "the materialized capture's LocalId should match make_adder's own \
             parameter x's LocalId — same binding, same identity"
        );
        assert!(
            matches!(capture_ids[0], Some(_)),
            "the capture should carry a real LocalId, not None"
        );
    }
}
