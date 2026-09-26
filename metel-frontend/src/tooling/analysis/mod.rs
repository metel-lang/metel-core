//! Frontend-only analysis API for tooling consumers.
//!
//! Unlike the interpreter pipeline, this module deliberately stops after
//! typechecking. It is the boundary for editor tooling, documentation tools,
//! and other consumers which need compiler facts but must never evaluate user
//! code.

use std::path::Path;
use std::rc::Rc;

use crate::data::error::MetelError;
use crate::data::typed_ast::TypedModuleGraph;
use crate::identity::{self, MemberTable, ModuleTable, NameInterner, PositionIndex, ResolutionMap};
use crate::pipeline::coherence;
use crate::pipeline::move_check;
use crate::pipeline::name_resolution::name_resolver::{self, ResolvedNames};
use crate::pipeline::parsing::module_loader::{self, ModuleGraph, SourceProvider};
use crate::pipeline::path_normalization;
use crate::pipeline::type_checking::{self, CorePrelude};

/// Configuration for a frontend-only analysis run.
#[derive(Debug, Clone, Copy, Default)]
pub struct AnalysisOptions {
    /// Include warnings from the opt-in move checker.
    pub move_check: bool,
}

/// Compiler facts made available to tooling after successful analysis.
#[derive(Debug)]
pub struct Analysis {
    /// Fully typed modules in dependency order.
    pub graph: TypedModuleGraph,
    /// Name-resolution facts, including definition and reference tables.
    pub names: Rc<ResolvedNames>,
    /// Structural binding identities for every lexical binding and value
    /// reference (metel-core#1049). Identity-keyed; carries no source spans.
    pub resolution: ResolutionMap,
    /// Byte-offset → identity index for this snapshot (metel-core#1048). The
    /// only position-keyed structure; rebuilt per analysis, never a semantic
    /// input.
    pub positions: PositionIndex,
    /// The interner used to build `resolution`, for turning a `NameId` back
    /// into a spelling.
    pub name_interner: NameInterner,
    /// Identity for every declared struct field and enum variant
    /// (`FieldId` / `VariantId`), keyed by `(owning SymbolId, member name)`
    /// — the interning milestone of the resolution freeze (metel-core#1051,
    /// ADR-0054 step 3). Field accesses, enum-variant literals, and match
    /// patterns on the typed IR carry the matching id (metel-core#1062 /
    /// #1062b).
    pub members: MemberTable,
    /// Identity for every module namespace, interned from its canonical
    /// (alias-dereferenced) path (metel-core#1070). A module is not a value
    /// binding; module-segment go-to-definition resolves through this, keyed by
    /// `ModuleId`, not a `BindingId`.
    pub modules: ModuleTable,
    /// Non-fatal frontend diagnostics.
    pub warnings: Vec<String>,
    /// Module paths that were skipped rather than typechecked, because a
    /// module they depend on independently failed (metel-core#1045). Always
    /// empty for [`analyze_root_with`]/[`analyze_virtual_root_with`]'s
    /// fail-fast path; only the diagnostics-collecting entry points
    /// ([`analyze_root_with_diagnostics`]/[`analyze_virtual_root_with_diagnostics`])
    /// can produce a non-empty list. `graph` has no `TypedModule` entry for
    /// any of these paths, but `names`/`resolution`/`positions`/`members`/
    /// `modules` still cover them fully -- go-to-definition and
    /// find-references still work; only `hover_at` degrades for them.
    pub skipped_modules: Vec<Vec<String>>,
}

impl Analysis {
    /// The innermost typed expression at a byte offset — hover.
    #[must_use]
    pub fn hover_at(
        &self,
        filename: &str,
        byte_offset: usize,
    ) -> Option<&crate::data::typed_ast::TypedExpr> {
        crate::tooling::query::expr_at(&self.graph, filename, byte_offset)
    }

    /// Where the identifier/path at a byte offset is defined — go-to-definition,
    /// covering lexical locals, module-qualified / imported globals
    /// (metel-core#1050), and module-path segments (metel-core#1070).
    #[must_use]
    pub fn definition_at(
        &self,
        filename: &str,
        byte_offset: usize,
    ) -> Option<crate::tooling::query::DefinitionSite<'_>> {
        crate::tooling::query::definition(
            &self.resolution,
            &self.positions,
            &self.names,
            &self.modules,
            filename,
            byte_offset,
        )
    }

    /// Every use site of the binding at a byte offset — find-references.
    #[must_use]
    pub fn references_at(
        &self,
        filename: &str,
        byte_offset: usize,
    ) -> Vec<&crate::data::ast::Span> {
        crate::tooling::query::references(&self.resolution, &self.positions, filename, byte_offset)
    }
}

/// The result of an editor-oriented analysis attempt.
///
/// Tooling receives diagnostics as data rather than as a `Result` error, so it
/// can publish them for an incomplete document without treating ordinary user
/// mistakes as a server failure. Loading and typechecking each accumulate one
/// diagnostic per independently-failing file/module rather than stopping at
/// the first (metel-core#1045) -- see
/// [`module_loader::load_root_collecting_diagnostics`] and
/// [`crate::pipeline::type_checking::check_graph_collecting_diagnostics`]. Name
/// resolution, path normalization, and coherence checking remain fail-fast,
/// whole-graph, single-diagnostic phases: `diagnostics` holds exactly one
/// entry (and `analysis` is `None`) when one of those fails, since none of
/// them has a natural per-module boundary to recover at. A future parser
/// recovery feature (more than one syntax diagnostic from a single file) is
/// designed for but not implemented here -- see
/// `module_loader::GraphLoadReport`'s own doc.
#[derive(Debug)]
pub struct AnalysisReport {
    /// Analysis facts when the graph's root module loaded and every
    /// whole-graph phase (name resolution, path normalization, coherence)
    /// succeeded. May still be `Some` with `diagnostics` non-empty: a module
    /// elsewhere in the project independently failed to load or typecheck.
    pub analysis: Option<Analysis>,
    /// Source or frontend diagnostics collected during the attempt.
    pub diagnostics: Vec<MetelError>,
}

impl AnalysisReport {
    fn failure(diagnostic: MetelError) -> Self {
        Self {
            analysis: None,
            diagnostics: vec![diagnostic],
        }
    }
}

/// Analyze an on-disk root through `provider` without evaluating it.
///
/// The root path is canonicalized as it is for [`module_loader::load_root_with`].
/// Use [`analyze_virtual_root_with`] for an in-memory root path which need not
/// exist on disk.
///
/// # Errors
/// Returns the first loading, parsing, resolution, coherence, or typechecking
/// error. Editor-oriented diagnostic accumulation is a later layer on top of
/// this stable analysis boundary.
pub fn analyze_root_with<P: SourceProvider>(
    path: impl AsRef<Path>,
    provider: &P,
    options: AnalysisOptions,
) -> Result<Analysis, MetelError> {
    let graph = module_loader::load_root_with(path, provider)?;
    analyze_graph(graph, options)
}

/// Analyze a virtual root through `provider` without evaluating it.
///
/// This is intended for a playground root or an editor buffer. The provider
/// supplies its source; the path is retained for module identity and
/// diagnostics but is not canonicalized or read from disk.
///
/// # Errors
/// Returns the first loading, parsing, resolution, coherence, or typechecking
/// error.
pub fn analyze_virtual_root_with<P: SourceProvider>(
    path: impl AsRef<Path>,
    provider: &P,
    options: AnalysisOptions,
) -> Result<Analysis, MetelError> {
    let graph = module_loader::load_virtual_root_with(path, provider)?;
    analyze_graph(graph, options)
}

/// Analyze an on-disk root and return diagnostics as data for tooling
/// (metel-core#1045).
///
/// The command-line pipeline should continue to use [`analyze_root_with`] and
/// its fail-fast `Result`. This API is for long-lived editor processes, where a
/// malformed source document is expected and must not be reported as a server
/// failure. Unlike `analyze_root_with`, a broken file elsewhere in the project
/// (one that fails to load, or one that fails to typecheck independently of
/// the file being analyzed) does not sink analysis of everything else -- see
/// [`module_loader::load_root_collecting_diagnostics`] and
/// [`crate::pipeline::type_checking::check_graph_collecting_diagnostics`].
#[must_use]
pub fn analyze_root_with_diagnostics<P: SourceProvider>(
    path: impl AsRef<Path>,
    provider: &P,
    options: AnalysisOptions,
) -> AnalysisReport {
    finish_diagnostics(
        module_loader::load_root_collecting_diagnostics(path, provider),
        options,
    )
}

/// Analyze a virtual root and return diagnostics as data for tooling.
///
/// See [`analyze_root_with_diagnostics`] for the collecting behavior this
/// shares.
#[must_use]
pub fn analyze_virtual_root_with_diagnostics<P: SourceProvider>(
    path: impl AsRef<Path>,
    provider: &P,
    options: AnalysisOptions,
) -> AnalysisReport {
    finish_diagnostics(
        module_loader::load_virtual_root_collecting_diagnostics(path, provider),
        options,
    )
}

/// Shared tail of both diagnostics-collecting entry points: decide whether
/// the loaded graph has anything worth analyzing, then run the
/// diagnostics-collecting analysis and merge in the loader's own diagnostics
/// (metel-core#1045).
///
/// `analysis` is `None` iff the graph's own root module (`module_path` empty,
/// the loader's own convention -- see `Loader::load_module`) never made it
/// into the loaded graph, matching `analyze_*_with_diagnostics`'s existing
/// contract for a root document that fails outright (see
/// `virtual_analysis_reports_parse_errors_as_diagnostics` below). A root that
/// *did* load, even with other files elsewhere broken or unloaded, still gets
/// a full `Some(Analysis)`.
fn finish_diagnostics(
    load_report: module_loader::GraphLoadReport,
    options: AnalysisOptions,
) -> AnalysisReport {
    let root_loaded = load_report
        .graph
        .modules
        .iter()
        .any(|m| m.module_path.is_empty());
    if !root_loaded {
        return AnalysisReport {
            analysis: None,
            diagnostics: load_report.diagnostics,
        };
    }

    let mut report = analyze_graph_with_diagnostics(load_report.graph, options);
    // Loader diagnostics are earlier in the pipeline than typecheck ones.
    let mut diagnostics = load_report.diagnostics;
    diagnostics.append(&mut report.diagnostics);
    report.diagnostics = diagnostics;
    report
}

/// Facts derivable from a parsed [`ModuleGraph`] before typechecking even
/// starts: name resolution and every structural identity table. None of this
/// depends on whether typechecking later succeeds (metel-core#1045) -- it's
/// shared verbatim between the fail-fast [`analyze_graph`] and the
/// diagnostics-collecting [`analyze_graph_with_diagnostics`], which differ
/// only in what happens after this point.
struct GraphFacts {
    names: Rc<ResolvedNames>,
    name_interner: NameInterner,
    modules: ModuleTable,
    identity: identity::Allocation,
    members: MemberTable,
}

/// # Errors
/// Returns the first name-resolution error (an unknown import, an export
/// conflict, …). This is the one fail-fast phase shared by both analysis
/// paths -- see `analyze_graph_with_diagnostics`'s own doc for why it, along
/// with path normalization and coherence checking, isn't extended to
/// per-module accumulation the way typechecking is.
fn resolve_graph_facts(graph: &ModuleGraph) -> Result<GraphFacts, MetelError> {
    let names = name_resolver::resolve(graph)?;

    // Structural identities are derived from the parsed graph, so allocate them
    // before `path_normalization::normalize` consumes `graph`.
    let mut name_interner = NameInterner::new();
    let identity_modules: Vec<(Vec<String>, &[crate::data::ast::Decl])> = graph
        .modules
        .iter()
        .map(|module| (module.module_path.clone(), module.program.decls.as_slice()))
        .collect();

    // Intern every module namespace. Its `module_path` is already canonical
    // (the loader keeps one `LoadedModule` per physical file); its location is
    // the module file's start, the go-to-definition target for a module-path
    // segment (metel-core#1070).
    //
    // Interned in canonical (sorted) module-path order, not `graph.modules`'s
    // own load order -- `ModuleTable::intern`'s dense-index allocation is
    // order-of-first-call dependent, so two runs over the identical module
    // set must visit modules in the same order to hand out the same `ModuleId`
    // (metel-core#1048's "regardless of file iteration order" requirement).
    let mut sorted_modules: Vec<&crate::pipeline::parsing::module_loader::LoadedModule> =
        graph.modules.iter().collect();
    sorted_modules.sort_by(|a, b| a.module_path.cmp(&b.module_path));
    let mut modules = ModuleTable::new();
    for module in sorted_modules {
        let file = module.file_path.to_string_lossy().into_owned();
        modules.intern(
            &module.module_path,
            Some(crate::data::ast::Span::new(0, 0, file)),
        );
    }

    let identity = identity::allocate_graph(
        &identity_modules,
        &names,
        &mut name_interner,
        identity::GraphModuleNav {
            table: &modules,
            aliases: &graph.path_aliases,
        },
    );
    let members = identity::collect_members(&identity_modules, &names, &mut name_interner);

    Ok(GraphFacts {
        names,
        name_interner,
        modules,
        identity,
        members,
    })
}

/// Analyze an already-loaded module graph directly, bypassing file discovery.
/// `pub(crate)` so cross-module test fixtures elsewhere in this crate (e.g.
/// `query`'s own multi-module tests, metel-core#1046) can build a `ModuleGraph`
/// by hand -- the same approach `identity`'s own cross-module fixtures use --
/// instead of going through a `SourceProvider` and real file discovery.
pub(crate) fn analyze_graph(
    graph: ModuleGraph,
    options: AnalysisOptions,
) -> Result<Analysis, MetelError> {
    let facts = resolve_graph_facts(&graph)?;
    let normalized = path_normalization::normalize(graph, facts.names.clone())?;
    coherence::check(&normalized)?;
    let report = type_checking::check_graph_with_report(
        &normalized,
        &CorePrelude::default(),
        Some(identity::FrozenIdentity {
            members: &facts.members,
            binding_spans: &facts.identity.binding_spans,
        }),
    )?;

    let mut warnings = report.warnings;
    if options.move_check {
        warnings.extend(move_check::check_graph(&report.graph)?);
    }

    Ok(Analysis {
        graph: report.graph,
        names: facts.names,
        resolution: facts.identity.resolution,
        positions: facts.identity.positions,
        name_interner: facts.name_interner,
        members: facts.members,
        modules: facts.modules,
        warnings,
        skipped_modules: Vec::new(),
    })
}

/// Analyze an already-loaded module graph, collecting diagnostics as data
/// instead of failing fast (metel-core#1045). Always produces `Some(Analysis)`
/// once name resolution, path normalization, and coherence checking all
/// succeed -- those three remain single-diagnostic, whole-graph passes for
/// this MVP (matching the parser phase's own "one diagnostic, skip later
/// phases" scope): none of them has a natural per-module boundary the way the
/// typechecker's `GlobalExports` accumulation already does, and a partial
/// result from any of them (a half-resolved symbol table, a half-normalized
/// path) isn't safely consumable by anything downstream. Only typechecking
/// gets per-module accumulation, via `check_graph_collecting_diagnostics`.
pub(crate) fn analyze_graph_with_diagnostics(
    graph: ModuleGraph,
    options: AnalysisOptions,
) -> AnalysisReport {
    let facts = match resolve_graph_facts(&graph) {
        Ok(facts) => facts,
        Err(e) => return AnalysisReport::failure(e),
    };
    let normalized = match path_normalization::normalize(graph, facts.names.clone()) {
        Ok(normalized) => normalized,
        Err(e) => return AnalysisReport::failure(e),
    };
    if let Err(e) = coherence::check(&normalized) {
        return AnalysisReport::failure(e);
    }

    let report = type_checking::check_graph_collecting_diagnostics(
        &normalized,
        &CorePrelude::default(),
        Some(identity::FrozenIdentity {
            members: &facts.members,
            binding_spans: &facts.identity.binding_spans,
        }),
    );

    let mut warnings = report.warnings;
    let mut diagnostics = report.diagnostics;
    if options.move_check {
        // Runs over whatever modules did type-check; a violation here is one
        // more diagnostic layered on an otherwise-valid partial analysis, not
        // a reason to discard it (unlike the three whole-graph passes above).
        match move_check::check_graph(&report.graph) {
            Ok(mc_warnings) => warnings.extend(mc_warnings),
            Err(e) => diagnostics.push(e),
        }
    }

    AnalysisReport {
        analysis: Some(Analysis {
            graph: report.graph,
            names: facts.names,
            resolution: facts.identity.resolution,
            positions: facts.identity.positions,
            name_interner: facts.name_interner,
            members: facts.members,
            modules: facts.modules,
            warnings,
            skipped_modules: report.skipped,
        }),
        diagnostics,
    }
}

#[cfg(test)]
mod tests;
