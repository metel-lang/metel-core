//! Frontend-only analysis API for tooling consumers.
//!
//! Unlike the interpreter pipeline, this module deliberately stops after
//! typechecking. It is the boundary for editor tooling, documentation tools,
//! and other consumers which need compiler facts but must never evaluate user
//! code.

use std::path::Path;

use crate::coherence;
use crate::error::MetelError;
use crate::identity::{self, MemberTable, NameInterner, PositionIndex, ResolutionMap};
use crate::module_loader::{self, ModuleGraph, SourceProvider};
use crate::move_check;
use crate::name_resolver::{self, ResolvedNames};
use crate::path_normalizer;
use crate::typechecker::{self, CorePrelude};
use crate::typed_ast::TypedModuleGraph;

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
    pub names: ResolvedNames,
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
    /// ADR-0054 step 3). Not yet threaded onto the typed IR.
    pub members: MemberTable,
    /// Non-fatal frontend diagnostics.
    pub warnings: Vec<String>,
}

impl Analysis {
    /// The innermost typed expression at a byte offset — hover.
    #[must_use]
    pub fn hover_at(
        &self,
        filename: &str,
        byte_offset: usize,
    ) -> Option<&crate::typed_ast::TypedExpr> {
        crate::query::expr_at(&self.graph, filename, byte_offset)
    }

    /// Where the identifier/path at a byte offset is defined — go-to-definition,
    /// covering lexical locals and module-qualified / imported globals
    /// (metel-core#1050).
    #[must_use]
    pub fn definition_at(
        &self,
        filename: &str,
        byte_offset: usize,
    ) -> Option<crate::query::DefinitionSite<'_>> {
        crate::query::definition(
            &self.resolution,
            &self.positions,
            &self.names,
            filename,
            byte_offset,
        )
    }

    /// Every use site of the binding at a byte offset — find-references.
    #[must_use]
    pub fn references_at(&self, filename: &str, byte_offset: usize) -> Vec<&crate::ast::Span> {
        crate::query::references(&self.resolution, &self.positions, filename, byte_offset)
    }
}

/// The result of an editor-oriented analysis attempt.
///
/// Tooling receives diagnostics as data rather than as a `Result` error, so it
/// can publish them for an incomplete document without treating ordinary user
/// mistakes as a server failure. The initial frontend remains fail-fast within
/// a phase: the list contains the first blocking diagnostic. Parser recovery
/// and multi-error typechecking can extend this representation without changing
/// its callers.
#[derive(Debug)]
pub struct AnalysisReport {
    /// Analysis facts when every blocking frontend phase succeeded.
    pub analysis: Option<Analysis>,
    /// Source or frontend diagnostics collected during the attempt.
    pub diagnostics: Vec<MetelError>,
}

impl AnalysisReport {
    fn success(analysis: Analysis) -> Self {
        Self {
            analysis: Some(analysis),
            diagnostics: Vec::new(),
        }
    }

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

/// Analyze an on-disk root and return diagnostics as data for tooling.
///
/// The command-line pipeline should continue to use [`analyze_root_with`] and
/// its fail-fast `Result`. This API is for long-lived editor processes, where a
/// malformed source document is expected and must not be reported as a server
/// failure.
#[must_use]
pub fn analyze_root_with_diagnostics<P: SourceProvider>(
    path: impl AsRef<Path>,
    provider: &P,
    options: AnalysisOptions,
) -> AnalysisReport {
    match analyze_root_with(path, provider, options) {
        Ok(analysis) => AnalysisReport::success(analysis),
        Err(diagnostic) => AnalysisReport::failure(diagnostic),
    }
}

/// Analyze a virtual root and return diagnostics as data for tooling.
///
/// See [`analyze_root_with_diagnostics`] for the initial fail-fast collection
/// boundary and its intended extension path.
#[must_use]
pub fn analyze_virtual_root_with_diagnostics<P: SourceProvider>(
    path: impl AsRef<Path>,
    provider: &P,
    options: AnalysisOptions,
) -> AnalysisReport {
    match analyze_virtual_root_with(path, provider, options) {
        Ok(analysis) => AnalysisReport::success(analysis),
        Err(diagnostic) => AnalysisReport::failure(diagnostic),
    }
}

fn analyze_graph(graph: ModuleGraph, options: AnalysisOptions) -> Result<Analysis, MetelError> {
    let names = name_resolver::resolve(&graph)?;

    // Structural identities are derived from the parsed graph, so allocate them
    // before `path_normalizer::normalize` consumes `graph`.
    let mut name_interner = NameInterner::new();
    let identity_modules: Vec<(Vec<String>, &[crate::ast::Decl])> = graph
        .modules
        .iter()
        .map(|module| (module.module_path.clone(), module.program.decls.as_slice()))
        .collect();
    let identity = identity::allocate_graph(&identity_modules, &names, &mut name_interner);
    let members = identity::collect_members(&identity_modules, &names, &mut name_interner);

    let normalized = path_normalizer::normalize(graph, &names)?;
    coherence::check(&normalized, &names)?;
    let report =
        typechecker::check_graph_with_report(&normalized, &names, &CorePrelude::default())?;

    let mut warnings = report.warnings;
    if options.move_check {
        warnings.extend(move_check::check_graph(&report.graph)?);
    }

    Ok(Analysis {
        graph: report.graph,
        names,
        resolution: identity.resolution,
        positions: identity.positions,
        name_interner,
        members,
        warnings,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module_loader::InMemorySourceProvider;

    #[test]
    fn virtual_analysis_returns_typed_modules_without_evaluation() {
        let provider = InMemorySourceProvider::new("editor.mtl", "fun main() {}");
        let analysis =
            analyze_virtual_root_with("editor.mtl", &provider, AnalysisOptions::default())
                .expect("an in-memory program should be analyzable");

        assert!(analysis
            .graph
            .modules
            .iter()
            .any(|module| module.module_path.is_empty()));
        assert!(analysis.warnings.is_empty());
    }

    #[test]
    fn virtual_analysis_reports_parse_errors_as_diagnostics() {
        let provider = InMemorySourceProvider::new("editor.mtl", "fun main(");
        let report = analyze_virtual_root_with_diagnostics(
            "editor.mtl",
            &provider,
            AnalysisOptions::default(),
        );

        assert!(report.analysis.is_none());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0]
                .primary_span()
                .expect("parse error should be located")
                .filename,
            "editor.mtl"
        );
    }
}
