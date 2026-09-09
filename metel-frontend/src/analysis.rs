//! Frontend-only analysis API for tooling consumers.
//!
//! Unlike the interpreter pipeline, this module deliberately stops after
//! typechecking. It is the boundary for editor tooling, documentation tools,
//! and other consumers which need compiler facts but must never evaluate user
//! code.

use std::path::Path;

use crate::coherence;
use crate::error::MetelError;
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
    /// Non-fatal frontend diagnostics.
    pub warnings: Vec<String>,
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

fn analyze_graph(graph: ModuleGraph, options: AnalysisOptions) -> Result<Analysis, MetelError> {
    let names = name_resolver::resolve(&graph)?;
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
}
