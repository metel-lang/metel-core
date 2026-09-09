use std::time::Instant;

use serde::Serialize;

use crate::coherence;
use crate::elaborator;
use crate::error::MetelError;
use crate::evaluator::{self, EvaluationReport};
use crate::module_loader;
use crate::move_check;
use crate::name_resolver;
use crate::path_normalizer;
use crate::typechecker::{self, CorePrelude, TypecheckPhaseTimings};

#[derive(Debug, Clone, Default)]
pub struct RunOptions {
    pub collect_evaluator_profile: bool,
    pub move_check: bool,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct PhaseTimings {
    pub load_root_ns: u64,
    pub resolve_ns: u64,
    pub normalize_ns: u64,
    pub coherence_ns: u64,
    pub typecheck_ns: u64,
    pub elaborate_ns: u64,
    pub evaluate_ns: u64,
    pub total_ns: u64,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct RunReport {
    pub phase_timings: PhaseTimings,
    pub evaluation: EvaluationReport,
    pub warnings: Vec<String>,
}

#[allow(dead_code)] // public API used by the benchmark binary
#[derive(Debug, Clone, Default, Serialize)]
pub struct EvaluatorFixturePhaseTimings {
    pub parse_ns: u64,
    pub typecheck_ns: u64,
    pub typecheck_detail: TypecheckPhaseTimings,
    pub evaluate_ns: u64,
    pub total_ns: u64,
}

#[allow(dead_code)] // public API used by the benchmark binary
#[derive(Debug, Clone, Default, Serialize)]
pub struct EvaluatorFixtureRunReport {
    pub phase_timings: EvaluatorFixturePhaseTimings,
    pub evaluation: EvaluationReport,
    pub warnings: Vec<String>,
}

/// Run the full pipeline (load, resolve, normalize, coherence, typecheck,
/// elaborate, evaluate) over the module rooted at `filename`.
///
/// # Errors
/// Returns an error if any pipeline phase fails: module loading, name
/// resolution, path normalization, coherence checking, typechecking, or
/// evaluation.
pub fn run_file(filename: &str, options: &RunOptions) -> Result<RunReport, MetelError> {
    let total_started = Instant::now();

    let started = Instant::now();
    let graph = module_loader::load_root(filename)?;
    let load_root_ns = elapsed_ns(started);

    let started = Instant::now();
    let names = name_resolver::resolve(&graph)?;
    let resolve_ns = elapsed_ns(started);

    let started = Instant::now();
    let normalized = path_normalizer::normalize(graph, &names)?;
    let normalize_ns = elapsed_ns(started);

    let started = Instant::now();
    coherence::check(&normalized, &names)?;
    let coherence_ns = elapsed_ns(started);

    let started = Instant::now();
    let typed_report =
        typechecker::check_graph_with_report(&normalized, &names, &CorePrelude::default())?;
    let typecheck_ns = elapsed_ns(started);

    let mut warnings = typed_report.warnings;
    if options.move_check {
        warnings.extend(move_check::check_graph(&typed_report.graph)?);
    }

    let started = Instant::now();
    let elaborated = elaborator::elaborate(typed_report.graph, &names)?;
    let elaborate_ns = elapsed_ns(started);

    let started = Instant::now();
    let evaluation = evaluator::evaluate_graph_with_options(
        elaborated,
        evaluator::EvaluationOptions {
            collect_profile: options.collect_evaluator_profile,
        },
    )?;
    let evaluate_ns = elapsed_ns(started);

    Ok(RunReport {
        phase_timings: PhaseTimings {
            load_root_ns,
            resolve_ns,
            normalize_ns,
            coherence_ns,
            typecheck_ns,
            elaborate_ns,
            evaluate_ns,
            total_ns: elapsed_ns(total_started),
        },
        evaluation,
        warnings,
    })
}

/// Run the full pipeline over one in-memory source string.
///
/// The source is rooted at the stable virtual path `playground.mtl`. It can
/// import binary-embedded `std::` modules, but the single-file provider never
/// falls through to the filesystem for user modules.
///
/// # Errors
/// Returns an error if parsing, name resolution, typechecking, or evaluation
/// fails.
pub fn run_source(source: &str, options: &RunOptions) -> Result<RunReport, MetelError> {
    let total_started = Instant::now();
    let root = "playground.mtl";
    let provider = module_loader::InMemorySourceProvider::new(root, source);

    let started = Instant::now();
    let graph = module_loader::load_virtual_root_with(root, &provider)?;
    let load_root_ns = elapsed_ns(started);

    let started = Instant::now();
    let names = name_resolver::resolve(&graph)?;
    let resolve_ns = elapsed_ns(started);

    let started = Instant::now();
    let normalized = path_normalizer::normalize(graph, &names)?;
    let normalize_ns = elapsed_ns(started);

    let started = Instant::now();
    coherence::check(&normalized, &names)?;
    let coherence_ns = elapsed_ns(started);

    let started = Instant::now();
    let typed_report =
        typechecker::check_graph_with_report(&normalized, &names, &CorePrelude::default())?;
    let typecheck_ns = elapsed_ns(started);

    let mut warnings = typed_report.warnings;
    if options.move_check {
        warnings.extend(move_check::check_graph(&typed_report.graph)?);
    }

    let started = Instant::now();
    let elaborated = elaborator::elaborate(typed_report.graph, &names)?;
    let elaborate_ns = elapsed_ns(started);

    let started = Instant::now();
    let evaluation = evaluator::evaluate_graph_with_options(
        elaborated,
        evaluator::EvaluationOptions {
            collect_profile: options.collect_evaluator_profile,
        },
    )?;
    let evaluate_ns = elapsed_ns(started);

    Ok(RunReport {
        phase_timings: PhaseTimings {
            load_root_ns,
            resolve_ns,
            normalize_ns,
            coherence_ns,
            typecheck_ns,
            elaborate_ns,
            evaluate_ns,
            total_ns: elapsed_ns(total_started),
        },
        evaluation,
        warnings,
    })
}

/// Run a single evaluator fixture through the full module pipeline (the same path
/// the shipped binary uses), reporting evaluator-focused phase timings for the
/// benchmark binary.
///
/// `parse_ns` here covers load + resolve + normalize (the front end), `typecheck_ns`
/// covers type-checking + elaboration, and `evaluate_ns` the graph evaluation.
/// Previously this used the single-program path (`check_with_ctx`); that path was
/// removed once the `SymbolId` migration made it the sole remaining surface-name
/// consumer (METEL-185 / ADR-0041), so the bench now matches the product path.
#[allow(dead_code)] // public API used by the benchmark binary
/// # Errors
/// Returns an error if any pipeline phase fails: module loading, name
/// resolution, path normalization, typechecking, or evaluation.
pub fn run_evaluator_fixture(
    filename: &str,
    options: &RunOptions,
) -> Result<EvaluatorFixtureRunReport, MetelError> {
    let total_started = Instant::now();

    let started = Instant::now();
    let graph = module_loader::load_root(filename)?;
    let names = name_resolver::resolve(&graph)?;
    let normalized = path_normalizer::normalize(graph, &names)?;
    coherence::check(&normalized, &names)?;
    let parse_ns = elapsed_ns(started);

    let started = Instant::now();
    let typed_report =
        typechecker::check_graph_with_report(&normalized, &names, &CorePrelude::default())?;

    let mut warnings = typed_report.warnings;
    if options.move_check {
        warnings.extend(move_check::check_graph(&typed_report.graph)?);
    }

    let elaborated = elaborator::elaborate(typed_report.graph, &names)?;
    let typecheck_ns = elapsed_ns(started);

    let started = Instant::now();
    let evaluation = evaluator::evaluate_graph_with_options(
        elaborated,
        evaluator::EvaluationOptions {
            collect_profile: options.collect_evaluator_profile,
        },
    )?;
    let evaluate_ns = elapsed_ns(started);

    Ok(EvaluatorFixtureRunReport {
        phase_timings: EvaluatorFixturePhaseTimings {
            parse_ns,
            typecheck_ns,
            typecheck_detail: typed_report.timings,
            evaluate_ns,
            total_ns: elapsed_ns(total_started),
        },
        evaluation,
        warnings,
    })
}

fn elapsed_ns(started: Instant) -> u64 {
    started.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn run_source_evaluates_a_virtual_single_file_program() {
        let report = run_source("fun main() {}", &RunOptions::default())
            .expect("an in-memory program should run through the full pipeline");

        assert!(report.warnings.is_empty());
    }
}
