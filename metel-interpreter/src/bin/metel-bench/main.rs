use std::fs;
use std::path::{Path, PathBuf};

use clap::Parser;
use metel::evaluator::{CallEdgeProfile, EvaluatorProfile, FunctionProfile};
use metel::orchestrator::{
    self, EvaluatorFixturePhaseTimings, EvaluatorFixtureRunReport, RunOptions,
};
use serde::Serialize;

#[derive(Debug, Parser)]
#[command(name = "metel-bench")]
#[command(about = "Benchmark and profile Metel evaluator integration programs")]
struct Args {
    /// Directory containing evaluator integration fixtures.
    #[arg(
        long,
        default_value = "tests/integration/sources/evaluator/integration"
    )]
    fixtures_dir: PathBuf,

    /// Output directory for benchmark and profile artifacts.
    #[arg(long, default_value = "docs/benchmarks/v0.8.2-evaluator-integration")]
    output_dir: PathBuf,

    /// Number of warmup runs before collecting benchmark timings.
    #[arg(long, default_value_t = 1)]
    warmups: usize,

    /// Number of benchmark iterations per fixture.
    #[arg(long, default_value_t = 10)]
    iterations: usize,

    /// Restrict benchmarking to a subset of fixture filenames.
    #[arg(long = "fixture")]
    fixtures: Vec<String>,
}

#[derive(Debug, Serialize)]
struct BenchmarkSuiteSummary {
    fixtures: Vec<FixtureBenchmarkSummary>,
}

#[derive(Debug, Serialize)]
struct FixtureBenchmarkSummary {
    fixture: String,
    benchmark: DurationStats,
    phase_mean_ns: EvaluatorFixturePhaseTimings,
    profile_json: String,
    callgraph_dot: String,
    top_functions: Vec<FunctionProfile>,
    top_edges: Vec<CallEdgeProfile>,
}

#[derive(Debug, Clone, Copy, Serialize)]
struct DurationStats {
    mean_ns: u64,
    min_ns: u64,
    max_ns: u64,
    stddev_ns: f64,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();
    let fixtures = discover_fixtures(&args.fixtures_dir, &args.fixtures)?;
    fs::create_dir_all(&args.output_dir)?;

    let mut summaries = Vec::new();

    for fixture in fixtures {
        let fixture_name = fixture
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("fixture")
            .to_string();

        for _ in 0..args.warmups {
            orchestrator::run_evaluator_fixture(
                fixture.to_string_lossy().as_ref(),
                &RunOptions::default(),
            )?;
        }

        let mut reports = Vec::new();
        for _ in 0..args.iterations {
            reports.push(orchestrator::run_evaluator_fixture(
                fixture.to_string_lossy().as_ref(),
                &RunOptions::default(),
            )?);
        }

        let profile_report = orchestrator::run_evaluator_fixture(
            fixture.to_string_lossy().as_ref(),
            &RunOptions {
                collect_evaluator_profile: true,
                ..RunOptions::default()
            },
        )?;
        let profile = profile_report
            .evaluation
            .profile
            .clone()
            .unwrap_or_default();

        let summary = FixtureBenchmarkSummary {
            fixture: fixture_name.clone(),
            benchmark: duration_stats(
                &reports
                    .iter()
                    .map(|report| report.phase_timings.total_ns)
                    .collect::<Vec<_>>(),
            ),
            phase_mean_ns: mean_phase_timings(&reports),
            profile_json: format!("{fixture_name}.profile.json"),
            callgraph_dot: format!("{fixture_name}.callgraph.dot"),
            top_functions: top_functions(&profile, 10),
            top_edges: top_edges(&profile, 10),
        };

        write_profile_artifacts(&args.output_dir, &fixture_name, &profile)?;
        summaries.push(summary);
    }

    let suite = BenchmarkSuiteSummary {
        fixtures: summaries,
    };
    fs::write(
        args.output_dir.join("summary.json"),
        serde_json::to_vec_pretty(&suite)?,
    )?;
    fs::write(args.output_dir.join("summary.md"), render_markdown(&suite))?;

    Ok(())
}

fn discover_fixtures(
    fixtures_dir: &Path,
    selected: &[String],
) -> Result<Vec<PathBuf>, Box<dyn std::error::Error>> {
    let mut fixtures = fs::read_dir(fixtures_dir)?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("mtl"))
        .collect::<Vec<_>>();
    fixtures.sort();

    if selected.is_empty() {
        return Ok(fixtures);
    }

    let mut filtered = fixtures
        .into_iter()
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| selected.iter().any(|selected| selected == name))
        })
        .collect::<Vec<_>>();
    filtered.sort();
    Ok(filtered)
}

fn write_profile_artifacts(
    output_dir: &Path,
    fixture_name: &str,
    profile: &EvaluatorProfile,
) -> Result<(), Box<dyn std::error::Error>> {
    fs::write(
        output_dir.join(format!("{fixture_name}.profile.json")),
        serde_json::to_vec_pretty(profile)?,
    )?;
    fs::write(
        output_dir.join(format!("{fixture_name}.callgraph.dot")),
        render_callgraph_dot(profile),
    )?;
    Ok(())
}

fn mean_phase_timings(reports: &[EvaluatorFixtureRunReport]) -> EvaluatorFixturePhaseTimings {
    let count = reports.len() as u64;
    let mut mean = EvaluatorFixturePhaseTimings::default();
    for report in reports {
        mean.parse_ns += report.phase_timings.parse_ns;
        mean.typecheck_ns += report.phase_timings.typecheck_ns;
        mean.typecheck_detail.registry_ns += report.phase_timings.typecheck_detail.registry_ns;
        mean.typecheck_detail.inference_ns += report.phase_timings.typecheck_detail.inference_ns;
        mean.typecheck_detail.solve_ns += report.phase_timings.typecheck_detail.solve_ns;
        mean.typecheck_detail.scheme_env_ns += report.phase_timings.typecheck_detail.scheme_env_ns;
        mean.typecheck_detail.construction_ns +=
            report.phase_timings.typecheck_detail.construction_ns;
        mean.typecheck_detail.finalize_ns += report.phase_timings.typecheck_detail.finalize_ns;
        mean.typecheck_detail.solve_calls += report.phase_timings.typecheck_detail.solve_calls;
        mean.typecheck_detail.constraints_processed +=
            report.phase_timings.typecheck_detail.constraints_processed;
        mean.evaluate_ns += report.phase_timings.evaluate_ns;
        mean.total_ns += report.phase_timings.total_ns;
    }
    mean.parse_ns /= count;
    mean.typecheck_ns /= count;
    mean.typecheck_detail.registry_ns /= count;
    mean.typecheck_detail.inference_ns /= count;
    mean.typecheck_detail.solve_ns /= count;
    mean.typecheck_detail.scheme_env_ns /= count;
    mean.typecheck_detail.construction_ns /= count;
    mean.typecheck_detail.finalize_ns /= count;
    mean.typecheck_detail.solve_calls /= count;
    mean.typecheck_detail.constraints_processed /= count;
    mean.evaluate_ns /= count;
    mean.total_ns /= count;
    mean
}

fn duration_stats(samples: &[u64]) -> DurationStats {
    let count = samples.len() as f64;
    let mean = samples.iter().sum::<u64>() as f64 / count;
    let variance = samples
        .iter()
        .map(|sample| {
            let delta = *sample as f64 - mean;
            delta * delta
        })
        .sum::<f64>()
        / count;

    DurationStats {
        mean_ns: mean.round() as u64,
        min_ns: *samples.iter().min().unwrap_or(&0),
        max_ns: *samples.iter().max().unwrap_or(&0),
        stddev_ns: variance.sqrt(),
    }
}

fn top_functions(profile: &EvaluatorProfile, limit: usize) -> Vec<FunctionProfile> {
    let mut functions = profile.functions.clone();
    functions.sort_by(|lhs, rhs| {
        rhs.inclusive_ns
            .cmp(&lhs.inclusive_ns)
            .then(lhs.function.cmp(&rhs.function))
    });
    functions.truncate(limit);
    functions
}

fn top_edges(profile: &EvaluatorProfile, limit: usize) -> Vec<CallEdgeProfile> {
    let mut edges = profile.edges.clone();
    edges.sort_by(|lhs, rhs| {
        rhs.inclusive_ns
            .cmp(&lhs.inclusive_ns)
            .then(lhs.callee.cmp(&rhs.callee))
    });
    edges.truncate(limit);
    edges
}

fn render_markdown(summary: &BenchmarkSuiteSummary) -> String {
    let mut out = String::new();
    out.push_str("# Evaluator Integration Benchmark Summary\n\n");
    out.push_str(
        "| Fixture | Mean (ms) | Min (ms) | Max (ms) | Stddev (ms) | Evaluate Phase (ms) |\n",
    );
    out.push_str("|---|---:|---:|---:|---:|---:|\n");
    for fixture in &summary.fixtures {
        out.push_str(&format!(
            "| {} | {:.3} | {:.3} | {:.3} | {:.3} | {:.3} |\n",
            fixture.fixture,
            ns_to_ms(fixture.benchmark.mean_ns),
            ns_to_ms(fixture.benchmark.min_ns),
            ns_to_ms(fixture.benchmark.max_ns),
            ns_to_ms_f64(fixture.benchmark.stddev_ns),
            ns_to_ms(fixture.phase_mean_ns.evaluate_ns),
        ));
    }

    for fixture in &summary.fixtures {
        out.push_str(&format!("\n## {}\n\n", fixture.fixture));
        out.push_str("### Phase Mean Timings\n\n");
        out.push_str("| Phase | Mean (ms) |\n|---|---:|\n");
        out.push_str(&format!(
            "| parse | {:.3} |\n",
            ns_to_ms(fixture.phase_mean_ns.parse_ns)
        ));
        out.push_str(&format!(
            "| typecheck | {:.3} |\n",
            ns_to_ms(fixture.phase_mean_ns.typecheck_ns)
        ));
        out.push_str(&format!(
            "| evaluate | {:.3} |\n",
            ns_to_ms(fixture.phase_mean_ns.evaluate_ns)
        ));
        out.push_str(&format!(
            "| total | {:.3} |\n",
            ns_to_ms(fixture.phase_mean_ns.total_ns)
        ));

        out.push_str("\n### Typechecker Sub-Phases\n\n");
        out.push_str("| Sub-phase | Mean (ms) |\n|---|---:|\n");
        out.push_str(&format!(
            "| registry | {:.3} |\n",
            ns_to_ms(fixture.phase_mean_ns.typecheck_detail.registry_ns)
        ));
        out.push_str(&format!(
            "| inference | {:.3} |\n",
            ns_to_ms(fixture.phase_mean_ns.typecheck_detail.inference_ns)
        ));
        out.push_str(&format!(
            "| solve | {:.3} |\n",
            ns_to_ms(fixture.phase_mean_ns.typecheck_detail.solve_ns)
        ));
        out.push_str(&format!(
            "| scheme_env | {:.3} |\n",
            ns_to_ms(fixture.phase_mean_ns.typecheck_detail.scheme_env_ns)
        ));
        out.push_str(&format!(
            "| construction | {:.3} |\n",
            ns_to_ms(fixture.phase_mean_ns.typecheck_detail.construction_ns)
        ));
        out.push_str(&format!(
            "| finalize | {:.3} |\n",
            ns_to_ms(fixture.phase_mean_ns.typecheck_detail.finalize_ns)
        ));
        out.push_str(&format!(
            "\nTypechecker counters: `solve_calls={}`, `constraints_processed={}`\n",
            fixture.phase_mean_ns.typecheck_detail.solve_calls,
            fixture.phase_mean_ns.typecheck_detail.constraints_processed,
        ));

        out.push_str("\n### Hottest Functions\n\n");
        out.push_str("| Function | Calls | Inclusive (ms) | Self (ms) |\n|---|---:|---:|---:|\n");
        for function in &fixture.top_functions {
            out.push_str(&format!(
                "| {} | {} | {:.3} | {:.3} |\n",
                function.function,
                function.calls,
                ns_to_ms(function.inclusive_ns),
                ns_to_ms(function.self_ns),
            ));
        }

        out.push_str("\n### Hottest Edges\n\n");
        out.push_str("| Caller | Callee | Calls | Inclusive (ms) |\n|---|---|---:|---:|\n");
        for edge in &fixture.top_edges {
            out.push_str(&format!(
                "| {} | {} | {} | {:.3} |\n",
                edge.caller.as_deref().unwrap_or("<entry>"),
                edge.callee,
                edge.calls,
                ns_to_ms(edge.inclusive_ns),
            ));
        }

        out.push_str(&format!(
            "\nArtifacts: `{}`, `{}`\n",
            fixture.profile_json, fixture.callgraph_dot
        ));
    }

    out
}

fn render_callgraph_dot(profile: &EvaluatorProfile) -> String {
    let mut out = String::from("digraph metel_callgraph {\n  rankdir=LR;\n");
    for function in &profile.functions {
        out.push_str(&format!(
            "  \"{}\" [label=\"{}\\ncalls={}\\ninclusive={:.3}ms\\nself={:.3}ms\"];\n",
            escape_dot(&function.function),
            escape_dot(&function.function),
            function.calls,
            ns_to_ms(function.inclusive_ns),
            ns_to_ms(function.self_ns),
        ));
    }
    for edge in &profile.edges {
        let caller = edge.caller.as_deref().unwrap_or("<entry>");
        out.push_str(&format!(
            "  \"{}\" -> \"{}\" [label=\"calls={}\\ninclusive={:.3}ms\"];\n",
            escape_dot(caller),
            escape_dot(&edge.callee),
            edge.calls,
            ns_to_ms(edge.inclusive_ns),
        ));
    }
    out.push_str("}\n");
    out
}

fn escape_dot(input: &str) -> String {
    input.replace('\\', "\\\\").replace('"', "\\\"")
}

fn ns_to_ms(ns: u64) -> f64 {
    ns as f64 / 1_000_000.0
}

fn ns_to_ms_f64(ns: f64) -> f64 {
    ns / 1_000_000.0
}

#[cfg(test)]
mod tests;
