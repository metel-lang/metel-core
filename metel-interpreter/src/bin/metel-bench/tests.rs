use super::*;

#[test]
fn duration_stats_computes_mean_min_max() {
    let stats = duration_stats(&[10, 20, 30]);
    assert_eq!(stats.mean_ns, 20);
    assert_eq!(stats.min_ns, 10);
    assert_eq!(stats.max_ns, 30);
    assert!(stats.stddev_ns > 0.0);
}

#[test]
fn render_callgraph_dot_includes_edges() {
    let profile = EvaluatorProfile {
        functions: vec![FunctionProfile {
            function: "main".to_string(),
            calls: 1,
            inclusive_ns: 1_000_000,
            self_ns: 500_000,
        }],
        edges: vec![CallEdgeProfile {
            caller: None,
            callee: "main".to_string(),
            calls: 1,
            inclusive_ns: 1_000_000,
        }],
    };

    let dot = render_callgraph_dot(&profile);
    assert!(dot.contains("\"<entry>\" -> \"main\""));
    assert!(dot.contains("calls=1"));
}

#[test]
fn mean_phase_timings_averages_after_summing() {
    let reports = vec![
        EvaluatorFixtureRunReport {
            phase_timings: EvaluatorFixturePhaseTimings {
                parse_ns: 1,
                typecheck_ns: 7,
                typecheck_detail: Default::default(),
                evaluate_ns: 11,
                total_ns: 13,
            },
            evaluation: Default::default(),
            warnings: Vec::new(),
        },
        EvaluatorFixtureRunReport {
            phase_timings: EvaluatorFixturePhaseTimings {
                parse_ns: 2,
                typecheck_ns: 8,
                typecheck_detail: Default::default(),
                evaluate_ns: 12,
                total_ns: 14,
            },
            evaluation: Default::default(),
            warnings: Vec::new(),
        },
    ];

    let mean = mean_phase_timings(&reports);
    assert_eq!(mean.parse_ns, 1);
    assert_eq!(mean.typecheck_ns, 7);
    assert_eq!(mean.evaluate_ns, 11);
    assert_eq!(mean.total_ns, 13);
}
