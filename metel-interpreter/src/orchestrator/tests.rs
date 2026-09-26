use super::*;

#[test]
fn run_source_evaluates_a_virtual_single_file_program() {
    let report = run_source("fun main() {}", &RunOptions::default())
        .expect("an in-memory program should run through the full pipeline");

    assert!(report.warnings.is_empty());
}
