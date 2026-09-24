// See src/lib.rs for the rationale — this binary target re-declares the same
// modules as a separate crate root, so the same crate-level allow is needed
// here too.
#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss,
    clippy::cast_possible_wrap,
    clippy::cast_lossless
)]

use std::process;

use clap::Parser;

use metel::data::error::MetelError;
use metel::orchestrator;
use metel::pipeline::parsing::module_loader;

#[derive(Parser)]
#[command(name = "metel")]
#[command(version)]
#[command(about = "Metel interpreter")]
#[command(long_about = "A tree-walk interpreter for the metel programming language")]
struct Args {
    /// Path to the \.mtl file to execute
    #[arg(value_name = "FILE")]
    file: String,

    /// Print the AST and exit without executing
    #[arg(long)]
    debug_ast: bool,

    /// Reject use-after-move (RFC-0071, issue #291)
    ///
    /// Off by default: the checker is complete but the existing corpus is
    /// written in a style affine ownership rejects, and that migration is
    /// tracked separately. Opt in to run it against your own code.
    #[arg(long)]
    move_check: bool,
}

fn main() {
    let args = Args::parse();

    if let Err(e) = run(&args.file, args.debug_ast, args.move_check) {
        eprintln!("{}", e);
        process::exit(1);
    }
}

fn run(filename: &str, debug_ast: bool, move_check: bool) -> Result<(), MetelError> {
    if !debug_ast {
        let report = orchestrator::run_file(
            filename,
            &orchestrator::RunOptions {
                move_check,
                ..orchestrator::RunOptions::default()
            },
        )?;
        for warning in report.warnings {
            eprintln!("warning: {warning}");
        }
        return Ok(());
    }

    // 1. Load modules
    let graph = module_loader::load_root(filename)?;

    if debug_ast {
        for m in graph.modules.iter() {
            println!("=== {:?} ===\n{:#?}", m.module_path, m.program);
        }
        return Ok(());
    }
    Ok(())
}
