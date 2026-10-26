use super::*;

#[test]
fn run_source_evaluates_a_virtual_single_file_program() {
    let report = run_source("fun main() {}", &RunOptions::default())
        .expect("an in-memory program should run through the full pipeline");

    assert!(report.warnings.is_empty());
}

/// The message of the error `source` produces.
fn error_message(source: &str) -> String {
    run_source(source, &RunOptions::default())
        .expect_err("the program should be rejected")
        .to_string()
}

// RFC-0184, spec.types.perhaps-t.legality-2: the removed name says what it became.
#[test]
fn the_removed_perhaps_name_says_it_is_now_option() {
    let message = error_message("fun f(x: Perhaps<i64>) -> i64 { 0 }\nfun main() {}");
    assert!(message.contains("`Perhaps` is now `Option`"), "{message}");
}

// A module that declares its own `Perhaps` is unaffected: the name resolves there, so a
// different mistake (a variant that does not exist) must not be blamed on the rename.
#[test]
fn a_users_own_perhaps_gets_no_rename_hint() {
    let message = error_message("enum Perhaps { Maybe }\nfun main() { let a := Perhaps::Zed; }");
    assert!(message.contains("Perhaps::Zed"), "{message}");
    assert!(!message.contains("is now"), "{message}");
}

// The same holds for a type declared inside a block.
#[test]
fn a_block_local_perhaps_gets_no_rename_hint() {
    let message =
        error_message("fun main() {\n    enum Perhaps { Maybe }\n    let a := Perhaps::Zed;\n}");
    assert!(!message.contains("is now"), "{message}");
}

// A path that merely ends in `Perhaps` is another module's business, not the core type's.
#[test]
fn a_path_ending_in_perhaps_gets_no_rename_hint() {
    let message = error_message("fun main() { let a := other::Perhaps::None; }");
    assert!(!message.contains("is now"), "{message}");
}
