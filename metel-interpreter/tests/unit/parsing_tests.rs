use metel::data::ast::{ImportTree, PathRoot};
use metel::pipeline::parsing::parser;

// Most of this file's former tests exercised *observable* parser behavior
// (does source X parse, does source Y produce a P0001/P0002 with a given
// code/line/col) and have been rewritten as real `.mtl`/`.toml` integration
// fixtures under `tests/integration/sources/parsing/`, which verify the same
// claims through the real parser entry point the shipped binary uses, not a
// direct Rust-level `parser::parse` call. See ADR-0049.
//
// The two tests below stay here because they have no fixture-level
// equivalent: one inspects the parsed `Program`'s AST fields directly (an
// import tree's roots/aliases/groups/globs -- the integration harness's
// `[program]` sidecar checks only expose coarse import/decl *counts*, not
// tree shape), and the other asserts a *negative* string property (a message
// must NOT contain something), which the harness's `expect.contains` can't
// express.

#[test]
fn module_ast_preserves_roots_aliases_groups_and_globs() {
    let source = r#"
import std::math;
import root::parser::Ast;
import root::v1::Parser as ParserV1;
import root::v2::{Parser as ParserV2, Token};
import root::prelude::*;

export ast::Ast;

fun main() { }
"#;
    let program = parser::parse(source, "module_ast.mtl").unwrap_or_else(|e| panic!("{e}"));

    assert_eq!(program.imports.len(), 5);
    assert_eq!(program.exports.len(), 1);

    assert_eq!(program.imports[0].path.root, PathRoot::Std);
    assert_eq!(
        program.imports[0].path.tree,
        ImportTree::Name {
            name: "math".to_string(),
            alias: None
        }
    );

    assert_eq!(program.imports[1].path.root, PathRoot::Root);
    assert_eq!(
        program.imports[1].path.tree,
        ImportTree::Path {
            name: "parser".to_string(),
            tree: Box::new(ImportTree::Name {
                name: "Ast".to_string(),
                alias: None
            }),
        }
    );

    assert_eq!(
        program.imports[2].path.tree,
        ImportTree::Path {
            name: "v1".to_string(),
            tree: Box::new(ImportTree::Name {
                name: "Parser".to_string(),
                alias: Some("ParserV1".to_string()),
            }),
        }
    );

    assert_eq!(
        program.imports[3].path.tree,
        ImportTree::Path {
            name: "v2".to_string(),
            tree: Box::new(ImportTree::Group(vec![
                ImportTree::Name {
                    name: "Parser".to_string(),
                    alias: Some("ParserV2".to_string()),
                },
                ImportTree::Name {
                    name: "Token".to_string(),
                    alias: None
                },
            ])),
        }
    );

    assert_eq!(
        program.imports[4].path.tree,
        ImportTree::Path {
            name: "prelude".to_string(),
            tree: Box::new(ImportTree::Glob)
        }
    );

    assert_eq!(
        program.exports[0].path.root,
        PathRoot::Name("ast".to_string())
    );
    assert_eq!(
        program.exports[0].path.tree,
        ImportTree::Name {
            name: "Ast".to_string(),
            alias: None
        }
    );
}

fn parse_error_message(filename: &str) -> String {
    let path = format!("tests/integration/sources/parsing/{filename}");
    let source =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("could not read {}: {}", path, e));
    match parser::parse(&source, filename) {
        Err(e) => format!("{e}"),
        Ok(_) => panic!("expected a parse error from {filename} but parsing succeeded"),
    }
}

#[test]
fn error_format_p0001_does_not_contain_raw_byte_offset() {
    let msg = parse_error_message("neg_01_syntax_error.mtl");
    assert!(
        !msg.contains(".."),
        "message should not contain '..' (raw byte range), got: {msg}"
    );
}
