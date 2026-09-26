use super::*;
use crate::data::ast::{
    Block, Decl, FunDecl, ImportDecl, ImportPath, ImportTree, PathRoot, Program, Span, Visibility,
};
use crate::pipeline::parsing::module_loader::{LoadedModule, ModuleGraph};
use std::path::PathBuf;

fn span() -> Span {
    Span::new(0, 0, "test")
}

fn make_import(root: PathRoot, tree: ImportTree) -> ImportDecl {
    ImportDecl {
        path: ImportPath { root, tree },
        span: span(),
    }
}

fn make_program(imports: Vec<ImportDecl>) -> Program {
    Program {
        imports,
        exports: vec![],
        decls: vec![],
    }
}

fn make_program_with_pubs(imports: Vec<ImportDecl>, pub_names: &[&str]) -> Program {
    let decls = pub_names
        .iter()
        .map(|n| {
            Decl::Fun(FunDecl {
                visibility: Visibility::Public,
                name: (*n).into(),
                generics: vec![],
                where_clause: None,
                params: vec![],
                return_type: None,
                native: None,
                body: Block {
                    stmts: vec![],
                    tail: None,
                    span: span(),
                },
                span: span(),
            })
        })
        .collect();
    Program {
        imports,
        exports: vec![],
        decls,
    }
}

fn make_graph(modules: Vec<(Vec<String>, Program)>) -> ModuleGraph {
    let root = if modules.is_empty() {
        PathBuf::new()
    } else {
        PathBuf::from("root.mtl")
    };
    let modules = modules
        .into_iter()
        .map(|(path, program)| LoadedModule {
            module_path: path,
            file_path: PathBuf::from("test.mtl"),
            program,
        })
        .collect();
    ModuleGraph {
        root,
        modules,
        path_aliases: std::collections::HashMap::new(),
    }
}

// arch-verifies: ["arch.name-resolution.requirement-2"]
#[test]
fn resolves_explicit_item_import() {
    // import parser::Token;
    let graph = make_graph(vec![
        (
            vec![],
            make_program(vec![make_import(
                PathRoot::Name("parser".into()),
                ImportTree::Name {
                    name: "Token".into(),
                    alias: None,
                },
            )]),
        ),
        (
            vec!["parser".into()],
            make_program_with_pubs(vec![], &["Token"]),
        ),
    ]);

    let names = resolve(&graph).unwrap();
    let root_scope = &names.scopes[&vec![]];
    let binding = root_scope
        .explicit
        .get("Token")
        .expect("Token should be bound");
    assert_eq!(binding.source_module, vec!["parser"]);
    assert_eq!(binding.source_name, "Token");
    assert_eq!(binding.kind, BindingKind::Item);
}

#[test]
fn resolves_alias_import() {
    // import parser::Token as Tok;
    let graph = make_graph(vec![
        (
            vec![],
            make_program(vec![make_import(
                PathRoot::Name("parser".into()),
                ImportTree::Name {
                    name: "Token".into(),
                    alias: Some("Tok".into()),
                },
            )]),
        ),
        (
            vec!["parser".into()],
            make_program_with_pubs(vec![], &["Token"]),
        ),
    ]);

    let names = resolve(&graph).unwrap();
    let root_scope = &names.scopes[&vec![]];
    assert!(
        root_scope.explicit.contains_key("Tok"),
        "alias Tok should be bound"
    );
    assert!(
        !root_scope.explicit.contains_key("Token"),
        "original name Token should not be bound"
    );
    let binding = &root_scope.explicit["Tok"];
    assert_eq!(binding.source_name, "Token");
}

#[test]
fn resolves_group_import() {
    // import parser::{Ast, Token};
    let graph = make_graph(vec![
        (
            vec![],
            make_program(vec![make_import(
                PathRoot::Name("parser".into()),
                ImportTree::Group(vec![
                    ImportTree::Name {
                        name: "Ast".into(),
                        alias: None,
                    },
                    ImportTree::Name {
                        name: "Token".into(),
                        alias: None,
                    },
                ]),
            )]),
        ),
        (
            vec!["parser".into()],
            make_program_with_pubs(vec![], &["Ast", "Token"]),
        ),
    ]);

    let names = resolve(&graph).unwrap();
    let root_scope = &names.scopes[&vec![]];
    assert!(root_scope.explicit.contains_key("Ast"));
    assert!(root_scope.explicit.contains_key("Token"));
}

#[test]
fn resolves_glob_import() {
    // import parser::*;
    let graph = make_graph(vec![
        (
            vec![],
            make_program(vec![make_import(
                PathRoot::Name("parser".into()),
                ImportTree::Glob,
            )]),
        ),
        (vec!["parser".into()], make_program(vec![])),
    ]);

    let names = resolve(&graph).unwrap();
    let root_scope = &names.scopes[&vec![]];
    assert!(
        root_scope.explicit.is_empty(),
        "glob should not add explicit bindings"
    );
    assert_eq!(
        root_scope.globs,
        vec![
            (GlobTier::User, vec!["parser".to_string()]),
            (GlobTier::Std, vec!["std".to_string(), "core".to_string()]),
        ]
    );
}

#[test]
fn resolves_module_handle_import() {
    // import parser; — parser is a known module, so this is a handle import
    let graph = make_graph(vec![
        (
            vec![],
            make_program(vec![make_import(
                PathRoot::Root,
                ImportTree::Name {
                    name: "parser".into(),
                    alias: None,
                },
            )]),
        ),
        (vec!["parser".into()], make_program(vec![])),
    ]);

    let names = resolve(&graph).unwrap();
    let root_scope = &names.scopes[&vec![]];
    let binding = root_scope
        .explicit
        .get("parser")
        .expect("parser handle should be bound");
    assert_eq!(binding.kind, BindingKind::Module);
    assert_eq!(binding.source_module, vec!["parser"]);
}

#[test]
fn rejects_duplicate_explicit_import() {
    // import parser::Token;
    // import lexer::Token;  ← conflict
    let graph = make_graph(vec![
        (
            vec![],
            make_program(vec![
                make_import(
                    PathRoot::Name("parser".into()),
                    ImportTree::Name {
                        name: "Token".into(),
                        alias: None,
                    },
                ),
                make_import(
                    PathRoot::Name("lexer".into()),
                    ImportTree::Name {
                        name: "Token".into(),
                        alias: None,
                    },
                ),
            ]),
        ),
        (
            vec!["parser".into()],
            make_program_with_pubs(vec![], &["Token"]),
        ),
        (
            vec!["lexer".into()],
            make_program_with_pubs(vec![], &["Token"]),
        ),
    ]);

    let err = resolve(&graph).expect_err("duplicate import should fail");
    assert!(
        err.to_string().contains("Token"),
        "error should mention Token"
    );
}

#[test]
fn private_item_import_is_recorded_for_typechecker() {
    // import parser::Token; where Token is private in parser.
    // The name_resolver records the binding; visibility enforcement (T0009)
    // happens in the typechecker's build_import_schemes which has access to
    // the full NormalizedModuleGraph to distinguish private from absent.
    let graph = make_graph(vec![
        (
            vec![],
            make_program(vec![make_import(
                PathRoot::Name("parser".into()),
                ImportTree::Name {
                    name: "Token".into(),
                    alias: None,
                },
            )]),
        ),
        (vec!["parser".into()], make_program(vec![])), // no pub declarations
    ]);

    let names = resolve(&graph).expect("name_resolver should not reject private imports");
    let root_scope = names.scopes.get(&vec![]).expect("root scope should exist");
    assert!(
        root_scope.explicit.contains_key("Token"),
        "Token binding should be recorded so the typechecker can produce T0009"
    );
}

#[test]
fn resolves_root_absolute_path() {
    // import root::parser::Ast;
    let graph = make_graph(vec![
        (
            vec![],
            make_program(vec![make_import(
                PathRoot::Root,
                ImportTree::Path {
                    name: "parser".into(),
                    tree: Box::new(ImportTree::Name {
                        name: "Ast".into(),
                        alias: None,
                    }),
                },
            )]),
        ),
        (
            vec!["parser".into()],
            make_program_with_pubs(vec![], &["Ast"]),
        ),
    ]);

    let names = resolve(&graph).unwrap();
    let root_scope = &names.scopes[&vec![]];
    let binding = root_scope.explicit.get("Ast").expect("Ast should be bound");
    assert_eq!(binding.source_module, vec!["parser"]);
}

#[test]
fn resolves_self_relative_path() {
    // In module ["parser"], import self::child::Thing;
    let graph = make_graph(vec![
        (
            vec!["parser".into()],
            make_program(vec![make_import(
                PathRoot::Self_,
                ImportTree::Path {
                    name: "child".into(),
                    tree: Box::new(ImportTree::Name {
                        name: "Thing".into(),
                        alias: None,
                    }),
                },
            )]),
        ),
        (
            vec!["parser".into(), "child".into()],
            make_program_with_pubs(vec![], &["Thing"]),
        ),
    ]);

    let names = resolve(&graph).unwrap();
    let parser_scope = &names.scopes[&vec!["parser".to_string()]];
    let binding = parser_scope
        .explicit
        .get("Thing")
        .expect("Thing should be bound");
    assert_eq!(binding.source_module, vec!["parser", "child"]);
}

#[test]
fn resolves_super_relative_path() {
    // In module ["parser", "child"], import super::Token;
    let graph = make_graph(vec![
        (
            vec!["parser".into(), "child".into()],
            make_program(vec![make_import(
                PathRoot::Super,
                ImportTree::Name {
                    name: "Token".into(),
                    alias: None,
                },
            )]),
        ),
        (
            vec!["parser".into()],
            make_program_with_pubs(vec![], &["Token"]),
        ),
    ]);

    let names = resolve(&graph).unwrap();
    let child_scope = &names.scopes[&vec!["parser".to_string(), "child".to_string()]];
    let binding = child_scope
        .explicit
        .get("Token")
        .expect("Token should be bound");
    assert_eq!(binding.source_module, vec!["parser"]);
}

fn make_export(root: PathRoot, tree: ImportTree) -> crate::data::ast::ExportDecl {
    use crate::data::ast::ExportDecl;
    ExportDecl {
        path: ImportPath { root, tree },
        span: span(),
    }
}

#[test]
fn facade_re_exports_item_for_callers() {
    // parser.mln: export ast::Ast;
    // Caller can import parser::Ast even though Ast is defined in ast.
    let ast_module_prog = make_program_with_pubs(vec![], &["Ast"]);
    let parser_prog = Program {
        imports: vec![],
        exports: vec![make_export(
            PathRoot::Name("ast".into()),
            ImportTree::Name {
                name: "Ast".into(),
                alias: None,
            },
        )],
        decls: vec![],
    };
    let root_prog = make_program(vec![make_import(
        PathRoot::Name("parser".into()),
        ImportTree::Name {
            name: "Ast".into(),
            alias: None,
        },
    )]);
    let graph = make_graph(vec![
        (vec![], root_prog),
        (vec!["parser".into()], parser_prog),
        // ast is imported by parser, so its path is ["parser", "ast"]
        (vec!["parser".into(), "ast".into()], ast_module_prog),
    ]);

    let names = resolve(&graph).unwrap();
    // parser's re_exports should include Ast
    let parser_scope = &names.scopes[&vec!["parser".to_string()]];
    assert!(
        parser_scope.re_exports.contains_key("Ast"),
        "parser should re-export Ast"
    );
    // root should have imported Ast from parser — but the binding's real identity
    // (ADR-0042) chases through the re-export to Ast's actual declaring module,
    // `["parser", "ast"]`, not the facade's own path. This is what makes the
    // binding's `symbol_id` match the same id `ast`'s own module registers a
    // runtime value under, instead of an orphaned id nothing ever populates.
    let root_scope = &names.scopes[&vec![]];
    let binding = root_scope
        .explicit
        .get("Ast")
        .expect("Ast should be importable from facade");
    assert_eq!(binding.source_module, vec!["parser", "ast"]);
    // The real regression check (ADR-0042): this binding's id must be the *same*
    // id `Ast`'s own declaration was interned under — not a fresh id minted for
    // `(["parser"], "Ast")`, which nothing would ever register a runtime value
    // under, since `Ast` isn't actually declared in `parser` itself.
    let real_id = names.symbols[&(
        vec!["parser".to_string(), "ast".to_string()],
        "Ast".to_string(),
    )];
    assert_eq!(
        binding.symbol_id, real_id,
        "an import of a re-exported name must reuse its real declaration's id"
    );
}

#[test]
fn re_export_alias_is_visible_not_original() {
    // parser.mln: export ast::Ast as Tree;
    let ast_module_prog = make_program_with_pubs(vec![], &["Ast"]);
    let parser_prog = Program {
        imports: vec![],
        exports: vec![make_export(
            PathRoot::Name("ast".into()),
            ImportTree::Name {
                name: "Ast".into(),
                alias: Some("Tree".into()),
            },
        )],
        decls: vec![],
    };
    let graph = make_graph(vec![
        (vec!["parser".into()], parser_prog),
        // ast is imported by parser, so its path is ["parser", "ast"]
        (vec!["parser".into(), "ast".into()], ast_module_prog),
    ]);

    let names = resolve(&graph).unwrap();
    let parser_scope = &names.scopes[&vec!["parser".to_string()]];
    assert!(
        parser_scope.re_exports.contains_key("Tree"),
        "aliased re-export Tree should appear"
    );
    assert!(
        !parser_scope.re_exports.contains_key("Ast"),
        "original name Ast should not appear"
    );
}

#[test]
fn rejects_re_export_of_private_item() {
    // parser.mln: export ast::Hidden; where Hidden is private in ast
    let ast_module_prog = make_program(vec![]); // no pub declarations
    let parser_prog = Program {
        imports: vec![],
        exports: vec![make_export(
            PathRoot::Name("ast".into()),
            ImportTree::Name {
                name: "Hidden".into(),
                alias: None,
            },
        )],
        decls: vec![],
    };
    let graph = make_graph(vec![
        (vec!["parser".into()], parser_prog),
        // ast is imported by parser, so its path is ["parser", "ast"]
        (vec!["parser".into(), "ast".into()], ast_module_prog),
    ]);

    let err = resolve(&graph).expect_err("re-exporting private item should fail");
    let msg = err.to_string();
    assert!(msg.contains("Hidden"), "error should mention Hidden");
    assert!(
        msg.contains("visibility"),
        "error should mention visibility"
    );
}

#[test]
fn glob_re_export_includes_all_public_names() {
    // parser.mln: export ast::*;
    let ast_module_prog = make_program_with_pubs(vec![], &["Ast", "Token"]);
    let parser_prog = Program {
        imports: vec![],
        exports: vec![make_export(PathRoot::Name("ast".into()), ImportTree::Glob)],
        decls: vec![],
    };
    let root_prog = make_program(vec![make_import(
        PathRoot::Name("parser".into()),
        ImportTree::Name {
            name: "Ast".into(),
            alias: None,
        },
    )]);
    let graph = make_graph(vec![
        (vec![], root_prog),
        (vec!["parser".into()], parser_prog),
        // ast is imported by parser, so its path is ["parser", "ast"]
        (vec!["parser".into(), "ast".into()], ast_module_prog),
    ]);

    let names = resolve(&graph).unwrap();
    let parser_scope = &names.scopes[&vec!["parser".to_string()]];
    assert!(parser_scope.re_exports.contains_key("Ast"));
    assert!(parser_scope.re_exports.contains_key("Token"));
    // root can import Ast from parser
    let root_scope = &names.scopes[&vec![]];
    assert!(root_scope.explicit.contains_key("Ast"));
}

// ── SymbolId consistency ──────────────────────────────────────────────────

// arch-verifies: ["arch.name-resolution.requirement-1"]
#[test]
fn same_declaration_gets_same_symbol_id_regardless_of_importer() {
    // root and other both import parser::Token (via absolute root:: path).
    // Both must get the same SymbolId for parser::Token.
    let root_prog = make_program(vec![make_import(
        PathRoot::Root,
        ImportTree::Path {
            name: "parser".into(),
            tree: Box::new(ImportTree::Name {
                name: "Token".into(),
                alias: None,
            }),
        },
    )]);
    let other_prog = make_program(vec![make_import(
        PathRoot::Root,
        ImportTree::Path {
            name: "parser".into(),
            tree: Box::new(ImportTree::Name {
                name: "Token".into(),
                alias: None,
            }),
        },
    )]);
    let graph = make_graph(vec![
        (vec![], root_prog),
        (vec!["other".into()], other_prog),
        (
            vec!["parser".into()],
            make_program_with_pubs(vec![], &["Token"]),
        ),
    ]);

    let names = resolve(&graph).unwrap();
    let root_id = names.scopes[&vec![]].explicit["Token"].symbol_id;
    let other_id = names.scopes[&vec!["other".to_string()]].explicit["Token"].symbol_id;
    assert_eq!(
        root_id, other_id,
        "same declaration must get same SymbolId in both importers"
    );
}

// arch-verifies: ["arch.name-resolution.requirement-1"]
#[test]
fn aliased_import_has_same_symbol_id_as_direct_import() {
    // root imports parser::Token as Tok; other imports parser::Token directly.
    // Both must resolve to the same SymbolId — alias must not change identity.
    let root_prog = make_program(vec![make_import(
        PathRoot::Root,
        ImportTree::Path {
            name: "parser".into(),
            tree: Box::new(ImportTree::Name {
                name: "Token".into(),
                alias: Some("Tok".into()),
            }),
        },
    )]);
    let other_prog = make_program(vec![make_import(
        PathRoot::Root,
        ImportTree::Path {
            name: "parser".into(),
            tree: Box::new(ImportTree::Name {
                name: "Token".into(),
                alias: None,
            }),
        },
    )]);
    let graph = make_graph(vec![
        (vec![], root_prog),
        (vec!["other".into()], other_prog),
        (
            vec!["parser".into()],
            make_program_with_pubs(vec![], &["Token"]),
        ),
    ]);

    let names = resolve(&graph).unwrap();
    let alias_id = names.scopes[&vec![]].explicit["Tok"].symbol_id;
    let direct_id = names.scopes[&vec!["other".to_string()]].explicit["Token"].symbol_id;
    assert_eq!(
        alias_id, direct_id,
        "aliased import should have same SymbolId as direct import"
    );
}

// arch-verifies: ["arch.name-resolution.requirement-1"]
#[test]
fn distinct_declarations_get_distinct_symbol_ids() {
    // parser::Token and parser::Ast must have different SymbolIds.
    let graph = make_graph(vec![
        (
            vec![],
            make_program(vec![make_import(
                PathRoot::Name("parser".into()),
                ImportTree::Group(vec![
                    ImportTree::Name {
                        name: "Token".into(),
                        alias: None,
                    },
                    ImportTree::Name {
                        name: "Ast".into(),
                        alias: None,
                    },
                ]),
            )]),
        ),
        (
            vec!["parser".into()],
            make_program_with_pubs(vec![], &["Token", "Ast"]),
        ),
    ]);

    let names = resolve(&graph).unwrap();
    let root_scope = &names.scopes[&vec![]];
    let token_id = root_scope.explicit["Token"].symbol_id;
    let ast_id = root_scope.explicit["Ast"].symbol_id;
    assert_ne!(
        token_id, ast_id,
        "distinct declarations must have distinct SymbolIds"
    );
}

#[test]
fn definitions_index_maps_symbol_to_declaration_span() {
    // A module with a public function `foo`. Its SymbolId must map to a
    // definition span in ResolvedNames.definitions (RFC-0059).
    let graph = make_graph(vec![(
        vec!["lib".into()],
        make_program_with_pubs(vec![], &["foo"]),
    )]);

    let names = resolve(&graph).unwrap();
    let foo_id = names.symbols[&(vec!["lib".to_string()], "foo".to_string())];
    assert!(
        names.definitions.contains_key(&foo_id),
        "definitions should contain the SymbolId of `foo`"
    );
}

#[test]
fn definitions_index_covers_every_declared_symbol() {
    // Every top-level declared name in a module should have a definition span.
    let graph = make_graph(vec![(
        vec!["lib".into()],
        make_program_with_pubs(vec![], &["a", "b", "c"]),
    )]);

    let names = resolve(&graph).unwrap();
    for name in ["a", "b", "c"] {
        let id = names.symbols[&(vec!["lib".to_string()], name.to_string())];
        assert!(
            names.definitions.contains_key(&id),
            "definitions should contain `{name}`"
        );
    }
}

#[test]
fn interns_impl_and_aspect_method_symbols() {
    // Inherent, aspect-impl, and aspect-declared methods each get a distinct
    // SymbolId under their structured key, with a recorded definition span
    // (METEL-185 step 3a).
    let src = "struct Foo { x: i64 }\n\
               extend Foo { fun bar(self) -> i64 { self.x } }\n\
               aspect Greet { fun hi(self) -> i64; }\n\
               extend Foo: Greet { fun hi(self) -> i64 { 1 } }";
    let program = crate::pipeline::parsing::parser::parse(src, "t.mtl").expect("parse");
    let graph = make_graph(vec![(vec![], program)]);
    let names = resolve(&graph).unwrap();

    let inherent = names.symbols[&(vec![], "Foo::bar".to_string())];
    let aspect_impl = names.symbols[&(vec![], "Foo::Greet::hi".to_string())];
    let aspect_decl = names.symbols[&(vec![], "Greet::hi".to_string())];

    for id in [inherent, aspect_impl, aspect_decl] {
        assert!(
            names.definitions.contains_key(&id),
            "method symbol {id:?} should have a definition span"
        );
    }
    assert_ne!(
        inherent, aspect_impl,
        "an inherent method and an aspect-impl method on the same type must differ"
    );
    assert_ne!(aspect_impl, aspect_decl);
}

// arch-verifies: ["arch.name-resolution.requirement-1"]
#[test]
fn symbol_id_is_stable_in_symbol_table() {
    // names.symbols should contain the same (module, name) → id mapping.
    let graph = make_graph(vec![
        (
            vec![],
            make_program(vec![make_import(
                PathRoot::Name("parser".into()),
                ImportTree::Name {
                    name: "Token".into(),
                    alias: None,
                },
            )]),
        ),
        (
            vec!["parser".into()],
            make_program_with_pubs(vec![], &["Token"]),
        ),
    ]);

    let names = resolve(&graph).unwrap();
    let binding_id = names.scopes[&vec![]].explicit["Token"].symbol_id;
    let table_id = names.symbols[&(vec!["parser".to_string()], "Token".to_string())];
    assert_eq!(
        binding_id, table_id,
        "SymbolId in binding must match entry in names.symbols"
    );
}

// arch-verifies: ["arch.name-resolution.requirement-1"]
#[test]
fn symbol_id_is_independent_of_module_resolution_order() {
    // ADR-0054's structural-allocation amendment (metel-core#1048): a
    // SymbolId must be a function of (module path, name), never of
    // traversal order. Resolving the identical set of modules in reverse
    // order must hand every declaration the same id it got in forward
    // order. Confirmed to fail before this fix: `graph.modules`'s own
    // load-order fed `SymbolTable::intern`'s allocation counter directly,
    // so `a::A` and `b::B` got their ids swapped when the module list was
    // reversed.
    let a = (
        vec!["a".to_string()],
        make_program_with_pubs(vec![], &["A"]),
    );
    let b = (
        vec!["b".to_string()],
        make_program_with_pubs(vec![], &["B"]),
    );

    let forward = resolve(&make_graph(vec![a.clone(), b.clone()])).unwrap();
    let reversed = resolve(&make_graph(vec![b, a])).unwrap();

    let a_key = (vec!["a".to_string()], "A".to_string());
    let b_key = (vec!["b".to_string()], "B".to_string());
    assert_eq!(
        forward.symbols[&a_key], reversed.symbols[&a_key],
        "a::A's SymbolId changed when module resolution order was reversed"
    );
    assert_eq!(
        forward.symbols[&b_key], reversed.symbols[&b_key],
        "b::B's SymbolId changed when module resolution order was reversed"
    );
}
