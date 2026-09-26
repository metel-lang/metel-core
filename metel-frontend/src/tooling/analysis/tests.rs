use super::*;
use crate::pipeline::parsing::module_loader::InMemorySourceProvider;

#[test]
fn virtual_analysis_returns_typed_modules_without_evaluation() {
    let provider = InMemorySourceProvider::new("editor.mtl", "fun main() {}");
    let analysis = analyze_virtual_root_with("editor.mtl", &provider, AnalysisOptions::default())
        .expect("an in-memory program should be analyzable");

    assert!(
        analysis
            .graph
            .modules
            .iter()
            .any(|module| module.module_path.is_empty())
    );
    assert!(analysis.warnings.is_empty());
}

// ── #1062 (Freeze 1051c): FieldId / VariantId on the typed IR ──────────────

mod member_ids_on_typed_ir {
    use super::*;
    use crate::data::typed_ast::{FunBody, TypedDecl, TypedExpr, TypedMatchArm, TypedPattern};

    fn analyze(src: &str) -> Analysis {
        let provider = InMemorySourceProvider::new("editor.mtl", src);
        analyze_virtual_root_with("editor.mtl", &provider, AnalysisOptions::default())
            .expect("source should analyze")
    }

    fn root_sym(analysis: &Analysis, name: &str) -> crate::identity::symbols::SymbolId {
        *analysis
            .names
            .symbols
            .get(&(vec![], name.to_string()))
            .unwrap_or_else(|| panic!("`{name}` should have a symbol"))
    }

    /// Tail expression of the root-module function `fn_name`.
    fn tail_expr<'a>(analysis: &'a Analysis, fn_name: &str) -> &'a TypedExpr {
        let root = analysis
            .graph
            .modules
            .iter()
            .find(|m| m.module_path.is_empty())
            .expect("root module");
        let func = root
            .decls
            .iter()
            .find_map(|d| match d {
                TypedDecl::Fun(f) if f.name == fn_name => Some(f),
                _ => None,
            })
            .unwrap_or_else(|| panic!("`{fn_name}` should be a typed function"));
        match &func.body {
            FunBody::Typed(block) => block
                .tail
                .as_deref()
                .unwrap_or_else(|| panic!("`{fn_name}` should have a tail expression")),
            _ => panic!("`{fn_name}` should have a concrete typed body"),
        }
    }

    #[test]
    fn field_access_carries_the_interned_field_id() {
        let analysis = analyze(
            "struct Point { x: i64, y: i64 }\n\
             fun get_x(p: Point) -> i64 { p.x }\n",
        );
        let point = root_sym(&analysis, "Point");
        let TypedExpr::FieldAccess {
            field_id, field, ..
        } = tail_expr(&analysis, "get_x")
        else {
            panic!("expected a field access");
        };
        assert_eq!(field, "x");
        let id = field_id.expect("field access should carry a FieldId");
        assert_eq!(
            Some(id),
            analysis.members.field(point, "x"),
            "the stamped id must be the one the member table interned"
        );
        assert_eq!(
            analysis.members.field_info(id).map(|i| i.owner),
            Some(point)
        );
    }

    #[test]
    fn enum_variant_literal_carries_the_interned_variant_id() {
        let analysis = analyze(
            "enum Color { Red, Green, Blue }\n\
             fun pick() -> Color { Color::Green }\n",
        );
        let color = root_sym(&analysis, "Color");
        let TypedExpr::StructLiteral {
            variant_id,
            type_id,
            ..
        } = tail_expr(&analysis, "pick")
        else {
            panic!("expected a struct-literal node for the enum variant");
        };
        assert_eq!(*type_id, Some(color));
        assert_eq!(
            *variant_id,
            analysis.members.variant(color, "Green"),
            "the stamped variant id must be the interned one"
        );
        assert!(variant_id.is_some(), "a resolved variant must carry an id");
    }

    #[test]
    fn plain_struct_literal_has_no_variant_id() {
        let analysis = analyze(
            "struct Point { x: i64, y: i64 }\n\
             fun make() -> Point { Point { x = 1, y = 2 } }\n",
        );
        let TypedExpr::StructLiteral { variant_id, .. } = tail_expr(&analysis, "make") else {
            panic!("expected a struct literal");
        };
        assert_eq!(*variant_id, None, "a struct is not a variant");
    }

    #[test]
    fn field_access_on_a_type_the_member_table_never_saw_reports_none() {
        // A block-local struct gets no `(module, name)` symbol from the name
        // resolver, so `collect_members` never interns its fields. The node
        // must carry `None` — the sanctioned recovery state — not a
        // fabricated id.
        let analysis = analyze(
            "fun f() -> i64 {\n\
             \tstruct Local { v: i64 }\n\
             \tlet x := Local { v = 3 };\n\
             \tx.v\n\
             }\n",
        );
        let TypedExpr::FieldAccess {
            field_id, field, ..
        } = tail_expr(&analysis, "f")
        else {
            panic!("expected a field access");
        };
        assert_eq!(field, "v");
        assert_eq!(
            *field_id, None,
            "no id for a type the member table never saw"
        );
    }

    // ── pattern member sites (#1062b) ─────────────────────────────────────

    /// Arms of the single `match` that is the tail of the root function
    /// `fn_name`.
    fn match_arms<'a>(analysis: &'a Analysis, fn_name: &str) -> &'a [TypedMatchArm] {
        match tail_expr(analysis, fn_name) {
            TypedExpr::Match(m) => &m.arms,
            _ => panic!("`{fn_name}` tail should be a match"),
        }
    }

    #[test]
    fn enum_variant_patterns_carry_the_interned_variant_and_field_ids() {
        let analysis = analyze(
            "enum Sig { Halt, Go { code: i64 } }\n\
             fun handle(s: Sig) -> i64 {\n\
             \tmatch (s) {\n\
             \t\tSig::Halt => 0,\n\
             \t\tSig::Go { code } => code,\n\
             \t}\n\
             }\n",
        );
        let sig = root_sym(&analysis, "Sig");
        let arms = match_arms(&analysis, "handle");

        let TypedPattern::EnumVariant {
            variant_id, fields, ..
        } = &arms[0].pattern
        else {
            panic!("arm 0 should be an enum-variant pattern");
        };
        assert_eq!(*variant_id, analysis.members.variant(sig, "Halt"));
        assert!(fields.is_empty());

        let TypedPattern::EnumVariant {
            variant_id, fields, ..
        } = &arms[1].pattern
        else {
            panic!("arm 1 should be an enum-variant pattern");
        };
        assert_eq!(*variant_id, analysis.members.variant(sig, "Go"));
        assert_eq!(fields.len(), 1);
        assert_eq!(fields[0].0, "code");
        assert_eq!(
            fields[0].1,
            analysis.members.field(sig, "Go::code"),
            "variant fields are interned variant-qualified on the enum owner"
        );
        // #1052a-4: `Sig::Go { code }` also binds `code` as a local.
        assert!(
            fields[0].2.is_some(),
            "the variant field-shorthand binding carries a LocalId"
        );
    }

    #[test]
    fn struct_pattern_carries_the_interned_field_ids() {
        let analysis = analyze(
            "struct Pt { x: i64, y: i64 }\n\
             fun sum(p: Pt) -> i64 {\n\
             \tmatch (p) {\n\
             \t\tPt { x, y } => x + y,\n\
             \t}\n\
             }\n",
        );
        let pt = root_sym(&analysis, "Pt");
        let TypedPattern::Struct {
            type_id, fields, ..
        } = &match_arms(&analysis, "sum")[0].pattern
        else {
            panic!("expected a struct pattern");
        };
        assert_eq!(*type_id, Some(pt));
        let by_name: std::collections::HashMap<_, _> = fields
            .iter()
            .map(|(n, field_id, local_id)| (n.as_str(), (*field_id, *local_id)))
            .collect();
        assert_eq!(by_name["x"].0, analysis.members.field(pt, "x"));
        assert_eq!(by_name["y"].0, analysis.members.field(pt, "y"));
        assert!(by_name["x"].0.is_some() && by_name["y"].0.is_some());
        // #1052a-4: each field-shorthand also introduces a lexical binding.
        assert!(
            by_name["x"].1.is_some() && by_name["y"].1.is_some(),
            "struct pattern field bindings carry a LocalId"
        );
    }

    #[test]
    fn structural_record_pattern_has_no_nominal_field_channel() {
        // A bare `{ .. }` record pattern is structural: its labels are
        // `LabelId`s, never nominal `FieldId`s (ADR-0054), so the typed
        // pattern carries plain spellings with no id slot to fabricate.
        let analysis = analyze(
            "fun mag(p: { x: i64, y: i64 }) -> i64 {\n\
             \tmatch (p) {\n\
             \t\t{ x, y } => x + y,\n\
             \t}\n\
             }\n",
        );
        let TypedPattern::Record { fields, .. } = &match_arms(&analysis, "mag")[0].pattern else {
            panic!("expected a structural record pattern");
        };
        let names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(names, ["x", "y"]);
        // Structural: no `FieldId` channel, but each label still binds a local.
        assert!(fields.iter().all(|(_, local)| local.is_some()));
    }

    // ── registry entry ids (#1068) ───────────────────────────────────────

    #[test]
    fn registry_field_and_variant_entries_carry_the_interned_ids() {
        let analysis = analyze(
            "struct Pt { x: i64, y: i64 }\n\
             enum Sig { Halt, Go { code: i64 } }\n\
             fun use_them(p: Pt, s: Sig) -> i64 {\n\
             \tmatch (s) { Sig::Halt => p.x, Sig::Go { code } => code }\n\
             }\n",
        );
        let reg = &analysis.graph.type_registry;
        let pt = root_sym(&analysis, "Pt");
        let sig = root_sym(&analysis, "Sig");

        let pt_fields = reg.struct_fields_by_id(pt).expect("Pt in registry");
        for f in pt_fields {
            assert_eq!(
                f.id,
                analysis.members.field(pt, &f.name),
                "FieldEntry `{}` stamped with the interned FieldId",
                f.name
            );
            assert!(f.id.is_some());
        }

        let sig_info = reg.enum_info_by_id(sig).expect("Sig in registry");
        for v in &sig_info.variants {
            assert_eq!(v.id, analysis.members.variant(sig, &v.name));
            assert!(v.id.is_some());
            for f in &v.fields {
                assert_eq!(
                    f.id,
                    analysis
                        .members
                        .field(sig, &format!("{}::{}", v.name, f.name)),
                    "variant field `{}::{}` stamped variant-qualified",
                    v.name,
                    f.name
                );
            }
        }
    }

    // ── binding identity on value references (#1052a-1) ───────────────────

    #[test]
    fn local_reference_carries_its_local_binding_id() {
        let analysis = analyze(
            "fun f(p: i64) -> i64 {\n\
             \tlet q := p;\n\
             \tq\n\
             }\n",
        );
        // `f`'s tail is the bare `q` use.
        let TypedExpr::Ident(name, binding, _, _) = tail_expr(&analysis, "f") else {
            panic!("expected a bare ident tail");
        };
        assert_eq!(name, "q");
        let id = binding.expect("a resolved local reference carries a BindingId");
        let crate::identity::BindingId::Local(local) = id else {
            panic!("`q` is a lexical local, not a global");
        };
        // It matches the resolution map's own record for that binding.
        assert!(
            analysis
                .resolution
                .definitions
                .contains_key(&crate::identity::BindingId::Local(local)),
            "the stamped LocalId is a real definition in the resolution map"
        );
    }

    #[test]
    fn global_call_callee_carries_its_symbol_binding_id() {
        let analysis = analyze(
            "fun helper() -> i64 { 1 }\n\
             fun main() -> i64 { helper() }\n",
        );
        let TypedExpr::Call { callee, .. } = tail_expr(&analysis, "main") else {
            panic!("expected a call tail");
        };
        let TypedExpr::Ident(name, binding, _, _) = &**callee else {
            panic!("expected an ident callee");
        };
        assert_eq!(name, "helper");
        assert!(
            matches!(binding, Some(crate::identity::BindingId::Global(_))),
            "a top-level function reference resolves to a Global BindingId, got {binding:?}"
        );
    }

    #[test]
    fn block_local_let_carries_its_local_id_and_the_use_matches() {
        let analysis = analyze(
            "fun f() -> i64 {\n\
             \tlet q := 1;\n\
             \tq\n\
             }\n",
        );
        let root = analysis
            .graph
            .modules
            .iter()
            .find(|m| m.module_path.is_empty())
            .unwrap();
        let TypedDecl::Fun(func) = root
            .decls
            .iter()
            .find(|d| matches!(d, TypedDecl::Fun(f) if f.name == "f"))
            .unwrap()
        else {
            unreachable!()
        };
        let FunBody::Typed(block) = &func.body else {
            panic!("typed body")
        };
        let let_id = block
            .stmts
            .iter()
            .find_map(|d| match d {
                TypedDecl::Let(ld) if ld.name == "q" => Some(ld.local_id),
                _ => None,
            })
            .expect("a `let q` in the block");
        let bound = let_id.expect("a block-local let carries a LocalId");

        // The `q` use in the tail resolves to that same LocalId.
        let TypedExpr::Ident(_, Some(crate::identity::BindingId::Local(used)), _, _) =
            block.tail.as_deref().unwrap()
        else {
            panic!("tail `q` should be a local reference");
        };
        assert_eq!(*used, bound, "the use and the `let` share one LocalId");
    }

    #[test]
    fn match_arm_binding_pattern_carries_a_local_id() {
        let analysis = analyze(
            "fun pick(n: i64) -> i64 {\n\
             \tmatch (n) { x => x }\n\
             }\n",
        );
        let TypedPattern::Binding(name, local, _) = &match_arms(&analysis, "pick")[0].pattern
        else {
            panic!("expected a binding pattern");
        };
        assert_eq!(name, "x");
        assert!(local.is_some(), "a match-arm binding introduces a LocalId");
    }

    #[test]
    fn for_in_loop_binding_carries_a_local_id() {
        use crate::data::typed_ast::TypedStmt;
        let analysis = analyze(
            "fun sum(xs: i64[]) -> i64 {\n\
             \tvar acc: i64 := 0;\n\
             \tfor (x in xs) { acc := acc + x; }\n\
             \tacc\n\
             }\n",
        );
        let root = analysis
            .graph
            .modules
            .iter()
            .find(|m| m.module_path.is_empty())
            .unwrap();
        let TypedDecl::Fun(func) = root
            .decls
            .iter()
            .find(|d| matches!(d, TypedDecl::Fun(f) if f.name == "sum"))
            .unwrap()
        else {
            unreachable!()
        };
        let FunBody::Typed(block) = &func.body else {
            panic!("typed body")
        };
        let has_local_id = block.stmts.iter().any(|d| match d {
            TypedDecl::Stmt(s) => matches!(
                &**s,
                TypedStmt::ForIn(fi) if fi.binding == "x" && fi.binding_id.is_some()
            ),
            _ => false,
        });
        assert!(has_local_id, "the `for` loop binding carries a LocalId");
    }

    #[test]
    fn function_params_carry_local_ids_the_body_use_matches() {
        let analysis = analyze("fun add(a: i64, b: i64) -> i64 { a + b }\n");
        let root = analysis
            .graph
            .modules
            .iter()
            .find(|m| m.module_path.is_empty())
            .unwrap();
        let TypedDecl::Fun(func) = root
            .decls
            .iter()
            .find(|d| matches!(d, TypedDecl::Fun(f) if f.name == "add"))
            .unwrap()
        else {
            unreachable!()
        };
        assert_eq!(func.param_ids.len(), 2);
        assert!(
            func.param_ids.iter().all(Option::is_some),
            "every parameter carries a LocalId: {:?}",
            func.param_ids
        );
    }

    #[test]
    fn closure_capture_ids_resolve_the_captured_local() {
        let analysis = analyze(
            "fun mk() -> i64 {\n\
             \tlet base := 10;\n\
             \tlet f := [base] |x: i64| { x + base };\n\
             \tf(1)\n\
             }\n",
        );
        let root = analysis
            .graph
            .modules
            .iter()
            .find(|m| m.module_path.is_empty())
            .unwrap();
        let TypedDecl::Fun(func) = root
            .decls
            .iter()
            .find(|d| matches!(d, TypedDecl::Fun(f) if f.name == "mk"))
            .unwrap()
        else {
            unreachable!()
        };
        let FunBody::Typed(block) = &func.body else {
            panic!("typed body")
        };
        // `let base` — its LocalId.
        let base_id = block
            .stmts
            .iter()
            .find_map(|d| match d {
                TypedDecl::Let(ld) if ld.name == "base" => ld.local_id,
                _ => None,
            })
            .expect("`let base`");
        // The closure's capture of `base` resolves to that same LocalId.
        let cap_ids = block.stmts.iter().find_map(|d| match d {
            TypedDecl::Let(ld) => match &ld.value {
                TypedExpr::Closure { capture_ids, .. } => Some(capture_ids.clone()),
                _ => None,
            },
            _ => None,
        });
        let cap_ids = cap_ids.expect("a closure `let f`");
        assert!(
            cap_ids.contains(&Some(base_id)),
            "the closure captures `base` by its LocalId: {cap_ids:?}"
        );
    }

    #[test]
    fn a_forward_reference_to_a_nested_fn_resolves_to_its_local_id() {
        // metel-core#712 hoisting: the call in the `let` initializer runs
        // before `helper`'s declaration line, but resolves to it.
        let analysis = analyze(
            "fun outer() -> i64 {\n\
             \tlet r := helper();\n\
             \tfun helper() -> i64 { 7 }\n\
             \tr\n\
             }\n",
        );
        let root = analysis
            .graph
            .modules
            .iter()
            .find(|m| m.module_path.is_empty())
            .unwrap();
        let TypedDecl::Fun(outer) = root
            .decls
            .iter()
            .find(|d| matches!(d, TypedDecl::Fun(f) if f.name == "outer"))
            .unwrap()
        else {
            unreachable!()
        };
        let FunBody::Typed(block) = &outer.body else {
            panic!("typed body")
        };
        let helper_id = block
            .stmts
            .iter()
            .find_map(|d| match d {
                TypedDecl::Fun(f) if f.name == "helper" => f.local_id,
                _ => None,
            })
            .expect("nested `fun helper` carries a LocalId");
        // The `helper()` call in the `let r := …` initializer.
        let call_callee = block.stmts.iter().find_map(|d| match d {
            TypedDecl::Let(ld) if ld.name == "r" => match &ld.value {
                TypedExpr::Call { callee, .. } => Some(&**callee),
                _ => None,
            },
            _ => None,
        });
        let TypedExpr::Ident(_, Some(crate::identity::BindingId::Local(used)), _, _) =
            call_callee.expect("`let r := helper()`")
        else {
            panic!("the forward `helper` reference is a resolved local");
        };
        assert_eq!(*used, helper_id, "forward ref resolves to the nested fn");
    }

    #[test]
    fn nested_fn_carries_a_local_id_top_level_does_not() {
        let analysis = analyze(
            "fun outer() -> i64 {\n\
             \tfun helper(n: i64) -> i64 { n + 1 }\n\
             \thelper(41)\n\
             }\n",
        );
        let root = analysis
            .graph
            .modules
            .iter()
            .find(|m| m.module_path.is_empty())
            .unwrap();
        let TypedDecl::Fun(outer) = root
            .decls
            .iter()
            .find(|d| matches!(d, TypedDecl::Fun(f) if f.name == "outer"))
            .unwrap()
        else {
            unreachable!()
        };
        assert!(
            outer.local_id.is_none(),
            "a top-level fn has no lexical LocalId"
        );
        let FunBody::Typed(block) = &outer.body else {
            panic!("typed body")
        };
        let helper = block
            .stmts
            .iter()
            .find_map(|d| match d {
                TypedDecl::Fun(f) if f.name == "helper" => Some(f),
                _ => None,
            })
            .expect("nested `fun helper`");
        let helper_id = helper.local_id.expect("a nested fn carries a LocalId");

        // The call to `helper` in the tail resolves to that same LocalId.
        let TypedExpr::Call { callee, .. } = block.tail.as_deref().unwrap() else {
            panic!("tail is a call");
        };
        let TypedExpr::Ident(_, Some(crate::identity::BindingId::Local(used)), _, _) = &**callee
        else {
            panic!("callee `helper` is a local reference");
        };
        assert_eq!(
            *used, helper_id,
            "the call and the nested fn share one LocalId"
        );
    }

    #[test]
    fn assignment_to_a_top_level_var_carries_its_global_binding_id() {
        use crate::data::typed_ast::{TypedPlace, TypedStmt};
        let analysis = analyze(
            "var counter: i64 := 0;\n\
             fun bump() { counter := counter + 1; }\n",
        );
        let root = analysis
            .graph
            .modules
            .iter()
            .find(|m| m.module_path.is_empty())
            .unwrap();
        let TypedDecl::Fun(bump) = root
            .decls
            .iter()
            .find(|d| matches!(d, TypedDecl::Fun(f) if f.name == "bump"))
            .unwrap()
        else {
            unreachable!()
        };
        let FunBody::Typed(block) = &bump.body else {
            panic!("typed body")
        };
        let target_binding = block
            .stmts
            .iter()
            .find_map(|d| match d {
                TypedDecl::Stmt(s) => match &**s {
                    TypedStmt::Expr(TypedExpr::Assign {
                        target: TypedPlace::Ident(name, binding, _),
                        ..
                    }) if name == "counter" => Some(*binding),
                    _ => None,
                },
                _ => None,
            })
            .expect("a `counter := …` assignment");
        assert!(
            matches!(target_binding, Some(crate::identity::BindingId::Global(_))),
            "a top-level `var` assignment target resolves to its SymbolId: {target_binding:?}"
        );
    }

    #[test]
    fn assignment_target_ident_carries_the_local_binding_id() {
        use crate::data::typed_ast::{TypedPlace, TypedStmt};
        let analysis = analyze(
            "fun bump() -> i64 {\n\
             \tvar n := 1;\n\
             \tn := n + 1;\n\
             \tn\n\
             }\n",
        );
        let root = analysis
            .graph
            .modules
            .iter()
            .find(|m| m.module_path.is_empty())
            .unwrap();
        let TypedDecl::Fun(func) = root
            .decls
            .iter()
            .find(|d| matches!(d, TypedDecl::Fun(f) if f.name == "bump"))
            .unwrap()
        else {
            unreachable!()
        };
        let FunBody::Typed(block) = &func.body else {
            panic!("typed body")
        };
        let decl_id = block
            .stmts
            .iter()
            .find_map(|d| match d {
                TypedDecl::Mut(md) if md.name == "n" => md.local_id,
                _ => None,
            })
            .expect("`var n` carries a LocalId");
        let target_binding = block
            .stmts
            .iter()
            .find_map(|d| match d {
                TypedDecl::Stmt(s) => match &**s {
                    TypedStmt::Expr(TypedExpr::Assign {
                        target: TypedPlace::Ident(name, binding, _),
                        ..
                    }) if name == "n" => Some(*binding),
                    _ => None,
                },
                _ => None,
            })
            .expect("an `n := …` assignment");
        assert_eq!(
            target_binding,
            Some(crate::identity::BindingId::Local(decl_id)),
            "the assignment target resolves to the `var n` binding"
        );
    }
}

#[test]
fn virtual_analysis_reports_parse_errors_as_diagnostics() {
    let provider = InMemorySourceProvider::new("editor.mtl", "fun main(");
    let report =
        analyze_virtual_root_with_diagnostics("editor.mtl", &provider, AnalysisOptions::default());

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

// ── #1045: diagnostics accumulation ─────────────────────────────────────

#[test]
fn a_broken_sibling_file_does_not_sink_the_rest_of_the_project() {
    // metel-core#1045: a file that fails to parse used to abort loading
    // the entire graph -- one diagnostic and nothing else, for the whole
    // project, even for files with no relationship to the broken one.
    use crate::pipeline::parsing::module_loader::MultiFileSourceProvider;

    let provider = MultiFileSourceProvider::new(
        "editor.mtl",
        "import a::helper;\nimport b::broken;\nfun main() -> i64 { helper() }\n",
    )
    .with_file("a.mtl", "public fun helper() -> i64 { 42 }\n")
    // Missing closing paren -- a genuine parse error, not a semantic one.
    .with_file("b.mtl", "public fun broken( -> i64 { 1 }\n");

    let report =
        analyze_virtual_root_with_diagnostics("editor.mtl", &provider, AnalysisOptions::default());

    assert_eq!(
        report.diagnostics.len(),
        1,
        "exactly one diagnostic, for b.mtl: {:?}",
        report.diagnostics
    );
    assert!(
        report.diagnostics[0]
            .primary_span()
            .expect("parse error should be located")
            .filename
            .contains("b.mtl"),
        "the diagnostic should point at the broken file: {:?}",
        report.diagnostics[0]
    );

    let analysis = report
        .analysis
        .expect("the root and a.mtl should still analyze");
    let module_paths: Vec<&[String]> = analysis
        .graph
        .modules
        .iter()
        .map(|m| m.module_path.as_slice())
        .collect();
    assert!(
        module_paths.iter().any(|p| p.is_empty()),
        "the root module should still be typed: {module_paths:?}"
    );
    assert!(
        module_paths.contains(&["a".to_string()].as_slice()),
        "a.mtl should still be typed: {module_paths:?}"
    );
    assert!(
        !module_paths.contains(&["b".to_string()].as_slice()),
        "b.mtl never parsed, so it can't be in the typed graph: {module_paths:?}"
    );
}

#[test]
fn an_independent_type_error_does_not_sink_unrelated_modules() {
    // metel-core#1045: module `a` has its own, self-contained type error.
    // `b` has no relationship to `a` at all and should still fully
    // analyze; `c` imports `a` and should be skipped (not itself given a
    // misleading diagnostic) since its own check would be unreliable;
    // the root imports both `b` and `c`, so it transitively depends on
    // the failed `a` too and is skipped for the same reason `c` is.
    use crate::pipeline::parsing::module_loader::MultiFileSourceProvider;

    let provider = MultiFileSourceProvider::new(
        "editor.mtl",
        "import b::ok_fn;\nimport c::uses_a;\nfun main() -> i64 { ok_fn() }\n",
    )
    .with_file("a.mtl", "public fun bad() -> i64 { \"oops\" }\n")
    .with_file("b.mtl", "public fun ok_fn() -> i64 { 1 }\n")
    .with_file(
        "c.mtl",
        "import a::bad;\npublic fun uses_a() -> i64 { bad() }\n",
    );

    let report =
        analyze_virtual_root_with_diagnostics("editor.mtl", &provider, AnalysisOptions::default());

    assert_eq!(
        report.diagnostics.len(),
        1,
        "exactly one diagnostic, a's own type error: {:?}",
        report.diagnostics
    );
    assert!(
        report.diagnostics[0]
            .primary_span()
            .expect("type error should be located")
            .filename
            .contains("a.mtl"),
        "the diagnostic should point at a.mtl: {:?}",
        report.diagnostics[0]
    );

    let analysis = report.analysis.expect("b.mtl should still analyze");
    let module_paths: Vec<&[String]> = analysis
        .graph
        .modules
        .iter()
        .map(|m| m.module_path.as_slice())
        .collect();
    assert!(
        module_paths.contains(&["b".to_string()].as_slice()),
        "b.mtl is independent of a and should still be typed: {module_paths:?}"
    );
    assert!(
        !module_paths.contains(&["a".to_string()].as_slice()),
        "a.mtl failed and has no typed entry: {module_paths:?}"
    );
    assert!(
        !module_paths.contains(&["c".to_string()].as_slice()),
        "c.mtl depends on the failed a.mtl and should be skipped, not typed: {module_paths:?}"
    );
    assert!(
        analysis
            .skipped_modules
            .contains(&["c".to_string()].to_vec()),
        "c.mtl should be recorded as skipped: {:?}",
        analysis.skipped_modules
    );
    assert!(
        analysis.skipped_modules.contains(&Vec::new()),
        "the root transitively depends on the failed a.mtl via c and \
         should be skipped too: {:?}",
        analysis.skipped_modules
    );

    // b.mtl's own facts are fully queryable even though a.mtl and c.mtl
    // are not -- hover/goto-def degrade only for the affected subgraph.
    // The offset targets the body's `1` (a typed expression); the
    // function name itself has no expression node to hover.
    const B_SOURCE: &str = "public fun ok_fn() -> i64 { 1 }\n";
    let body_offset = B_SOURCE.rfind('1').expect("b.mtl's body is `1`");
    assert!(
        analysis.hover_at("b.mtl", body_offset).is_some(),
        "hover should still work inside the unaffected module"
    );
}
