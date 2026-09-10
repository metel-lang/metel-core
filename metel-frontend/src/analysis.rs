//! Frontend-only analysis API for tooling consumers.
//!
//! Unlike the interpreter pipeline, this module deliberately stops after
//! typechecking. It is the boundary for editor tooling, documentation tools,
//! and other consumers which need compiler facts but must never evaluate user
//! code.

use std::path::Path;

use crate::coherence;
use crate::error::MetelError;
use crate::identity::{self, MemberTable, ModuleTable, NameInterner, PositionIndex, ResolutionMap};
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
    /// Structural binding identities for every lexical binding and value
    /// reference (metel-core#1049). Identity-keyed; carries no source spans.
    pub resolution: ResolutionMap,
    /// Byte-offset → identity index for this snapshot (metel-core#1048). The
    /// only position-keyed structure; rebuilt per analysis, never a semantic
    /// input.
    pub positions: PositionIndex,
    /// The interner used to build `resolution`, for turning a `NameId` back
    /// into a spelling.
    pub name_interner: NameInterner,
    /// Identity for every declared struct field and enum variant
    /// (`FieldId` / `VariantId`), keyed by `(owning SymbolId, member name)`
    /// — the interning milestone of the resolution freeze (metel-core#1051,
    /// ADR-0054 step 3). Field accesses, enum-variant literals, and match
    /// patterns on the typed IR carry the matching id (metel-core#1062 /
    /// #1062b).
    pub members: MemberTable,
    /// Identity for every module namespace, interned from its canonical
    /// (alias-dereferenced) path (metel-core#1070). A module is not a value
    /// binding; module-segment go-to-definition resolves through this, keyed by
    /// `ModuleId`, not a `BindingId`.
    pub modules: ModuleTable,
    /// Non-fatal frontend diagnostics.
    pub warnings: Vec<String>,
}

impl Analysis {
    /// The innermost typed expression at a byte offset — hover.
    #[must_use]
    pub fn hover_at(
        &self,
        filename: &str,
        byte_offset: usize,
    ) -> Option<&crate::typed_ast::TypedExpr> {
        crate::query::expr_at(&self.graph, filename, byte_offset)
    }

    /// Where the identifier/path at a byte offset is defined — go-to-definition,
    /// covering lexical locals, module-qualified / imported globals
    /// (metel-core#1050), and module-path segments (metel-core#1070).
    #[must_use]
    pub fn definition_at(
        &self,
        filename: &str,
        byte_offset: usize,
    ) -> Option<crate::query::DefinitionSite<'_>> {
        crate::query::definition(
            &self.resolution,
            &self.positions,
            &self.names,
            &self.modules,
            filename,
            byte_offset,
        )
    }

    /// Every use site of the binding at a byte offset — find-references.
    #[must_use]
    pub fn references_at(&self, filename: &str, byte_offset: usize) -> Vec<&crate::ast::Span> {
        crate::query::references(&self.resolution, &self.positions, filename, byte_offset)
    }
}

/// The result of an editor-oriented analysis attempt.
///
/// Tooling receives diagnostics as data rather than as a `Result` error, so it
/// can publish them for an incomplete document without treating ordinary user
/// mistakes as a server failure. The initial frontend remains fail-fast within
/// a phase: the list contains the first blocking diagnostic. Parser recovery
/// and multi-error typechecking can extend this representation without changing
/// its callers.
#[derive(Debug)]
pub struct AnalysisReport {
    /// Analysis facts when every blocking frontend phase succeeded.
    pub analysis: Option<Analysis>,
    /// Source or frontend diagnostics collected during the attempt.
    pub diagnostics: Vec<MetelError>,
}

impl AnalysisReport {
    fn success(analysis: Analysis) -> Self {
        Self {
            analysis: Some(analysis),
            diagnostics: Vec::new(),
        }
    }

    fn failure(diagnostic: MetelError) -> Self {
        Self {
            analysis: None,
            diagnostics: vec![diagnostic],
        }
    }
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

/// Analyze an on-disk root and return diagnostics as data for tooling.
///
/// The command-line pipeline should continue to use [`analyze_root_with`] and
/// its fail-fast `Result`. This API is for long-lived editor processes, where a
/// malformed source document is expected and must not be reported as a server
/// failure.
#[must_use]
pub fn analyze_root_with_diagnostics<P: SourceProvider>(
    path: impl AsRef<Path>,
    provider: &P,
    options: AnalysisOptions,
) -> AnalysisReport {
    match analyze_root_with(path, provider, options) {
        Ok(analysis) => AnalysisReport::success(analysis),
        Err(diagnostic) => AnalysisReport::failure(diagnostic),
    }
}

/// Analyze a virtual root and return diagnostics as data for tooling.
///
/// See [`analyze_root_with_diagnostics`] for the initial fail-fast collection
/// boundary and its intended extension path.
#[must_use]
pub fn analyze_virtual_root_with_diagnostics<P: SourceProvider>(
    path: impl AsRef<Path>,
    provider: &P,
    options: AnalysisOptions,
) -> AnalysisReport {
    match analyze_virtual_root_with(path, provider, options) {
        Ok(analysis) => AnalysisReport::success(analysis),
        Err(diagnostic) => AnalysisReport::failure(diagnostic),
    }
}

fn analyze_graph(graph: ModuleGraph, options: AnalysisOptions) -> Result<Analysis, MetelError> {
    let names = name_resolver::resolve(&graph)?;

    // Structural identities are derived from the parsed graph, so allocate them
    // before `path_normalizer::normalize` consumes `graph`.
    let mut name_interner = NameInterner::new();
    let identity_modules: Vec<(Vec<String>, &[crate::ast::Decl])> = graph
        .modules
        .iter()
        .map(|module| (module.module_path.clone(), module.program.decls.as_slice()))
        .collect();

    // Intern every module namespace. Its `module_path` is already canonical
    // (the loader keeps one `LoadedModule` per physical file); its location is
    // the module file's start, the go-to-definition target for a module-path
    // segment (metel-core#1070).
    let mut modules = ModuleTable::new();
    for module in &graph.modules {
        let file = module.file_path.to_string_lossy().into_owned();
        modules.intern(&module.module_path, Some(crate::ast::Span::new(0, 0, file)));
    }

    let identity = identity::allocate_graph(
        &identity_modules,
        &names,
        &mut name_interner,
        identity::GraphModuleNav {
            table: &modules,
            aliases: &graph.path_aliases,
        },
    );
    let members = identity::collect_members(&identity_modules, &names, &mut name_interner);

    let normalized = path_normalizer::normalize(graph, &names)?;
    coherence::check(&normalized, &names)?;
    let report = typechecker::check_graph_with_report(
        &normalized,
        &names,
        &CorePrelude::default(),
        Some(identity::FrozenIdentity {
            members: &members,
            binding_spans: &identity.binding_spans,
        }),
    )?;

    let mut warnings = report.warnings;
    if options.move_check {
        warnings.extend(move_check::check_graph(&report.graph)?);
    }

    Ok(Analysis {
        graph: report.graph,
        names,
        resolution: identity.resolution,
        positions: identity.positions,
        name_interner,
        members,
        modules,
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

    // ── #1062 (Freeze 1051c): FieldId / VariantId on the typed IR ──────────────

    mod member_ids_on_typed_ir {
        use super::*;
        use crate::typed_ast::{FunBody, TypedDecl, TypedExpr, TypedMatchArm, TypedPattern};

        fn analyze(src: &str) -> Analysis {
            let provider = InMemorySourceProvider::new("editor.mtl", src);
            analyze_virtual_root_with("editor.mtl", &provider, AnalysisOptions::default())
                .expect("source should analyze")
        }

        fn root_sym(analysis: &Analysis, name: &str) -> crate::symbols::SymbolId {
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
            let TypedPattern::Record { fields, .. } = &match_arms(&analysis, "mag")[0].pattern
            else {
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
            use crate::typed_ast::TypedStmt;
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
        fn assignment_target_ident_carries_the_local_binding_id() {
            use crate::typed_ast::{TypedPlace, TypedStmt};
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
        let report = analyze_virtual_root_with_diagnostics(
            "editor.mtl",
            &provider,
            AnalysisOptions::default(),
        );

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
}
