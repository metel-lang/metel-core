use super::*;

/// The non-comment lines of every `pipeline/type_checking/construction*` source file.
fn construction_code() -> Vec<(String, String)> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/pipeline/type_checking");
    let mut files = vec![root.join("construction.rs")];
    for entry in std::fs::read_dir(root.join("construction")).expect("construction/ exists") {
        files.push(entry.expect("dir entry").path());
    }
    files
        .into_iter()
        .map(|path| {
            let code = std::fs::read_to_string(&path)
                .expect("construction source readable")
                .lines()
                .filter(|line| !line.trim_start().starts_with("//"))
                .collect::<Vec<_>>()
                .join("\n");
            (path.display().to_string(), code)
        })
        .collect()
}

// arch-verifies: ["arch.resolution.requirement-3"]
#[test]
fn typed_ir_threads_member_ids_rather_than_rederiving_them() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/data/typed_ast.rs");
    let source = std::fs::read_to_string(path).expect("data/typed_ast.rs readable");
    assert!(
        source.contains("Option<FieldId>"),
        "typed field access/construction must carry a FieldId"
    );
    assert!(
        source.contains("Option<VariantId>"),
        "typed variant access/construction must carry a VariantId"
    );
}

// arch-verifies: ["arch.type-construction.requirement-6"]
#[test]
fn typed_ir_has_no_ascription_node() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/data/typed_ast.rs");
    let code = std::fs::read_to_string(&path).expect("data/typed_ast.rs readable");
    let code: String = code
        .lines()
        .filter(|line| !line.trim_start().starts_with("//"))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        !code.contains("Ascribe"),
        "{} defines an ascription node; ascriptions must be erased during construction",
        path.display()
    );
}

// arch-verifies: ["arch.type-inference.requirement-3"]
#[test]
fn from_impl_lookup_runs_in_inference_not_construction() {
    for (path, code) in construction_code() {
        assert!(
            !code.contains("has_from_impl"),
            "{path} looks up `From` impls; `?` coercion is decided in inference (`infer_propagate_error`)"
        );
    }
}

// arch-verifies: ["arch.type-inference.requirement-4"]
#[test]
fn construction_never_runs_the_constraint_solver() {
    for (path, code) in construction_code() {
        for forbidden in ["InferContext", ".solve(", "solve_constraints", "occurs_in"] {
            assert!(
                !code.contains(forbidden),
                "{path} references `{forbidden}`; construction consumes solved facts and must not re-run inference"
            );
        }
    }
}

/// The prelude's free-function schemes are derived from the embedded
/// std::core source (METEL-181); this asserts the derivation covers every
/// `native` declaration in core.mtl, so a new stdlib function can never
/// typecheck differently between the graph path (real module) and the
/// single-program path (prelude). Replaces the old hand-list parity test —
/// there is no longer a duplicated set to keep in sync.
#[test]
fn prelude_schemes_cover_embedded_core_natives() {
    let prelude = CorePrelude::default();
    let core_path = ["std".to_string(), "core".to_string()];
    let source = crate::stdlib::lookup(&core_path).expect("std::core is embedded");
    let program = crate::pipeline::parsing::parser::parse(source, "<embedded std::core>")
        .expect("core.mtl parses");

    let mut native_count = 0usize;
    for decl in &program.decls {
        if let Decl::Fun(fun) = decl {
            if fun.native.is_some() {
                native_count += 1;
                // Overloaded core natives (the assert pair) are dispatched
                // by SymbolId via the seeded overload table — they must
                // NOT appear in the name-keyed prelude.
                if overload::core_overload_table().contains_key(&fun.name) {
                    assert!(
                        !prelude.contains(&fun.name),
                        "overloaded std::core native `{}` must not be name-keyed in the prelude",
                        fun.name
                    );
                    assert!(
                        overload::core_native_symbol(fun).is_some(),
                        "overloaded std::core native `{}` must have a canonical SymbolId",
                        fun.name
                    );
                    continue;
                }
                assert!(
                    prelude.contains(&fun.name),
                    "prelude is missing a scheme for std::core native `{}`",
                    fun.name
                );
            }
        }
    }
    assert!(native_count > 0, "core.mtl should declare native functions");
}

/// metel-core#1052 (Option A): `construct_generic_body`'s runtime
/// reconstruction of a generic function body gets real `BindingId`s too,
/// not just the ahead-of-time construction pass — because `body` is the
/// exact same `ast::Block` the identity walk already processed, so its
/// `binding_spans` entries apply unchanged regardless of which concrete
/// type this particular call instantiates.
// arch-verifies: ["arch.type-construction.requirement-2"]
#[test]
fn construct_generic_body_stamps_a_real_local_id() {
    use crate::data::typed_ast::TypedExpr;
    use crate::data::types::Type;
    use crate::identity::{self, BindingId, FrozenIdentity};
    use crate::pipeline::parsing::module_loader::{self, InMemorySourceProvider};
    use std::rc::Rc;

    let root = "generic.mtl";
    let source = "fun pick<T>(a: T, b: T) -> T {\n\tlet r := a;\n\tr\n}\n";
    let provider = InMemorySourceProvider::new(root, source);
    let graph =
        module_loader::load_virtual_root_with(root, &provider).expect("in-memory root loads");
    let names = crate::pipeline::name_resolution::name_resolver::resolve(&graph).expect("resolves");
    let members = identity::collect_members_for_graph(&graph, &names);
    let allocation = identity::allocate_for_graph(&graph, &names);
    let normalized =
        crate::pipeline::path_normalization::normalize(graph, names.clone()).expect("normalizes");
    crate::pipeline::coherence::check(&normalized).expect("coheres");
    let typed_report = check_graph_with_report(
        &normalized,
        &CorePrelude::default(),
        Some(FrozenIdentity {
            members: &members,
            binding_spans: &allocation.binding_spans,
        }),
    )
    .expect("typechecks");

    // The raw (untyped) declaration — `construct_generic_body` takes the
    // same `ast::Block` the identity walk already saw. std::core is a
    // synthesized module ahead of the user's root, so find `pick` by name
    // rather than assuming module order.
    let module = normalized
        .modules()
        .iter()
        .find(|m| {
            m.program
                .decls
                .iter()
                .any(|d| matches!(d, Decl::Fun(f) if f.name == "pick"))
        })
        .expect("the module declaring `fun pick`");
    let Decl::Fun(fun) = module
        .program
        .decls
        .iter()
        .find(|d| matches!(d, Decl::Fun(f) if f.name == "pick"))
        .expect("`fun pick` in the raw graph")
    else {
        unreachable!()
    };
    let typed_module = typed_report
        .graph
        .modules
        .iter()
        .find(|m| m.module_path == module.module_path)
        .expect("the matching typed module");
    let scheme = typed_module
        .scheme_env
        .get("pick")
        .expect("a scheme for `pick`")
        .clone();

    let type_ctx = crate::pipeline::type_checking::typeinference::TypeCtx {
        scheme_env: typed_module.scheme_env.clone(),
        registry: typed_report.graph.type_registry.clone(),
        members: Some(Rc::new(members)),
        binding_spans: Some(Rc::new(allocation.binding_spans)),
        symbols: Some(Rc::new(names.symbols.clone())),
        current_module: typed_module.module_path.clone(),
    };

    let typed_block = construct_generic_body(
        &scheme,
        &fun.params,
        &[Type::I64, Type::I64],
        &fun.body,
        &fun.span,
        &type_ctx,
        None,
    )
    .expect("reconstructs for i64 args");

    let r_id = typed_block
        .stmts
        .iter()
        .find_map(|d| match d {
            TypedDecl::Let(ld) if ld.name == "r" => ld.local_id,
            _ => None,
        })
        .expect("a local in a runtime-reconstructed generic body carries a LocalId");
    let TypedExpr::Ident(_, Some(BindingId::Local(used)), _, _) =
        typed_block.tail.as_deref().unwrap()
    else {
        panic!("the tail `r` should be a resolved local reference");
    };
    assert_eq!(
        *used, r_id,
        "the reconstructed body's `r` use resolves to the same LocalId as its `let`"
    );

    // Reconstructing the same generic body for a *different* concrete
    // instantiation yields the same `LocalId` for `r` — a binding's
    // lexical identity does not depend on which type parameterized this
    // particular call (relevant to go-to-definition / find-references
    // across monomorphizations).
    let typed_block_str = construct_generic_body(
        &scheme,
        &fun.params,
        &[Type::Str, Type::Str],
        &fun.body,
        &fun.span,
        &type_ctx,
        None,
    )
    .expect("reconstructs for str args");
    let r_id_str = typed_block_str
        .stmts
        .iter()
        .find_map(|d| match d {
            TypedDecl::Let(ld) if ld.name == "r" => ld.local_id,
            _ => None,
        })
        .expect("`let r` carries a LocalId in the str instantiation too");
    assert_eq!(
        r_id, r_id_str,
        "the same source binding keeps one LocalId across monomorphizations"
    );
}

/// metel-core#1098: `expr?` desugars (in `construct_propagate_error`) into
/// a synthesized match with an `Ok`-arm `value` binding and an `Err`-arm
/// `error` binding — neither has a source pattern to hang an id off, so
/// the identity walk binds one synthetic id at the `?`'s own span
/// (`allocate.rs`'s `PropagateError` case) and construction shares it
/// between both arms, since they're mutually exclusive at runtime.
#[test]
fn propagate_error_desugar_shares_one_local_id_between_arms() {
    use crate::data::typed_ast::{FunBody, TypedExpr, TypedPattern};
    use crate::identity::{self, FrozenIdentity};
    use crate::pipeline::parsing::module_loader::{self, InMemorySourceProvider};

    let root = "prop.mtl";
    let source = "fun get_id() -> Result<i64, i64> { Result::Ok { value = 5 } }\n\
                       fun use_it() -> Result<i64, i64> {\n\
                       \tlet v := get_id()?;\n\
                       \tResult::Ok { value = v }\n\
                       }\n";
    let provider = InMemorySourceProvider::new(root, source);
    let graph =
        module_loader::load_virtual_root_with(root, &provider).expect("in-memory root loads");
    let names = crate::pipeline::name_resolution::name_resolver::resolve(&graph).expect("resolves");
    let members = identity::collect_members_for_graph(&graph, &names);
    let allocation = identity::allocate_for_graph(&graph, &names);
    let normalized =
        crate::pipeline::path_normalization::normalize(graph, names.clone()).expect("normalizes");
    crate::pipeline::coherence::check(&normalized).expect("coheres");
    let typed_report = check_graph_with_report(
        &normalized,
        &CorePrelude::default(),
        Some(FrozenIdentity {
            members: &members,
            binding_spans: &allocation.binding_spans,
        }),
    )
    .expect("typechecks");

    let module = typed_report
        .graph
        .modules
        .iter()
        .find(|m| {
            m.decls
                .iter()
                .any(|d| matches!(d, TypedDecl::Fun(f) if f.name == "use_it"))
        })
        .expect("the module declaring `use_it`");
    let TypedDecl::Fun(fun) = module
        .decls
        .iter()
        .find(|d| matches!(d, TypedDecl::Fun(f) if f.name == "use_it"))
        .expect("`use_it`")
    else {
        unreachable!()
    };
    let FunBody::Typed(body) = &fun.body else {
        panic!("use_it should have a typed body");
    };
    let match_expr = body
        .stmts
        .iter()
        .find_map(|d| match d {
            TypedDecl::Let(ld) if ld.name == "v" => match &ld.value {
                TypedExpr::Match(m) => Some(m),
                _ => None,
            },
            _ => None,
        })
        .expect("the `?` desugars to a match assigned to `v`");

    let ok_id = match &match_expr.arms[0].pattern {
        TypedPattern::EnumVariant { fields, .. } => fields[0].2,
        other => panic!("expected the Ok-arm's EnumVariant pattern, got {other:?}"),
    };
    let err_id = match &match_expr.arms[1].pattern {
        TypedPattern::EnumVariant { fields, .. } => fields[0].2,
        other => panic!("expected the Err-arm's EnumVariant pattern, got {other:?}"),
    };
    assert!(
        ok_id.is_some(),
        "the `?` desugar's Ok-arm binding should carry a LocalId"
    );
    assert_eq!(
        ok_id, err_id,
        "the Ok-arm value and Err-arm error share one LocalId \
             (mutually exclusive match arms, safe to share one frame slot)"
    );
}

/// metel-core#1100: a top-level `let`/`mut`'s own initializer expression
/// is now walked by the identity allocator (`allocate.rs`'s
/// `walk_value_body`, wired into `allocate_module`'s top-level loop) —
/// previously only `Decl::Fun`/`Impl`/`Aspect` bodies were, so a
/// reference *inside* a top-level initializer (e.g. `let apply_fn :=
/// add_one;`) never got a `PositionHit::Reference` entry to promote and
/// stayed `BindingId`-less. This also fixed metel-core#1099 as a side
/// effect: a top-level `let`-bound closure literal's own parameters are
/// inside that same never-walked initializer.
#[test]
fn toplevel_let_initializer_reference_carries_a_symbol_id() {
    use crate::data::typed_ast::{FunBody, TypedExpr};
    use crate::identity::{self, BindingId, FrozenIdentity};
    use crate::pipeline::parsing::module_loader::{self, InMemorySourceProvider};

    let root = "toplevel_init.mtl";
    let source = "fun add_one(x: i64) -> i64 { x + 1 }\n\
                       let apply_fn := add_one;\n\
                       fun main() -> i64 {\n\
                       \tapply_fn(41)\n\
                       }\n";
    let provider = InMemorySourceProvider::new(root, source);
    let graph =
        module_loader::load_virtual_root_with(root, &provider).expect("in-memory root loads");
    let names = crate::pipeline::name_resolution::name_resolver::resolve(&graph).expect("resolves");
    let members = identity::collect_members_for_graph(&graph, &names);
    let allocation = identity::allocate_for_graph(&graph, &names);
    let normalized =
        crate::pipeline::path_normalization::normalize(graph, names.clone()).expect("normalizes");
    crate::pipeline::coherence::check(&normalized).expect("coheres");
    let typed_report = check_graph_with_report(
        &normalized,
        &CorePrelude::default(),
        Some(FrozenIdentity {
            members: &members,
            binding_spans: &allocation.binding_spans,
        }),
    )
    .expect("typechecks");

    let module = typed_report
        .graph
        .modules
        .iter()
        .find(|m| {
            m.decls
                .iter()
                .any(|d| matches!(d, TypedDecl::Let(ld) if ld.name == "apply_fn"))
        })
        .expect("the module declaring `apply_fn`");
    let TypedDecl::Let(apply_fn) = module
        .decls
        .iter()
        .find(|d| matches!(d, TypedDecl::Let(ld) if ld.name == "apply_fn"))
        .expect("`let apply_fn`")
    else {
        unreachable!()
    };
    let TypedExpr::Ident(name, binding, ..) = &apply_fn.value else {
        panic!(
            "apply_fn's initializer should be a bare Ident reference to `add_one`, got {:?}",
            apply_fn.value
        );
    };
    assert_eq!(name, "add_one");
    assert!(
        matches!(binding, Some(BindingId::Global(_))),
        "the `add_one` reference inside apply_fn's own initializer should \
             carry its declaration's SymbolId, not stay identity-less"
    );

    // The call inside `main` still resolves through `Call::callee_id`, as
    // it did before this fix (this file's earlier check makes sure the
    // fix didn't regress the already-working case).
    let TypedDecl::Fun(main) = module
        .decls
        .iter()
        .find(|d| matches!(d, TypedDecl::Fun(f) if f.name == "main"))
        .expect("`main`")
    else {
        unreachable!()
    };
    let FunBody::Typed(body) = &main.body else {
        panic!("main should have a typed body");
    };
    let TypedExpr::Call { callee_id, .. } = body.tail.as_deref().unwrap() else {
        panic!(
            "main's tail should be the apply_fn(41) call, got {:?}",
            body.tail
        );
    };
    assert!(
        callee_id.is_some(),
        "apply_fn(41) should still dispatch via Call::callee_id"
    );
}

/// metel-core#1096: an implicit (no `[...]` list) closure's free
/// `Copy`-typed variables are materialized as `CaptureSpec::Clone`
/// entries (`verify_closure_capture_list`'s new return value), each
/// carrying the same `LocalId` as its enclosing binding — here,
/// `make_adder`'s own parameter `x`, captured implicitly by the closure
/// it returns.
#[test]
fn implicit_copy_capture_carries_the_enclosing_local_id() {
    use crate::data::typed_ast::{FunBody, TypedExpr};
    use crate::identity::{self, FrozenIdentity};
    use crate::pipeline::parsing::module_loader::{self, InMemorySourceProvider};

    let root = "implicit_capture.mtl";
    let source = "fun make_adder(x: i64) -> |i64| -> i64 {\n\
                       \t|y: i64| -> i64 { x + y }\n\
                       }\n\
                       fun main() -> i64 {\n\
                       \tlet add5 := make_adder(5);\n\
                       \tadd5(3)\n\
                       }\n";
    let provider = InMemorySourceProvider::new(root, source);
    let graph =
        module_loader::load_virtual_root_with(root, &provider).expect("in-memory root loads");
    let names = crate::pipeline::name_resolution::name_resolver::resolve(&graph).expect("resolves");
    let members = identity::collect_members_for_graph(&graph, &names);
    let allocation = identity::allocate_for_graph(&graph, &names);
    let normalized =
        crate::pipeline::path_normalization::normalize(graph, names.clone()).expect("normalizes");
    crate::pipeline::coherence::check(&normalized).expect("coheres");
    let typed_report = check_graph_with_report(
        &normalized,
        &CorePrelude::default(),
        Some(FrozenIdentity {
            members: &members,
            binding_spans: &allocation.binding_spans,
        }),
    )
    .expect("typechecks");

    let module = typed_report
        .graph
        .modules
        .iter()
        .find(|m| {
            m.decls
                .iter()
                .any(|d| matches!(d, TypedDecl::Fun(f) if f.name == "make_adder"))
        })
        .expect("the module declaring `make_adder`");
    let TypedDecl::Fun(fun) = module
        .decls
        .iter()
        .find(|d| matches!(d, TypedDecl::Fun(f) if f.name == "make_adder"))
        .expect("`make_adder`")
    else {
        unreachable!()
    };
    let FunBody::Typed(body) = &fun.body else {
        panic!("make_adder should have a typed body");
    };
    let TypedExpr::Closure {
        captures,
        capture_ids,
        ..
    } = body.tail.as_deref().unwrap()
    else {
        panic!(
            "make_adder's tail should be the inner closure, got {:?}",
            body.tail
        );
    };
    assert_eq!(
        captures.len(),
        1,
        "the implicit closure should materialize one capture for `x`, got {captures:?}"
    );
    assert!(
        matches!(&captures[0], crate::data::ast::CaptureSpec::Clone { name, .. } if name == "x"),
        "the materialized capture should be a Clone of `x`, got {:?}",
        captures[0]
    );
    assert_eq!(
        capture_ids, &fun.param_ids,
        "the materialized capture's LocalId should match make_adder's own \
             parameter x's LocalId — same binding, same identity"
    );
    assert!(
        matches!(capture_ids[0], Some(_)),
        "the capture should carry a real LocalId, not None"
    );
}

/// metel-core#1101: `extend<T> T[]: Aspect { ... }` (the structural
/// array-pattern target) previously had no `SymbolId` interned for its
/// methods at all -- `name_resolver.rs`'s `impl_target_name` and
/// `identity/allocate.rs`'s `allocate_module` both only recognized
/// `TypeExpr::Named` targets, silently skipping `TypeExpr::Array` ones.
/// With no owner `SymbolId` to hash against, every local inside such a
/// method's body -- including `self` -- got no `LocalId` at all. Both
/// now key these under a synthetic owner name ("[]Array" as of
/// metel-core#1121, originally the bare "Array" until that collided with
/// a literal `extend Array: Aspect { ... }` nominal target).
#[test]
fn array_extend_method_self_param_carries_a_local_id() {
    use crate::identity::{self, FrozenIdentity};
    use crate::pipeline::parsing::module_loader::{self, InMemorySourceProvider};

    let root = "array_extend.mtl";
    let source = "aspect Show {\n\
                       \tfun show(&self) -> i64;\n\
                       }\n\
                       extend<T> T[]: Show {\n\
                       \tfun show(&self) -> i64 {\n\
                       \t\tvar n := 0;\n\
                       \t\tfor (item in self) {\n\
                       \t\t\tn += 1;\n\
                       \t\t}\n\
                       \t\treturn n;\n\
                       \t}\n\
                       }\n\
                       fun main() -> i64 {\n\
                       \t[1, 2, 3].show()\n\
                       }\n";
    let provider = InMemorySourceProvider::new(root, source);
    let graph =
        module_loader::load_virtual_root_with(root, &provider).expect("in-memory root loads");
    let names = crate::pipeline::name_resolution::name_resolver::resolve(&graph).expect("resolves");
    let members = identity::collect_members_for_graph(&graph, &names);
    let allocation = identity::allocate_for_graph(&graph, &names);
    let normalized =
        crate::pipeline::path_normalization::normalize(graph, names.clone()).expect("normalizes");
    crate::pipeline::coherence::check(&normalized).expect("coheres");
    let typed_report = check_graph_with_report(
        &normalized,
        &CorePrelude::default(),
        Some(FrozenIdentity {
            members: &members,
            binding_spans: &allocation.binding_spans,
        }),
    )
    .expect("typechecks");

    let method = typed_report
        .graph
        .modules
        .iter()
        .find_map(|m| {
            m.decls.iter().find_map(|d| match d {
                TypedDecl::Impl(ib)
                    if matches!(ib.target_type, crate::data::ast::TypeExpr::Array(_)) =>
                {
                    ib.methods.iter().find(|f| f.name == "show")
                }
                _ => None,
            })
        })
        .expect("the array-extend impl's `show` method");
    assert!(
        !method.param_ids.is_empty(),
        "show(&self) should have at least one param_ids entry"
    );
    assert!(
        method.param_ids[0].is_some(),
        "the self param should carry a real LocalId, not None"
    );
}

#[test]
fn nominal_array_extend_does_not_collide_with_structural_array_extend() {
    // metel-core#1121: a literal `extend Array: Aspect { ... }` (a real,
    // reachable nominal impl target -- `Array` is accepted as a written
    // type name, see `conversions.rs`'s `("Array", 1)` case) used to be
    // keyed under the exact same synthetic owner name ("Array") as
    // `extend<T> T[]: Aspect { ... }` (the structural array-pattern
    // target, metel-core#1101). With the same owner and the same lexical
    // shape (one `var` binding named `n`), both methods' locals hashed
    // to the *same* LocalId. Fixed by keying the structural case under
    // "[]Array" instead, a string no `TypeExpr::Named` target can ever
    // spell (Metel identifiers can't contain `[`/`]`).
    use crate::identity::{self, FrozenIdentity};
    use crate::pipeline::parsing::module_loader::{self, InMemorySourceProvider};

    let root = "array_owner_collision.mtl";
    let source = "aspect Show {\n\
                       \tfun show(&self) -> i64;\n\
                       }\n\
                       extend Array: Show {\n\
                       \tfun show(&self) -> i64 {\n\
                       \t\tvar n := 1;\n\
                       \t\tn\n\
                       \t}\n\
                       }\n\
                       extend<T> T[]: Show {\n\
                       \tfun show(&self) -> i64 {\n\
                       \t\tvar n := 2;\n\
                       \t\tn\n\
                       \t}\n\
                       }\n\
                       fun main() -> i64 {\n\
                       \t[1, 2, 3].show()\n\
                       }\n";
    let provider = InMemorySourceProvider::new(root, source);
    let graph =
        module_loader::load_virtual_root_with(root, &provider).expect("in-memory root loads");
    let names = crate::pipeline::name_resolution::name_resolver::resolve(&graph).expect("resolves");
    let members = identity::collect_members_for_graph(&graph, &names);
    let allocation = identity::allocate_for_graph(&graph, &names);
    let normalized =
        crate::pipeline::path_normalization::normalize(graph, names.clone()).expect("normalizes");
    crate::pipeline::coherence::check(&normalized).expect("coheres");
    let typed_report = check_graph_with_report(
        &normalized,
        &CorePrelude::default(),
        Some(FrozenIdentity {
            members: &members,
            binding_spans: &allocation.binding_spans,
        }),
    )
    .expect("typechecks");

    // Search across every module's decls, not just the root's own --
    // std::core's prelude has its own `extend<T> T[]: ...` impls loaded
    // alongside it, so restricting to "the first module with an Impl
    // decl" would find the wrong module entirely.
    let all_decls = typed_report
        .graph
        .modules
        .iter()
        .flat_map(|m| m.decls.iter());
    let nominal_self_id = all_decls
            .clone()
            .find_map(|d| match d {
                TypedDecl::Impl(ib)
                    if matches!(&ib.target_type, crate::data::ast::TypeExpr::Named(n, _) if n == "Array") =>
                {
                    ib.methods.iter().find(|f| f.name == "show")
                }
                _ => None,
            })
            .expect("the nominal `extend Array` impl's `show` method")
            .param_ids[0]
            .expect("nominal self param should carry a real LocalId");
    let structural_self_id = all_decls
        .clone()
        .find_map(|d| match d {
            TypedDecl::Impl(ib)
                if matches!(ib.target_type, crate::data::ast::TypeExpr::Array(_)) =>
            {
                ib.methods.iter().find(|f| f.name == "show")
            }
            _ => None,
        })
        .expect("the structural `extend<T> T[]` impl's `show` method")
        .param_ids[0]
        .expect("structural self param should carry a real LocalId");

    assert_ne!(
        nominal_self_id, structural_self_id,
        "the nominal and structural Array impls' self params must not \
             collide onto the same LocalId"
    );
}

#[test]
fn qualified_path_static_method_call_carries_a_type_id() {
    // metel-core#1093: a static-method reference (`Type::method`,
    // resolved via `ctx.method_env`) constructs a `TypedExpr::Path` — it
    // should carry the owning type's SymbolId.
    //
    // The sibling case (a fieldful enum-variant path used as a curried
    // constructor value, e.g. `Colour::Custom`) is stamped by the same
    // construction code with a `variant_id` too, but isn't covered here:
    // that surface form doesn't type-check at all today (metel-core#1108,
    // a separate, pre-existing inference gap found while writing this
    // test) — every real fieldful-variant reference in the codebase goes
    // through `match` or an immediate struct literal instead, neither of
    // which builds a `TypedExpr::Path`.
    use crate::data::typed_ast::{FunBody, TypedExpr};
    use crate::identity::{self, FrozenIdentity};
    use crate::pipeline::parsing::module_loader::{self, InMemorySourceProvider};

    let root = "qualified_path.mtl";
    let source = "struct Point {\n\
                       \tx: i64,\n\
                       }\n\
                       extend Point {\n\
                       \tfun origin() -> Point {\n\
                       \t\tPoint { x = 0 }\n\
                       \t}\n\
                       }\n\
                       fun main() -> i64 {\n\
                       \tlet p := Point::origin();\n\
                       \tp.x\n\
                       }\n";
    let provider = InMemorySourceProvider::new(root, source);
    let graph =
        module_loader::load_virtual_root_with(root, &provider).expect("in-memory root loads");
    let names = crate::pipeline::name_resolution::name_resolver::resolve(&graph).expect("resolves");
    let members = identity::collect_members_for_graph(&graph, &names);
    let allocation = identity::allocate_for_graph(&graph, &names);
    let normalized =
        crate::pipeline::path_normalization::normalize(graph, names.clone()).expect("normalizes");
    crate::pipeline::coherence::check(&normalized).expect("coheres");
    let typed_report = check_graph_with_report(
        &normalized,
        &CorePrelude::default(),
        Some(FrozenIdentity {
            members: &members,
            binding_spans: &allocation.binding_spans,
        }),
    )
    .expect("typechecks");

    let main_body = typed_report
        .graph
        .modules
        .iter()
        .find_map(|m| {
            m.decls.iter().find_map(|d| match d {
                TypedDecl::Fun(f) if f.name == "main" => match &f.body {
                    FunBody::Typed(block) => Some(block),
                    _ => None,
                },
                _ => None,
            })
        })
        .expect("typed `main` body");

    let value = main_body
        .stmts
        .iter()
        .find_map(|d| match d {
            TypedDecl::Let(l) if l.name == "p" => Some(&l.value),
            _ => None,
        })
        .expect("`let p` not found");
    let (type_id, variant_id) = match value {
        TypedExpr::Call { callee, .. } => match callee.as_ref() {
            TypedExpr::Path {
                type_id,
                variant_id,
                ..
            } => (*type_id, *variant_id),
            other => panic!("callee is not a Path: {other:?}"),
        },
        other => panic!("`p`'s value is not a Call: {other:?}"),
    };
    assert!(
        type_id.is_some(),
        "Point::origin()'s callee Path should carry Point's SymbolId"
    );
    assert!(
        variant_id.is_none(),
        "a static method is not a variant constructor"
    );
}

#[test]
fn record_projection_base_carries_its_binding_id() {
    // metel-core#1054 (record-projection identity slice): `self.{ fd }`'s
    // base is re-typed as a synthesised `Ident` node; it should resolve
    // to `self`'s own `LocalId`, the same as any other reference to
    // `self` in the method body, not `None`.
    use crate::data::typed_ast::{FunBody, TypedExpr};
    use crate::identity::{self, BindingId, FrozenIdentity};
    use crate::pipeline::parsing::module_loader::{self, InMemorySourceProvider};

    let root = "record_projection.mtl";
    let source = "struct Handle {\n\
                       \tfd: i64,\n\
                       }\n\
                       extend Handle {\n\
                       \tfun narrow(self) -> i64 {\n\
                       \t\tlet r := self.{ fd };\n\
                       \t\tr.fd\n\
                       \t}\n\
                       }\n\
                       fun main() -> i64 {\n\
                       \tHandle { fd = 5 }.narrow()\n\
                       }\n";
    let provider = InMemorySourceProvider::new(root, source);
    let graph =
        module_loader::load_virtual_root_with(root, &provider).expect("in-memory root loads");
    let names = crate::pipeline::name_resolution::name_resolver::resolve(&graph).expect("resolves");
    let members = identity::collect_members_for_graph(&graph, &names);
    let allocation = identity::allocate_for_graph(&graph, &names);
    let normalized =
        crate::pipeline::path_normalization::normalize(graph, names.clone()).expect("normalizes");
    crate::pipeline::coherence::check(&normalized).expect("coheres");
    let typed_report = check_graph_with_report(
        &normalized,
        &CorePrelude::default(),
        Some(FrozenIdentity {
            members: &members,
            binding_spans: &allocation.binding_spans,
        }),
    )
    .expect("typechecks");

    let narrow_body = typed_report
        .graph
        .modules
        .iter()
        .find_map(|m| {
            m.decls.iter().find_map(|d| match d {
                TypedDecl::Impl(ib) => ib.methods.iter().find_map(|f| {
                    if f.name == "narrow" {
                        match &f.body {
                            FunBody::Typed(block) => Some(block),
                            _ => None,
                        }
                    } else {
                        None
                    }
                }),
                _ => None,
            })
        })
        .expect("typed `narrow` body");

    let value = narrow_body
        .stmts
        .iter()
        .find_map(|d| match d {
            TypedDecl::Let(l) if l.name == "r" => Some(&l.value),
            _ => None,
        })
        .expect("`let r` not found");
    let object = match value {
        TypedExpr::RecordLiteral { fields, .. } => match fields.as_slice() {
            [(_, TypedExpr::FieldAccess { object, .. })] => object.as_ref(),
            other => panic!("expected one projected field, got {other:?}"),
        },
        other => panic!("`r`'s value is not a RecordLiteral: {other:?}"),
    };
    match object {
        TypedExpr::Ident(name, binding, ..) => {
            assert_eq!(name, "self");
            assert!(
                matches!(binding, Some(BindingId::Local(_))),
                "self.{{ fd }}'s base should carry self's LocalId, not {binding:?}"
            );
        }
        other => panic!("projection base is not an Ident: {other:?}"),
    }
}

#[test]
fn toplevel_bare_statement_reference_carries_a_symbol_id() {
    // metel-core#1116: a bare top-level statement (`w.get();`, outside any
    // `fun`) referencing an earlier top-level `let` -- the identity
    // walker's own module-level dispatch never visits `Decl::Stmt` at all
    // (it only descends into `Fun`/`Let`/`Mut`/`Impl`/`Aspect` bodies), so
    // this reference has no `binding_spans` entry of its own. Construction
    // falls back to the reference-resolver's separate `Def` table (a
    // whole-module walk that does cover bare statements) -- verified here
    // by checking the receiver Ident still carries a real SymbolId.
    use crate::data::typed_ast::{TypedExpr, TypedStmt};
    use crate::identity::{self, FrozenIdentity};
    use crate::pipeline::parsing::module_loader::{self, InMemorySourceProvider};

    let root = "toplevel_stmt.mtl";
    let source = "struct Wrapper {\n\
                       \tn: i64,\n\
                       }\n\
                       extend Wrapper {\n\
                       \tfun get(self) -> i64 {\n\
                       \t\tself.n\n\
                       \t}\n\
                       }\n\
                       let w := Wrapper { n = 5 };\n\
                       w.get();\n";
    let provider = InMemorySourceProvider::new(root, source);
    let graph =
        module_loader::load_virtual_root_with(root, &provider).expect("in-memory root loads");
    let names = crate::pipeline::name_resolution::name_resolver::resolve(&graph).expect("resolves");
    let members = identity::collect_members_for_graph(&graph, &names);
    let allocation = identity::allocate_for_graph(&graph, &names);
    let normalized =
        crate::pipeline::path_normalization::normalize(graph, names.clone()).expect("normalizes");
    crate::pipeline::coherence::check(&normalized).expect("coheres");
    let typed_report = check_graph_with_report(
        &normalized,
        &CorePrelude::default(),
        Some(FrozenIdentity {
            members: &members,
            binding_spans: &allocation.binding_spans,
        }),
    )
    .expect("typechecks");

    let stmt = typed_report
        .graph
        .modules
        .iter()
        .find_map(|m| {
            m.decls.iter().find_map(|d| match d {
                TypedDecl::Stmt(s) => Some(s.as_ref()),
                _ => None,
            })
        })
        .expect("the top-level `w.get();` statement");
    let binding = match stmt {
        TypedStmt::Expr(TypedExpr::MethodCall { receiver, .. }) => match receiver.as_ref() {
            TypedExpr::Ident(_, binding, ..) => *binding,
            other => panic!("receiver is not an Ident: {other:?}"),
        },
        other => panic!("not a MethodCall statement: {other:?}"),
    };
    assert!(
        binding.is_some(),
        "w's reference in the top-level statement should carry a real BindingId, not None"
    );
}
