use super::*;
use crate::pipeline::type_checking::type_engine::OverloadEntry;

fn entry(index: u32, params: Vec<Type>, ret: Type) -> OverloadEntry {
    OverloadEntry {
        params,
        ret,
        symbol_id: SymbolId::core_overload(index),
    }
}

/// Parse `source` and number its overloads the way a module of that path is numbered. `table`
/// stands for the resolver's one symbol table for the whole graph: every module's top-level
/// function names are interned into it, so two modules never share an overloaded name's symbol.
fn build_for_module(
    source: &str,
    module: &[&str],
    table: &mut crate::identity::symbols::SymbolTable,
) -> Result<OverloadTable, crate::data::error::MetelError> {
    let program =
        crate::pipeline::parsing::parser::parse(source, "<test>").expect("test source parses");
    let module: Vec<String> = module.iter().map(|m| (*m).to_string()).collect();
    for decl in &program.decls {
        if let Decl::Fun(f) = decl {
            table.intern(&module, &f.name);
        }
    }
    build_overload_table(
        &program.decls,
        &TypeDefinitionRegistry::new(),
        &module,
        &OverloadTable::new(),
        table.map(),
    )
}

fn fresh_table() -> crate::identity::symbols::SymbolTable {
    crate::identity::symbols::SymbolTable::new()
}

const TWO_OVERLOADS: &str =
    "fun f(x: i64) -> i64 { x }\nfun f(x: String) -> i64 { 0 }\nfun g(x: i64) -> i64 { x }\n";

fn ids_of(table: &OverloadTable, name: &str) -> Vec<SymbolId> {
    table[name].iter().map(|e| e.symbol_id).collect()
}

// metel-core#1546 / LIMIT-NAME-RESOLUTION-002: an overload's id is derived from the program, so
// numbering the same module again gives the same ids (a process-global counter would not).
#[test]
fn overload_ids_are_reproducible_across_builds_of_the_same_module() {
    let first = build_for_module(TWO_OVERLOADS, &["app"], &mut fresh_table()).unwrap();
    let second = build_for_module(TWO_OVERLOADS, &["app"], &mut fresh_table()).unwrap();
    assert_eq!(ids_of(&first, "f"), ids_of(&second, "f"));
    assert!(
        !first.contains_key("g"),
        "a lone function is not an overload group"
    );
}

#[test]
fn overloads_of_one_name_are_numbered_by_source_position() {
    let table = build_for_module(TWO_OVERLOADS, &["app"], &mut fresh_table()).unwrap();
    let ids = ids_of(&table, "f");
    assert_eq!(ids.len(), 2);
    assert_ne!(ids[0], ids[1]);
    assert!(ids.iter().all(|id| matches!(id, SymbolId::Overload(_))));
    // The first definition in source order takes ordinal 0: swapping the order swaps the ids.
    let swapped = "fun f(x: String) -> i64 { 0 }\nfun f(x: i64) -> i64 { x }\n";
    let swapped = build_for_module(swapped, &["app"], &mut fresh_table()).unwrap();
    assert_eq!(ids_of(&swapped, "f"), ids);
    assert_eq!(swapped["f"][0].params, vec![Type::Str]);
    assert_eq!(table["f"][0].params, vec![Type::I64]);
}

#[test]
fn two_modules_overloading_the_same_name_get_different_ids() {
    let mut graph_table = fresh_table();
    let a = build_for_module(TWO_OVERLOADS, &["a"], &mut graph_table).unwrap();
    let b = build_for_module(TWO_OVERLOADS, &["b"], &mut graph_table).unwrap();
    for id in ids_of(&a, "f") {
        assert!(
            !ids_of(&b, "f").contains(&id),
            "{id:?} appears in both modules"
        );
    }
}

#[test]
fn an_overloaded_name_without_a_resolved_symbol_is_an_internal_error() {
    let program = crate::pipeline::parsing::parser::parse(TWO_OVERLOADS, "<test>").unwrap();
    let err = build_overload_table(
        &program.decls,
        &TypeDefinitionRegistry::new(),
        &["app".to_string()],
        &OverloadTable::new(),
        &HashMap::new(),
    )
    .expect_err("no symbol for `f`");
    assert!(
        err.to_string().contains("no resolved symbol"),
        "unexpected error: {err}"
    );
}

#[test]
fn core_overload_ids_are_their_declaration_order_and_the_same_every_time() {
    let core = core_overload_table();
    // Rebuild from scratch: the ids must not depend on this process's table or hash seed.
    let rebuilt = build_table_from_decls(
        &crate::stdlib::core_program().decls,
        None,
        &mut OverloadIds::Core { next: 0 },
    )
    .unwrap();
    for (name, entries) in core {
        let again: Vec<SymbolId> = rebuilt[name].iter().map(|e| e.symbol_id).collect();
        let now: Vec<SymbolId> = entries.iter().map(|e| e.symbol_id).collect();
        assert_eq!(
            now, again,
            "core overload ids for `{name}` changed between builds"
        );
    }
    // Dense and in order: the first overloaded name in the core source takes index 0, and
    // the ids are exactly 0..n with no gaps.
    let total: usize = core.values().map(Vec::len).sum();
    let mut ids: Vec<SymbolId> = core.values().flatten().map(|e| e.symbol_id).collect();
    ids.sort_by_key(|id| format!("{id:?}"));
    let mut expected: Vec<SymbolId> = (0..total as u32).map(SymbolId::core_overload).collect();
    expected.sort_by_key(|id| format!("{id:?}"));
    assert_eq!(ids, expected);
    let first_overloaded = crate::stdlib::core_program()
        .decls
        .iter()
        .find_map(|d| match d {
            Decl::Fun(f) if core.contains_key(&f.name) => Some(f.name.clone()),
            _ => None,
        })
        .expect("core.mtl overloads at least one function");
    assert_eq!(
        core[&first_overloaded][0].symbol_id,
        SymbolId::core_overload(0)
    );
}

#[test]
fn select_requires_exact_match() {
    let entries = vec![
        entry(0, vec![Type::I32], Type::Unit),
        entry(1, vec![Type::I64], Type::Unit),
    ];
    // Exact match picks the right candidate.
    assert_eq!(
        select(&entries, &[Type::I32]).unwrap().symbol_id,
        entries[0].symbol_id
    );
    assert_eq!(
        select(&entries, &[Type::I64]).unwrap().symbol_id,
        entries[1].symbol_id
    );
    // No coercion: a type with no exact candidate does not match.
    assert!(select(&entries, &[Type::I16]).is_none());
    // Arity mismatch does not match.
    assert!(select(&entries, &[Type::I32, Type::I32]).is_none());
    assert!(select(&entries, &[]).is_none());
}

#[test]
fn select_distinguishes_by_arity() {
    let entries = vec![
        entry(0, vec![Type::I64], Type::I64),
        entry(1, vec![Type::I64, Type::I64], Type::I64),
    ];
    assert_eq!(select(&entries, &[Type::I64]).unwrap().params.len(), 1);
    assert_eq!(
        select(&entries, &[Type::I64, Type::I64])
            .unwrap()
            .params
            .len(),
        2
    );
}
