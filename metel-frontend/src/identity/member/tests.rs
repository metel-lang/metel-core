use std::collections::HashMap;
use std::path::PathBuf;

use crate::pipeline::name_resolution::name_resolver::resolve;
use crate::pipeline::parsing::module_loader::{LoadedModule, ModuleGraph};

use super::super::NameInterner;
use super::collect_members;

fn members(
    source: &str,
) -> (
    super::MemberTable,
    std::rc::Rc<crate::pipeline::name_resolution::name_resolver::ResolvedNames>,
) {
    let program = crate::pipeline::parsing::parser::parse(source, "test.mtl").expect("parse");
    let graph = ModuleGraph {
        root: PathBuf::from("test.mtl"),
        modules: vec![LoadedModule {
            module_path: vec![],
            file_path: PathBuf::from("test.mtl"),
            program,
        }],
        path_aliases: HashMap::new(),
    };
    let names = resolve(&graph).expect("resolve");
    let modules = vec![(vec![], graph.modules[0].program.decls.as_slice())];
    let mut interner = NameInterner::new();
    let table = collect_members(&modules, &names, &mut interner);
    (table, names)
}

fn sym(
    names: &crate::pipeline::name_resolution::name_resolver::ResolvedNames,
    name: &str,
) -> super::SymbolId {
    *names
        .symbols
        .get(&(vec![], name.to_string()))
        .unwrap_or_else(|| panic!("`{name}` interned"))
}

// arch-verifies: ["arch.resolution.requirement-3"]
#[test]
fn struct_fields_get_distinct_ids_owned_by_the_struct() {
    let (t, names) = members("struct Point { x: i64, y: i64 }");
    let p = sym(&names, "Point");
    let x = t.field(p, "x").expect("x");
    let y = t.field(p, "y").expect("y");
    assert_ne!(x, y);
    assert_eq!(t.field_count(), 2);
    assert_eq!(t.field_info(x).map(|i| i.owner), Some(p));
}

// arch-verifies: ["arch.resolution.requirement-3"]
#[test]
fn same_field_name_on_different_types_is_a_different_id() {
    let (t, names) = members("struct A { v: i64 }\nstruct B { v: i64 }");
    let a = sym(&names, "A");
    let b = sym(&names, "B");
    assert_ne!(
        t.field(a, "v").unwrap(),
        t.field(b, "v").unwrap(),
        "the owner is part of the key"
    );
}

// arch-verifies: ["arch.resolution.requirement-3"]
#[test]
fn enum_variants_and_their_fields_are_interned() {
    let (t, names) = members("enum E { A { x: i64 }, B { x: i64 } }");
    let e = sym(&names, "E");
    let a = t.variant(e, "A").expect("A");
    let b = t.variant(e, "B").expect("B");
    assert_ne!(a, b);
    // Variant-qualified field names keep `A.x` and `B.x` distinct.
    assert_ne!(
        t.field(e, "A::x").unwrap(),
        t.field(e, "B::x").unwrap(),
        "variant-qualified field keys stay distinct"
    );
    assert_eq!(t.variant_count(), 2);
}

// arch-verifies: ["arch.resolution.requirement-3"]
#[test]
fn interning_is_reformat_stable_and_order_independent() {
    let tight = "struct S { a: i64, b: i64 } enum E { V { c: i64 } }";
    let loose = "struct S {\n\n a: i64,\n\n  b: i64,\n}\n\nenum E {\n V { c: i64 },\n}\n";
    let (t1, n1) = members(tight);
    let (t2, n2) = members(loose);

    let s1 = sym(&n1, "S");
    let s2 = sym(&n2, "S");
    assert_eq!(t1.field(s1, "a"), t2.field(s2, "a"));
    assert_eq!(t1.field(s1, "b"), t2.field(s2, "b"));

    // Two runs over the same source produce identical ids.
    let (t3, n3) = members(tight);
    let s3 = sym(&n3, "S");
    assert_eq!(t1.field(s1, "a"), t3.field(s3, "a"));
    assert_eq!(t1.field(s1, "b"), t3.field(s3, "b"));
}

// arch-verifies: ["arch.resolution.requirement-3"]
#[test]
fn absent_members_report_none_not_a_fabricated_id() {
    let (t, names) = members("struct Point { x: i64 }");
    let p = sym(&names, "Point");
    assert!(t.field(p, "nonesuch").is_none());
    assert!(t.variant(p, "Nope").is_none());
}
