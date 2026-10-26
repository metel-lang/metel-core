use super::*;

#[test]
fn core_module_is_embedded() {
    let core = vec!["std".to_string(), "core".to_string()];
    let src = lookup(&core).expect("std::core must be embedded");
    assert!(src.contains("native(@std.core.print)"), "core.mtl content");
    assert!(module_paths().contains(&core));
}

#[test]
fn unknown_path_is_none() {
    assert!(lookup(&["std".to_string(), "nope".to_string()]).is_none());
    assert!(lookup(&["user".to_string()]).is_none());
}

// metel-core#1559: a std module's position in the embedded table numbers the SymbolIds of its
// declarations, so it must exist for every embedded module, be distinct, and follow the sorted
// order `build.rs` embeds in.
#[test]
fn every_embedded_module_has_a_distinct_index_in_sorted_order() {
    let paths = module_paths();
    let indices: Vec<u16> = paths
        .iter()
        .map(|p| module_index(p).expect("an embedded module has an index"))
        .collect();
    assert_eq!(indices, (0..paths.len() as u16).collect::<Vec<_>>());
    let mut sorted = paths.clone();
    sorted.sort();
    assert_eq!(paths, sorted, "build.rs must embed modules in path order");
    assert_eq!(
        module_index(&["std".to_string(), "no_such_module".to_string()]),
        None
    );
    assert_eq!(module_index(&["app".to_string()]), None);
}

// metel-core#1582: the reserved names are derived (builtin types that core.mtl does not declare), so
// they are exactly the fifteen intrinsic types: not the core types it declares, aspects, or user names.
#[test]
fn the_intrinsic_type_names_are_the_builtin_types_core_does_not_declare() {
    for name in [
        "boolean",
        "String",
        "Char",
        "i8",
        "i16",
        "i32",
        "i64",
        "u8",
        "u16",
        "u32",
        "u64",
        "f32",
        "f64",
        "Range",
        "RangeInclusive",
    ] {
        assert!(is_intrinsic_type_name(name), "{name}");
    }
    for name in [
        "List", "Option", "Result", "Display", "Iterable", "From", "Copy", "Point", "string", "I64",
    ] {
        assert!(!is_intrinsic_type_name(name), "{name}");
    }
}
