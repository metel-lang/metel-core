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
