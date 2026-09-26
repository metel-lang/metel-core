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
