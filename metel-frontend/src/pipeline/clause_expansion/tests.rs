//! The flow computation reaches declarations inside function bodies (metel-core#1964): the clause expansion
//! writes `extend<T> W<T>: Copy` for a local `struct W<T> derives Copy { v: View<T> }`, with no bound on `T`
//! because a view holds it by reference, and shadows a module-level type of the same name.

use std::sync::atomic::{AtomicU64, Ordering};

use crate::data::ast::{Decl, ImplBlock};
use crate::pipeline::clause_expansion::resolve_and_expand;
use crate::pipeline::parsing::module_loader;

/// The impls the clause expansion wrote in the body of `main`, as `(aspect, bounded parameter names)`.
fn local_impls(source: &str) -> Vec<(String, Vec<String>)> {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let path =
        std::env::temp_dir().join(format!("metel_clause_flow_{}_{n}.mtl", std::process::id()));
    std::fs::write(&path, source).expect("write temp fixture");
    let mut graph = module_loader::load_root(&path).expect("load");
    resolve_and_expand(&mut graph).expect("expand");
    let _ = std::fs::remove_file(&path);
    let main = graph
        .modules
        .iter()
        .flat_map(|m| m.program.decls.iter())
        .find_map(|d| match d {
            Decl::Fun(f) if f.name == "main" => Some(f),
            _ => None,
        })
        .expect("fn main");
    main.body
        .stmts
        .iter()
        .filter_map(|d| match d {
            Decl::Impl(ImplBlock {
                aspect_name: Some(aspect),
                generics,
                from_clause: true,
                ..
            }) => Some((
                aspect.clone(),
                generics
                    .iter()
                    .filter(|g| !g.bounds.is_empty())
                    .map(|g| g.name.clone())
                    .collect(),
            )),
            _ => None,
        })
        .collect()
}

#[test]
fn a_local_copy_declaration_gets_its_computed_flow() {
    let impls = local_impls(
        "copy struct View<T> { r: &T }
         fun main() {
             struct W<T> derives Copy { v: View<T> }
             struct Plain<T> derives Copy { v: T }
             struct Outer<A, B> derives Copy { w: Plain<A>, n: B }
         }",
    );
    // W<T> holds T only through a view: no bound. Plain<T> holds it: bounded. Outer reads the flow of the
    // local `Plain` declared in the same block.
    assert!(impls.contains(&("Copy".to_string(), vec![])), "{impls:?}");
    assert!(
        impls.contains(&("Copy".to_string(), vec!["T".to_string()])),
        "{impls:?}"
    );
    assert!(
        impls.contains(&("Copy".to_string(), vec!["A".to_string(), "B".to_string()])),
        "{impls:?}"
    );
}

#[test]
fn a_local_declaration_shadows_a_module_level_type_of_the_same_name() {
    // The module-level `Hold<T>` holds `T`; the local one holds it only through a view. `W` names `Hold` and
    // must read the local flow, so it bounds nothing.
    let impls = local_impls(
        "copy struct View<T> { r: &T }
         struct Hold<T> derives Copy { v: T }
         fun main() {
             struct Hold<T> derives Copy { v: View<T> }
             struct W<T> derives Copy { h: Hold<T> }
         }",
    );
    let unbounded = impls
        .iter()
        .filter(|(aspect, bounded)| aspect == "Copy" && bounded.is_empty())
        .count();
    assert_eq!(unbounded, 2, "{impls:?}");
}
