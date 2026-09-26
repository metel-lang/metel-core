use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use crate::identity::FieldId;

use super::{Place, Projection};

fn hash(p: &Projection) -> u64 {
    let mut h = DefaultHasher::new();
    p.hash(&mut h);
    h.finish()
}

#[test]
fn field_identity_ignores_the_interned_id() {
    // The same field reached via an expression (id known) and via an
    // assignment target / RFC-0137 narrowing (no id) must be the same place,
    // or the partial-move overlap algebra and loop fixpoint fragment.
    let with_id = Projection::field_with_id("f", Some(FieldId(7)));
    let other_id = Projection::field_with_id("f", Some(FieldId(99)));
    let no_id = Projection::field("f");
    assert_eq!(with_id, other_id);
    assert_eq!(with_id, no_id);
    assert_eq!(hash(&with_id), hash(&no_id));
    assert_eq!(with_id.cmp(&no_id), std::cmp::Ordering::Equal);
    assert_ne!(with_id, Projection::field("g"));
}

#[test]
fn prefix_matches_exact_place() {
    let place = Place::new("x".to_string()).with_projection(Projection::field("a"));
    assert!(place.is_prefix_of(&place));
}

#[test]
fn prefix_matches_descendant_place() {
    let left = Place::new("x".to_string()).with_projection(Projection::field("a"));
    let right = left.clone().with_projection(Projection::field("b"));
    assert!(left.is_prefix_of(&right));
}

#[test]
fn prefix_rejects_sibling_place() {
    let left = Place::new("x".to_string()).with_projection(Projection::field("a"));
    let right = Place::new("x".to_string()).with_projection(Projection::field("b"));
    assert!(!left.is_prefix_of(&right));
}

#[test]
fn opaque_index_is_a_real_projection() {
    let left = Place::new("xs".to_string()).with_projection(Projection::OpaqueIndex);
    let right = left.clone().with_projection(Projection::field("len"));
    assert!(left.is_prefix_of(&right));
}

#[test]
fn deref_is_a_real_projection() {
    let left = Place::new("p".to_string()).with_projection(Projection::Deref);
    let right = left.clone().with_projection(Projection::field("name"));
    assert!(left.is_prefix_of(&right));
    assert_eq!(left.projections(), &[Projection::Deref]);
}

#[test]
fn deref_is_distinct_from_the_reference_itself() {
    let reference = Place::new("p".to_string());
    let pointee = reference.clone().with_projection(Projection::Deref);
    assert_ne!(reference, pointee);
    assert!(reference.is_prefix_of(&pointee));
    assert!(!pointee.is_prefix_of(&reference));
}
