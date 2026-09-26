use super::*;
use crate::identity::symbols::SYM_ASPECT_DISPLAY;

fn display_owner() -> AspectDispatchOwner {
    AspectDispatchOwner {
        aspect_id: SYM_ASPECT_DISPLAY,
        aspect_name: "Display".to_string(),
        is_generic: false,
    }
}

const FOO_ID: SymbolId = SymbolId(9001);
const BAR_ID: SymbolId = SymbolId(9002);

// arch-verifies: ["arch.elaboration.requirement-1"]
#[test]
fn resolve_dispatch_aspect_returns_aspect_variant() {
    let mut map = HashMap::new();
    map.insert((Some(FOO_ID), "to_string".to_string()), display_owner());
    assert_eq!(
        resolve_dispatch(Some("Foo"), Some(FOO_ID), "to_string", &map),
        MethodDispatch::Aspect {
            aspect_id: SYM_ASPECT_DISPLAY
        }
    );
}

// arch-verifies: ["arch.elaboration.requirement-1"]
#[test]
fn resolve_dispatch_wrong_type_returns_inherent() {
    let mut map = HashMap::new();
    map.insert((Some(FOO_ID), "to_string".to_string()), display_owner());
    // Same method name but different receiver type → Inherent, not an aspect call.
    assert_eq!(
        resolve_dispatch(Some("Bar"), Some(BAR_ID), "to_string", &map),
        MethodDispatch::Inherent
    );
}

/// metel-core#1136: two unrelated modules' same-named types (same bare
/// `"Foo"` spelling, distinct `SymbolId`s) must not collide.
// arch-verifies: ["arch.elaboration.requirement-1"]
#[test]
fn resolve_dispatch_same_bare_name_different_identity_returns_inherent() {
    let mut map = HashMap::new();
    map.insert((Some(FOO_ID), "to_string".to_string()), display_owner());
    assert_eq!(
        resolve_dispatch(Some("Foo"), Some(BAR_ID), "to_string", &map),
        MethodDispatch::Inherent,
        "a different module's same-named type must not match another's registration"
    );
}

// arch-verifies: ["arch.elaboration.requirement-1"]
#[test]
fn resolve_dispatch_no_type_returns_inherent() {
    let mut map = HashMap::new();
    map.insert((Some(FOO_ID), "to_string".to_string()), display_owner());
    assert_eq!(
        resolve_dispatch(None, None, "to_string", &map),
        MethodDispatch::Inherent
    );
}

#[test]
fn resolve_dispatch_unknown_method_returns_inherent() {
    let map = HashMap::new();
    assert_eq!(
        resolve_dispatch(Some("Foo"), Some(FOO_ID), "len", &map),
        MethodDispatch::Inherent
    );
}

// arch-verifies: ["arch.elaboration.requirement-1"]
#[test]
fn resolve_dispatch_non_aspect_method_returns_inherent() {
    let mut map = HashMap::new();
    map.insert((Some(FOO_ID), "to_string".to_string()), display_owner());
    assert_eq!(
        resolve_dispatch(Some("Foo"), Some(FOO_ID), "push", &map),
        MethodDispatch::Inherent
    );
}

/// metel-core#1136: a primitive receiver (no `SymbolId` at all) still
/// dispatches correctly by bare name -- primitives aren't user-declarable,
/// so there's no collision risk to guard against for them.
#[test]
fn resolve_dispatch_primitive_receiver_has_no_identity() {
    let mut map = HashMap::new();
    map.insert((None, "to_string".to_string()), display_owner());
    assert_eq!(
        resolve_dispatch(Some("i64"), None, "to_string", &map),
        MethodDispatch::Aspect {
            aspect_id: SYM_ASPECT_DISPLAY
        }
    );
}
