use super::*;

#[test]
fn the_declared_ranges_are_ordered_and_disjoint() {
    assert!(ranges_are_ordered_and_disjoint(&ALL));
    for pair in ALL.windows(2) {
        assert!(
            pair[0].end <= pair[1].start,
            "{} overlaps {}",
            pair[0].name,
            pair[1].name
        );
    }
}

#[test]
fn an_overlap_an_empty_range_and_a_wrong_order_are_rejected() {
    let a = TypeVarRange {
        name: "a",
        start: 0,
        end: 10,
    };
    let overlapping = TypeVarRange {
        name: "b",
        start: 5,
        end: 20,
    };
    let empty = TypeVarRange {
        name: "c",
        start: 30,
        end: 30,
    };
    let earlier = TypeVarRange {
        name: "d",
        start: 0,
        end: 4,
    };
    assert!(ranges_are_ordered_and_disjoint(&[a]));
    assert!(!ranges_are_ordered_and_disjoint(&[a, overlapping]));
    assert!(!ranges_are_ordered_and_disjoint(&[empty]));
    assert!(!ranges_are_ordered_and_disjoint(&[a, earlier]));
}

#[test]
fn each_generator_stays_inside_its_range() {
    for range in ALL {
        let mut generator = TypeVarGenerator::in_range(range);
        let first = generator.fresh();
        let second = generator.fresh();
        assert_eq!(first.0, range.start);
        assert!(
            range.contains(first.0) && range.contains(second.0),
            "{}",
            range.name
        );
        assert_ne!(first, second);
    }
}

#[test]
fn new_is_the_local_range() {
    assert_eq!(TypeVarGenerator::new().range(), LOCAL);
    assert_eq!(TypeVarGenerator::new().counter(), 0);
}

#[test]
#[should_panic(expected = "TypeVar range `construction`")]
fn a_generator_panics_instead_of_entering_the_next_range() {
    let mut generator = TypeVarGenerator {
        counter: CONSTRUCTION.end - 1,
        range: CONSTRUCTION,
    };
    let last = generator.fresh();
    assert!(CONSTRUCTION.contains(last.0));
    let _ = generator.fresh();
}

#[test]
fn reserving_past_a_variable_of_another_range_changes_nothing() {
    let mut generator = TypeVarGenerator::new();
    generator.reserve_past(TypeVar(EXPORT.start + 5));
    generator.reserve_past(TypeVar(PRELUDE.start + 5));
    assert_eq!(generator.counter(), 0);
}

#[test]
fn reserving_past_a_variable_of_its_own_range_moves_the_counter() {
    let mut generator = TypeVarGenerator::new();
    generator.reserve_past(TypeVar(41));
    assert_eq!(generator.fresh(), TypeVar(42));
    generator.reserve_past(TypeVar(3));
    assert_eq!(generator.fresh(), TypeVar(43));
}

#[test]
fn continuing_keeps_the_range_and_the_position() {
    let mut generator = TypeVarGenerator::in_range(EXPORT);
    generator.fresh();
    let mut next = generator.continuing();
    assert_eq!(next.range(), EXPORT);
    assert_eq!(next.fresh().0, EXPORT.start + 1);
}
