use super::*;
use crate::pipeline::type_checking::typeinference::OverloadEntry;

fn entry(params: Vec<Type>, ret: Type) -> OverloadEntry {
    OverloadEntry {
        params,
        ret,
        symbol_id: next_overload_symbol(),
    }
}

#[test]
fn overload_symbol_ids_are_unique_and_in_range() {
    let a = next_overload_symbol();
    let b = next_overload_symbol();
    assert_ne!(a, b);
    assert!(a.0 >= crate::identity::symbols::OVERLOAD_SYM_START);
    assert!(b.0 >= crate::identity::symbols::OVERLOAD_SYM_START);
}

#[test]
fn select_requires_exact_match() {
    let entries = vec![
        entry(vec![Type::I32], Type::Unit),
        entry(vec![Type::I64], Type::Unit),
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
        entry(vec![Type::I64], Type::I64),
        entry(vec![Type::I64, Type::I64], Type::I64),
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
