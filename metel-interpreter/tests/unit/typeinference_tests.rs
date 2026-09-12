//! Test suite for the type inference system.
//! Tests are organized by phase/component matching the task breakdown.

#[cfg(test)]
mod phase_1_type_variables {
    use metel::typeinference::{TypeVar, TypeVarGenerator};

    #[test]
    fn test_type_var_creation() {
        let var1 = TypeVar(0);
        let var2 = TypeVar(1);

        assert_eq!(var1.0, 0);
        assert_eq!(var2.0, 1);
        assert_ne!(var1, var2);
    }

    #[test]
    fn test_type_var_display() {
        let var = TypeVar(42);
        assert_eq!(format!("{}", var), "?t42");
    }

    #[test]
    fn test_type_var_generator_fresh() {
        let mut var_gen = TypeVarGenerator::new();

        let v1 = var_gen.fresh();
        let v2 = var_gen.fresh();
        let v3 = var_gen.fresh();

        assert_eq!(v1.0, 0);
        assert_eq!(v2.0, 1);
        assert_eq!(v3.0, 2);
        assert_ne!(v1, v2);
        assert_ne!(v2, v3);
    }

    #[test]
    fn test_type_var_generator_counter() {
        let mut var_gen = TypeVarGenerator::new();
        assert_eq!(var_gen.counter(), 0);

        var_gen.fresh();
        assert_eq!(var_gen.counter(), 1);

        var_gen.fresh();
        var_gen.fresh();
        assert_eq!(var_gen.counter(), 3);
    }

    #[test]
    fn test_type_var_ordering() {
        let v0 = TypeVar(0);
        let v1 = TypeVar(1);
        let v5 = TypeVar(5);

        assert!(v0 < v1);
        assert!(v1 < v5);
        assert!(v0 < v5);
    }

    #[test]
    fn test_type_var_hashable() {
        use std::collections::HashSet;

        let mut set = HashSet::new();
        set.insert(TypeVar(0));
        set.insert(TypeVar(1));
        set.insert(TypeVar(0)); // Duplicate

        assert_eq!(set.len(), 2);
        assert!(set.contains(&TypeVar(0)));
        assert!(set.contains(&TypeVar(1)));
        assert!(!set.contains(&TypeVar(2)));
    }
}

#[cfg(test)]
mod phase_2_infer_types {
    use metel::typeinference::{InferType, TypeVar};
    use metel::types::Type;

    #[test]
    fn test_concrete_variants() {
        assert_eq!(InferType::int(), InferType::Concrete(Type::I64));
        assert_eq!(InferType::float(), InferType::Concrete(Type::F64));
        assert_eq!(InferType::bool(), InferType::Concrete(Type::Boolean));
        assert_eq!(InferType::str(), InferType::Concrete(Type::Str));
        assert_eq!(InferType::unit(), InferType::Concrete(Type::Unit));
    }

    #[test]
    fn test_var_constructor() {
        let v = TypeVar(3);
        assert_eq!(InferType::var(v), InferType::Var(TypeVar(3)));
    }

    #[test]
    fn test_display_concrete() {
        assert_eq!(format!("{}", InferType::int()), "i64");
        assert_eq!(format!("{}", InferType::float()), "f64");
        assert_eq!(format!("{}", InferType::bool()), "boolean");
        assert_eq!(format!("{}", InferType::str()), "String");
        assert_eq!(format!("{}", InferType::unit()), "()");
    }

    #[test]
    fn test_display_var() {
        assert_eq!(format!("{}", InferType::var(TypeVar(0))), "?t0");
        assert_eq!(format!("{}", InferType::var(TypeVar(7))), "?t7");
    }

    #[test]
    fn test_display_fun() {
        let ty = InferType::fun(
            vec![InferType::int(), InferType::bool()],
            Box::new(InferType::str()),
        );
        assert_eq!(format!("{}", ty), "|i64, boolean| -> String");
    }

    #[test]
    fn test_display_fun_no_params() {
        let ty = InferType::fun(vec![], Box::new(InferType::unit()));
        assert_eq!(format!("{}", ty), "|| -> ()");
    }

    #[test]
    fn test_display_tuple() {
        let ty = InferType::Tuple(vec![InferType::int(), InferType::bool()]);
        assert_eq!(format!("{}", ty), "(i64, boolean)");
    }

    #[test]
    fn test_display_array() {
        let ty = InferType::Array(Box::new(InferType::int()));
        assert_eq!(format!("{}", ty), "i64[]");
    }

    #[test]
    fn test_display_named_no_args() {
        let ty = InferType::Named("Foo".to_string(), vec![], metel::types::NominalId::NONE);
        assert_eq!(format!("{}", ty), "Foo");
    }

    #[test]
    fn test_display_named_with_args() {
        let ty = InferType::Named(
            "Map".to_string(),
            vec![InferType::str(), InferType::int()],
            metel::types::NominalId::NONE,
        );
        assert_eq!(format!("{}", ty), "Map<String, i64>");
    }

    #[test]
    fn test_display_with_type_vars() {
        let ty = InferType::fun(
            vec![InferType::var(TypeVar(0))],
            Box::new(InferType::var(TypeVar(0))),
        );
        assert_eq!(format!("{}", ty), "|?t0| -> ?t0");
    }

    #[test]
    fn test_nested_types() {
        // Array of functions: (i64) -> boolean []
        let ty = InferType::Array(Box::new(InferType::fun(
            vec![InferType::int()],
            Box::new(InferType::bool()),
        )));
        assert_eq!(format!("{}", ty), "|i64| -> boolean[]");
    }

    #[test]
    fn test_equality() {
        let a = InferType::fun(
            vec![InferType::var(TypeVar(0))],
            Box::new(InferType::var(TypeVar(1))),
        );
        let b = InferType::fun(
            vec![InferType::var(TypeVar(0))],
            Box::new(InferType::var(TypeVar(1))),
        );
        let c = InferType::fun(
            vec![InferType::var(TypeVar(0))],
            Box::new(InferType::var(TypeVar(2))),
        );
        assert_eq!(a, b);
        assert_ne!(a, c);
    }
}

#[cfg(test)]
mod phase_3_substitution {
    use metel::typeinference::{InferType, Substitution, TypeVar};

    #[test]
    fn test_bind_and_lookup() {
        let mut s = Substitution::new();
        s.bind(TypeVar(0), InferType::int());
        assert_eq!(s.lookup(TypeVar(0)), Some(&InferType::int()));
        assert_eq!(s.lookup(TypeVar(1)), None);
    }

    #[test]
    fn test_apply_concrete_unchanged() {
        let s = Substitution::new();
        assert_eq!(s.apply(&InferType::int()), InferType::int());
    }

    #[test]
    fn test_apply_resolves_var() {
        let mut s = Substitution::new();
        s.bind(TypeVar(0), InferType::int());
        assert_eq!(s.apply(&InferType::var(TypeVar(0))), InferType::int());
    }

    #[test]
    fn test_apply_unbound_var_unchanged() {
        let s = Substitution::new();
        assert_eq!(
            s.apply(&InferType::var(TypeVar(5))),
            InferType::var(TypeVar(5))
        );
    }

    #[test]
    fn test_apply_chains_transitively() {
        // ?t0 → ?t1, ?t1 → i64  ⟹  apply(?t0) = i64
        let mut s = Substitution::new();
        s.bind(TypeVar(0), InferType::var(TypeVar(1)));
        s.bind(TypeVar(1), InferType::int());
        assert_eq!(s.apply(&InferType::var(TypeVar(0))), InferType::int());
    }

    #[test]
    fn test_apply_nested_fun() {
        // (?t0) -> ?t1  with { ?t0→boolean, ?t1→i64 }  ⟹  (boolean) -> i64
        let mut s = Substitution::new();
        s.bind(TypeVar(0), InferType::bool());
        s.bind(TypeVar(1), InferType::int());
        let ty = InferType::fun(
            vec![InferType::var(TypeVar(0))],
            Box::new(InferType::var(TypeVar(1))),
        );
        let expected = InferType::fun(vec![InferType::bool()], Box::new(InferType::int()));
        assert_eq!(s.apply(&ty), expected);
    }

    #[test]
    fn test_apply_array() {
        let mut s = Substitution::new();
        s.bind(TypeVar(0), InferType::str());
        let ty = InferType::Array(Box::new(InferType::var(TypeVar(0))));
        assert_eq!(s.apply(&ty), InferType::Array(Box::new(InferType::str())));
    }

    #[test]
    fn test_apply_tuple() {
        let mut s = Substitution::new();
        s.bind(TypeVar(0), InferType::int());
        s.bind(TypeVar(1), InferType::bool());
        let ty = InferType::Tuple(vec![InferType::var(TypeVar(0)), InferType::var(TypeVar(1))]);
        assert_eq!(
            s.apply(&ty),
            InferType::Tuple(vec![InferType::int(), InferType::bool()])
        );
    }

    #[test]
    fn test_apply_named() {
        let mut s = Substitution::new();
        s.bind(TypeVar(0), InferType::int());
        let ty = InferType::Named(
            "List".to_string(),
            vec![InferType::var(TypeVar(0))],
            metel::types::NominalId::NONE,
        );
        assert_eq!(
            s.apply(&ty),
            InferType::Named(
                "List".to_string(),
                vec![InferType::int()],
                metel::types::NominalId::NONE
            )
        );
    }

    #[test]
    fn test_compose_applies_other_to_self_values() {
        // s1: { ?t0 → ?t1 },  s2: { ?t1 → i64 }
        // compose(s1, s2) should resolve ?t0 all the way to i64
        let mut s1 = Substitution::new();
        s1.bind(TypeVar(0), InferType::var(TypeVar(1)));
        let mut s2 = Substitution::new();
        s2.bind(TypeVar(1), InferType::int());

        let composed = s1.compose(&s2);
        assert_eq!(
            composed.apply(&InferType::var(TypeVar(0))),
            InferType::int()
        );
        assert_eq!(
            composed.apply(&InferType::var(TypeVar(1))),
            InferType::int()
        );
    }

    #[test]
    fn test_compose_self_wins_on_overlap() {
        // compose(s1, s2) means "apply s1 first, then s2".
        // s1: { ?t0 → i64 },  s2: { ?t0 → boolean }
        // ?t0 → s2(s1(?t0)) = s2(i64) = i64  (s2 only binds vars, not concrete types)
        let mut s1 = Substitution::new();
        s1.bind(TypeVar(0), InferType::int());
        let mut s2 = Substitution::new();
        s2.bind(TypeVar(0), InferType::bool());

        let composed = s1.compose(&s2);
        assert_eq!(
            composed.apply(&InferType::var(TypeVar(0))),
            InferType::int()
        );
    }
}

#[cfg(test)]
mod phase_4_unification {
    use metel::typeinference::{unify, InferType, TypeVar};

    #[test]
    fn test_unify_identical_concrete() {
        let s = unify(&InferType::int(), &InferType::int()).unwrap();
        assert_eq!(s.apply(&InferType::int()), InferType::int());
    }

    #[test]
    fn test_unify_incompatible_concrete() {
        assert!(unify(&InferType::int(), &InferType::bool()).is_err());
        assert!(unify(&InferType::str(), &InferType::float()).is_err());
    }

    #[test]
    fn test_unify_var_with_concrete() {
        let s = unify(&InferType::var(TypeVar(0)), &InferType::int()).unwrap();
        assert_eq!(s.apply(&InferType::var(TypeVar(0))), InferType::int());
    }

    #[test]
    fn test_unify_concrete_with_var() {
        let s = unify(&InferType::bool(), &InferType::var(TypeVar(1))).unwrap();
        assert_eq!(s.apply(&InferType::var(TypeVar(1))), InferType::bool());
    }

    #[test]
    fn test_unify_var_with_var() {
        let s = unify(&InferType::var(TypeVar(0)), &InferType::var(TypeVar(1))).unwrap();
        // One of them should resolve to the other
        let result = s.apply(&InferType::var(TypeVar(0)));
        let other = s.apply(&InferType::var(TypeVar(1)));
        assert_eq!(result, other);
    }

    #[test]
    fn test_unify_var_with_itself() {
        let s = unify(&InferType::var(TypeVar(0)), &InferType::var(TypeVar(0))).unwrap();
        // Empty substitution — no binding needed
        assert_eq!(
            s.apply(&InferType::var(TypeVar(0))),
            InferType::var(TypeVar(0))
        );
    }

    #[test]
    fn test_unify_function_types() {
        // (?t0) -> ?t0  with  (i64) -> i64  => ?t0 = i64
        let a = InferType::fun(
            vec![InferType::var(TypeVar(0))],
            Box::new(InferType::var(TypeVar(0))),
        );
        let b = InferType::fun(vec![InferType::int()], Box::new(InferType::int()));
        let s = unify(&a, &b).unwrap();
        assert_eq!(s.apply(&InferType::var(TypeVar(0))), InferType::int());
    }

    #[test]
    fn test_unify_function_arity_mismatch() {
        let a = InferType::fun(vec![InferType::int()], Box::new(InferType::bool()));
        let b = InferType::fun(
            vec![InferType::int(), InferType::int()],
            Box::new(InferType::bool()),
        );
        assert!(unify(&a, &b).is_err());
    }

    #[test]
    fn test_unify_function_return_type() {
        // (i64) -> ?t0  with  (i64) -> boolean  => ?t0 = boolean
        let a = InferType::fun(vec![InferType::int()], Box::new(InferType::var(TypeVar(0))));
        let b = InferType::fun(vec![InferType::int()], Box::new(InferType::bool()));
        let s = unify(&a, &b).unwrap();
        assert_eq!(s.apply(&InferType::var(TypeVar(0))), InferType::bool());
    }

    #[test]
    fn test_unify_array_types() {
        // ?t0[]  with  i64[]  => ?t0 = i64
        let a = InferType::Array(Box::new(InferType::var(TypeVar(0))));
        let b = InferType::Array(Box::new(InferType::int()));
        let s = unify(&a, &b).unwrap();
        assert_eq!(s.apply(&InferType::var(TypeVar(0))), InferType::int());
    }

    #[test]
    fn test_unify_array_element_mismatch() {
        let a = InferType::Array(Box::new(InferType::int()));
        let b = InferType::Array(Box::new(InferType::bool()));
        assert!(unify(&a, &b).is_err());
    }

    #[test]
    fn test_unify_tuple_types() {
        // (?t0, boolean)  with  (i64, boolean)  => ?t0 = i64
        let a = InferType::Tuple(vec![InferType::var(TypeVar(0)), InferType::bool()]);
        let b = InferType::Tuple(vec![InferType::int(), InferType::bool()]);
        let s = unify(&a, &b).unwrap();
        assert_eq!(s.apply(&InferType::var(TypeVar(0))), InferType::int());
    }

    #[test]
    fn test_unify_tuple_length_mismatch() {
        let a = InferType::Tuple(vec![InferType::int()]);
        let b = InferType::Tuple(vec![InferType::int(), InferType::bool()]);
        assert!(unify(&a, &b).is_err());
    }

    #[test]
    fn test_unify_named_types() {
        // List<?t0>  with  List<i64>  => ?t0 = i64
        let a = InferType::Named(
            "List".to_string(),
            vec![InferType::var(TypeVar(0))],
            metel::types::NominalId::NONE,
        );
        let b = InferType::Named(
            "List".to_string(),
            vec![InferType::int()],
            metel::types::NominalId::NONE,
        );
        let s = unify(&a, &b).unwrap();
        assert_eq!(s.apply(&InferType::var(TypeVar(0))), InferType::int());
    }

    #[test]
    fn test_unify_named_type_name_mismatch() {
        let a = InferType::Named(
            "List".to_string(),
            vec![InferType::int()],
            metel::types::NominalId::NONE,
        );
        let b = InferType::Named(
            "Set".to_string(),
            vec![InferType::int()],
            metel::types::NominalId::NONE,
        );
        assert!(unify(&a, &b).is_err());
    }

    #[test]
    fn test_unify_incompatible_shapes() {
        // Fun vs Array
        let a = InferType::fun(vec![InferType::int()], Box::new(InferType::bool()));
        let b = InferType::Array(Box::new(InferType::int()));
        assert!(unify(&a, &b).is_err());

        // Tuple vs Concrete
        assert!(unify(&InferType::Tuple(vec![InferType::int()]), &InferType::int()).is_err());
    }

    #[test]
    fn test_occurs_check_array() {
        // ?t0 = ?t0[]  — should fail
        let a = InferType::var(TypeVar(0));
        let b = InferType::Array(Box::new(InferType::var(TypeVar(0))));
        assert!(unify(&a, &b).is_err());
    }

    #[test]
    fn test_occurs_check_function() {
        // ?t0 = (?t0) -> i64  — should fail
        let a = InferType::var(TypeVar(0));
        let b = InferType::fun(vec![InferType::var(TypeVar(0))], Box::new(InferType::int()));
        assert!(unify(&a, &b).is_err());
    }

    #[test]
    fn test_unify_multi_var_function() {
        // (?t0, ?t1) -> ?t0  with  (i64, boolean) -> i64  => ?t0=i64, ?t1=boolean
        let a = InferType::fun(
            vec![InferType::var(TypeVar(0)), InferType::var(TypeVar(1))],
            Box::new(InferType::var(TypeVar(0))),
        );
        let b = InferType::fun(
            vec![InferType::int(), InferType::bool()],
            Box::new(InferType::int()),
        );
        let s = unify(&a, &b).unwrap();
        assert_eq!(s.apply(&InferType::var(TypeVar(0))), InferType::int());
        assert_eq!(s.apply(&InferType::var(TypeVar(1))), InferType::bool());
    }
}

#[cfg(test)]
mod phase_5_constraints {
    use metel::ast::Span;
    use metel::typeinference::{solve_constraints, Constraint, InferType, TypeVar};
    use std::collections::HashSet;

    fn span() -> Span {
        Span::new(0, 1, "test")
    }

    fn no_lit_vars() -> HashSet<TypeVar> {
        HashSet::new()
    }

    #[test]
    fn test_single_constraint_var_concrete() {
        // ?t0 = i64  =>  { ?t0 → i64 }
        let cs = vec![Constraint::new(
            InferType::var(TypeVar(0)),
            InferType::int(),
            span(),
        )];
        let s = solve_constraints(cs, &no_lit_vars(), &no_lit_vars()).unwrap();
        assert_eq!(s.apply(&InferType::var(TypeVar(0))), InferType::int());
    }

    #[test]
    fn test_multiple_independent_constraints() {
        // ?t0 = i64, ?t1 = boolean  =>  { ?t0 → i64, ?t1 → boolean }
        let cs = vec![
            Constraint::new(InferType::var(TypeVar(0)), InferType::int(), span()),
            Constraint::new(InferType::var(TypeVar(1)), InferType::bool(), span()),
        ];
        let s = solve_constraints(cs, &no_lit_vars(), &no_lit_vars()).unwrap();
        assert_eq!(s.apply(&InferType::var(TypeVar(0))), InferType::int());
        assert_eq!(s.apply(&InferType::var(TypeVar(1))), InferType::bool());
    }

    #[test]
    fn test_transitive_constraints() {
        // ?t0 = ?t1, ?t1 = i64  =>  ?t0 resolves to i64
        let cs = vec![
            Constraint::new(
                InferType::var(TypeVar(0)),
                InferType::var(TypeVar(1)),
                span(),
            ),
            Constraint::new(InferType::var(TypeVar(1)), InferType::int(), span()),
        ];
        let s = solve_constraints(cs, &no_lit_vars(), &no_lit_vars()).unwrap();
        assert_eq!(s.apply(&InferType::var(TypeVar(0))), InferType::int());
        assert_eq!(s.apply(&InferType::var(TypeVar(1))), InferType::int());
    }

    #[test]
    fn test_conflicting_constraints_error() {
        // ?t0 = i64, ?t0 = boolean  =>  error
        let cs = vec![
            Constraint::new(InferType::var(TypeVar(0)), InferType::int(), span()),
            Constraint::new(InferType::var(TypeVar(0)), InferType::bool(), span()),
        ];
        assert!(solve_constraints(cs, &no_lit_vars(), &no_lit_vars()).is_err());
    }

    #[test]
    fn test_error_carries_span() {
        let bad_span = Span::new(10, 20, "myfile.mtl");
        let cs = vec![Constraint::new(
            InferType::int(),
            InferType::bool(),
            bad_span,
        )];
        let err = solve_constraints(cs, &no_lit_vars(), &no_lit_vars()).unwrap_err();
        let msg = format!("{}", err);
        assert!(msg.contains("myfile.mtl"));
    }

    #[test]
    fn test_empty_constraints() {
        let s = solve_constraints(vec![], &no_lit_vars(), &no_lit_vars()).unwrap();
        // Empty substitution — variables unchanged
        assert_eq!(
            s.apply(&InferType::var(TypeVar(0))),
            InferType::var(TypeVar(0))
        );
    }

    #[test]
    fn test_constraint_with_function_type() {
        // ?t0 = (i64) -> boolean
        let fun_ty = InferType::fun(vec![InferType::int()], Box::new(InferType::bool()));
        let cs = vec![Constraint::new(
            InferType::var(TypeVar(0)),
            fun_ty.clone(),
            span(),
        )];
        let s = solve_constraints(cs, &no_lit_vars(), &no_lit_vars()).unwrap();
        assert_eq!(s.apply(&InferType::var(TypeVar(0))), fun_ty);
    }

    #[test]
    fn test_earlier_bindings_propagate() {
        // ?t0 = i64, (?t0) -> boolean = (?t1) -> boolean  =>  ?t1 = i64
        let cs = vec![
            Constraint::new(InferType::var(TypeVar(0)), InferType::int(), span()),
            Constraint::new(
                InferType::fun(
                    vec![InferType::var(TypeVar(0))],
                    Box::new(InferType::bool()),
                ),
                InferType::fun(
                    vec![InferType::var(TypeVar(1))],
                    Box::new(InferType::bool()),
                ),
                span(),
            ),
        ];
        let s = solve_constraints(cs, &no_lit_vars(), &no_lit_vars()).unwrap();
        assert_eq!(s.apply(&InferType::var(TypeVar(1))), InferType::int());
    }
}

#[cfg(test)]
mod phase_6_type_schemes {
    use metel::typeinference::{
        free_vars, generalize, instantiate, InferType, TypeScheme, TypeVar, TypeVarGenerator,
    };
    use std::collections::HashSet;

    #[test]
    fn test_free_vars_concrete() {
        assert!(free_vars(&InferType::int()).is_empty());
        assert!(free_vars(&InferType::bool()).is_empty());
    }

    #[test]
    fn test_free_vars_var() {
        let vars = free_vars(&InferType::var(TypeVar(0)));
        assert_eq!(vars, [TypeVar(0)].into());
    }

    #[test]
    fn test_free_vars_fun() {
        // (?t0, i64) -> ?t1  =>  { ?t0, ?t1 }
        let ty = InferType::fun(
            vec![InferType::var(TypeVar(0)), InferType::int()],
            Box::new(InferType::var(TypeVar(1))),
        );
        assert_eq!(free_vars(&ty), [TypeVar(0), TypeVar(1)].into());
    }

    #[test]
    fn test_free_vars_nested() {
        // ?t0[]  =>  { ?t0 }
        let ty = InferType::Array(Box::new(InferType::var(TypeVar(0))));
        assert_eq!(free_vars(&ty), [TypeVar(0)].into());
    }

    #[test]
    fn test_generalize_no_env() {
        // generalize((?t0) -> ?t0, {})  =>  ∀?t0. (?t0) -> ?t0
        let ty = InferType::fun(
            vec![InferType::var(TypeVar(0))],
            Box::new(InferType::var(TypeVar(0))),
        );
        let scheme = generalize(ty, &HashSet::new());
        assert_eq!(scheme.quantified_vars, vec![TypeVar(0)]);
    }

    #[test]
    fn test_generalize_env_blocks_capture() {
        // If ?t0 is free in the env, it must not be quantified
        let ty = InferType::fun(
            vec![InferType::var(TypeVar(0))],
            Box::new(InferType::var(TypeVar(0))),
        );
        let env: HashSet<TypeVar> = [TypeVar(0)].into();
        let scheme = generalize(ty.clone(), &env);
        assert!(scheme.quantified_vars.is_empty());
        assert_eq!(scheme.ty, ty);
    }

    #[test]
    fn test_generalize_partial_capture() {
        // (?t0, ?t1) -> ?t0, env has ?t1  =>  only ?t0 is quantified
        let ty = InferType::fun(
            vec![InferType::var(TypeVar(0)), InferType::var(TypeVar(1))],
            Box::new(InferType::var(TypeVar(0))),
        );
        let env: HashSet<TypeVar> = [TypeVar(1)].into();
        let scheme = generalize(ty, &env);
        assert_eq!(scheme.quantified_vars, vec![TypeVar(0)]);
    }

    #[test]
    fn test_generalize_monomorphic_type() {
        // Concrete type has no free vars — scheme is mono
        let scheme = generalize(InferType::int(), &HashSet::new());
        assert!(scheme.quantified_vars.is_empty());
    }

    #[test]
    fn test_instantiate_produces_fresh_vars() {
        // ∀?t0. (?t0) -> ?t0  instantiated with generator at 5
        // => (?t5) -> ?t5
        let scheme = TypeScheme {
            quantified_vars: vec![TypeVar(0)],
            param_names: vec![],
            bounds: vec![],
            neg_bounds: vec![],
            record_kinds: vec![],
            assoc_projections: vec![],
            assoc_eq_constraints: vec![],
            opaque_returns: vec![],
            ty: InferType::fun(
                vec![InferType::var(TypeVar(0))],
                Box::new(InferType::var(TypeVar(0))),
            ),
        };
        let mut var_gen = TypeVarGenerator::new();
        // burn 0-4 so we can assert the exact fresh var
        for _ in 0..5 {
            var_gen.fresh();
        }

        let result = instantiate(&scheme, &mut var_gen);
        let expected = InferType::fun(
            vec![InferType::var(TypeVar(5))],
            Box::new(InferType::var(TypeVar(5))),
        );
        assert_eq!(result, expected);
    }

    #[test]
    fn test_instantiate_twice_gives_different_vars() {
        let mut var_gen = TypeVarGenerator::new();
        // Use the generator to produce the quantified var, matching real usage
        // where schemes are built from vars that were already generated.
        let quantified = var_gen.fresh(); // TypeVar(0)
        let scheme = TypeScheme {
            quantified_vars: vec![quantified],
            param_names: vec![],
            bounds: vec![],
            neg_bounds: vec![],
            record_kinds: vec![],
            assoc_projections: vec![],
            assoc_eq_constraints: vec![],
            opaque_returns: vec![],
            ty: InferType::var(quantified),
        };
        let first = instantiate(&scheme, &mut var_gen);
        let second = instantiate(&scheme, &mut var_gen);
        assert_ne!(first, second);
    }

    #[test]
    fn test_instantiate_mono_unchanged() {
        let scheme = TypeScheme::mono(InferType::int());
        let mut var_gen = TypeVarGenerator::new();
        assert_eq!(instantiate(&scheme, &mut var_gen), InferType::int());
    }

    #[test]
    fn test_display_mono() {
        let scheme = TypeScheme::mono(InferType::int());
        assert_eq!(format!("{}", scheme), "i64");
    }

    #[test]
    fn test_display_poly() {
        let scheme = TypeScheme {
            quantified_vars: vec![TypeVar(0)],
            param_names: vec![],
            bounds: vec![],
            neg_bounds: vec![],
            record_kinds: vec![],
            assoc_projections: vec![],
            assoc_eq_constraints: vec![],
            opaque_returns: vec![],
            ty: InferType::fun(
                vec![InferType::var(TypeVar(0))],
                Box::new(InferType::var(TypeVar(0))),
            ),
        };
        assert_eq!(format!("{}", scheme), "∀?t0. |?t0| -> ?t0");
    }

    #[test]
    fn test_display_multi_var() {
        let scheme = TypeScheme {
            quantified_vars: vec![TypeVar(0), TypeVar(1)],
            param_names: vec![],
            bounds: vec![],
            neg_bounds: vec![],
            record_kinds: vec![],
            assoc_projections: vec![],
            assoc_eq_constraints: vec![],
            opaque_returns: vec![],
            ty: InferType::fun(
                vec![InferType::var(TypeVar(0))],
                Box::new(InferType::var(TypeVar(1))),
            ),
        };
        assert_eq!(format!("{}", scheme), "∀?t0, ?t1. |?t0| -> ?t1");
    }
}

#[cfg(test)]
mod phase_7_infer_context {
    use metel::ast::Span;
    use metel::typeinference::{generalize, InferContext, InferType, TypeScheme, TypeVar};
    use std::collections::HashSet;

    fn span() -> Span {
        Span::new(0, 1, "test")
    }

    #[test]
    fn test_fresh_var_sequential() {
        let mut ctx = InferContext::default();
        let a = ctx.fresh_var();
        let b = ctx.fresh_var();
        let c = ctx.fresh_var();
        assert_eq!(a, InferType::Var(TypeVar(0)));
        assert_eq!(b, InferType::Var(TypeVar(1)));
        assert_eq!(c, InferType::Var(TypeVar(2)));
    }

    #[test]
    fn test_bind_mono_and_lookup() {
        let mut ctx = InferContext::default();
        ctx.bind_mono("x", InferType::int(), false);
        assert_eq!(ctx.lookup("x"), Some(InferType::int()));
    }

    #[test]
    fn test_lookup_unknown_is_none() {
        let mut ctx = InferContext::default();
        assert_eq!(ctx.lookup("unknown"), None);
    }

    #[test]
    fn test_bind_poly_auto_instantiates() {
        let mut ctx = InferContext::default();
        // Manually build ∀?t0. (?t0) -> ?t0
        // Use fresh_var so the generator counter is ahead of the quantified var
        let v = ctx.fresh_var(); // TypeVar(0)
        let scheme = TypeScheme {
            quantified_vars: vec![TypeVar(0)],
            param_names: vec![],
            bounds: vec![],
            neg_bounds: vec![],
            record_kinds: vec![],
            assoc_projections: vec![],
            assoc_eq_constraints: vec![],
            opaque_returns: vec![],
            ty: InferType::fun(vec![v.clone()], Box::new(v)),
        };
        ctx.bind_poly("id", scheme);

        // Each lookup returns a fresh instantiation
        let t1 = ctx.lookup("id").unwrap();
        let t2 = ctx.lookup("id").unwrap();
        assert_ne!(t1, t2);
    }

    #[test]
    fn test_poly_lookup_produces_infer_type() {
        let mut ctx = InferContext::default();
        let v = ctx.fresh_var(); // TypeVar(0)
        let scheme = TypeScheme {
            quantified_vars: vec![TypeVar(0)],
            param_names: vec![],
            bounds: vec![],
            neg_bounds: vec![],
            record_kinds: vec![],
            assoc_projections: vec![],
            assoc_eq_constraints: vec![],
            opaque_returns: vec![],
            ty: v,
        };
        ctx.bind_poly("id", scheme);

        // Should be a Var, not the original ?t0
        let result = ctx.lookup("id").unwrap();
        assert!(matches!(result, InferType::Var(v) if v != TypeVar(0)));
    }

    #[test]
    fn test_poly_takes_precedence_over_mono() {
        let mut ctx = InferContext::default();
        let v = ctx.fresh_var(); // TypeVar(0)
        ctx.bind_mono("f", InferType::int(), false);
        ctx.bind_poly(
            "f",
            TypeScheme {
                quantified_vars: vec![TypeVar(0)],
                param_names: vec![],
                bounds: vec![],
                neg_bounds: vec![],
                record_kinds: vec![],
                assoc_projections: vec![],
                assoc_eq_constraints: vec![],
                opaque_returns: vec![],
                ty: v,
            },
        );
        // Poly env wins — result is a fresh Var, not i64
        let result = ctx.lookup("f").unwrap();
        assert!(matches!(result, InferType::Var(_)));
    }

    #[test]
    fn test_add_constraint_and_solve() {
        let mut ctx = InferContext::default();
        let v = ctx.fresh_var(); // ?t0
        ctx.add_constraint(v, InferType::int(), span());

        let subst = ctx.solve().unwrap();
        assert_eq!(subst.apply(&InferType::Var(TypeVar(0))), InferType::int());
    }

    #[test]
    fn test_solve_conflicting_constraints_errors() {
        let mut ctx = InferContext::default();
        let v = ctx.fresh_var(); // ?t0
        ctx.add_constraint(v.clone(), InferType::int(), span());
        ctx.add_constraint(v, InferType::bool(), span());
        assert!(ctx.solve().is_err());
    }

    #[test]
    fn test_full_inference_scenario() {
        // Simulates: let id = (x) { x }; id(42)
        // Step 1: infer (x) { x } — give x a fresh var ?t0, body is also ?t0
        let mut ctx = InferContext::default();
        let x_ty = ctx.fresh_var(); // ?t0
        ctx.bind_mono("x", x_ty.clone(), false);
        let body_ty = ctx.lookup("x").unwrap(); // ?t0

        // fun type is (?t0) -> ?t0
        let fun_ty = InferType::fun(vec![x_ty.clone()], Box::new(body_ty));

        // Step 2: generalize and store as poly
        let scheme = generalize(fun_ty, &HashSet::new());
        ctx.bind_poly("id", scheme);

        // Step 3: call id(42) — instantiate id, unify with (i64) -> ?ret
        let id_ty = ctx.lookup("id").unwrap(); // (?t1) -> ?t1
        let ret_ty = ctx.fresh_var(); // ?t2
        let call_ty = InferType::fun(vec![InferType::int()], Box::new(ret_ty.clone()));
        ctx.add_constraint(id_ty, call_ty, span());

        let subst = ctx.solve().unwrap();
        // ret_ty should resolve to i64
        assert_eq!(subst.apply(&ret_ty), InferType::int());
    }

    // ── Scoping tests (task 0003) ─────────────────────────────────────────────

    #[test]
    fn test_scope_isolation() {
        let mut ctx = InferContext::default();
        ctx.push_scope();
        ctx.bind_mono("x", InferType::int(), false);
        assert_eq!(ctx.lookup("x"), Some(InferType::int()));
        ctx.pop_scope();
        assert_eq!(ctx.lookup("x"), None);
    }

    #[test]
    fn test_inner_scope_shadows_outer() {
        let mut ctx = InferContext::default();
        ctx.bind_mono("x", InferType::int(), false);
        ctx.push_scope();
        ctx.bind_mono("x", InferType::bool(), false);
        assert_eq!(ctx.lookup("x"), Some(InferType::bool()));
        ctx.pop_scope();
        assert_eq!(ctx.lookup("x"), Some(InferType::int()));
    }

    #[test]
    fn test_outer_scope_visible_in_inner() {
        let mut ctx = InferContext::default();
        ctx.bind_mono("x", InferType::int(), false);
        ctx.push_scope();
        assert_eq!(ctx.lookup("x"), Some(InferType::int()));
        ctx.pop_scope();
    }

    #[test]
    fn test_nested_scopes() {
        let mut ctx = InferContext::default();
        ctx.bind_mono("a", InferType::int(), false);
        ctx.push_scope();
        ctx.bind_mono("b", InferType::bool(), false);
        ctx.push_scope();
        ctx.bind_mono("c", InferType::str(), false);
        assert_eq!(ctx.lookup("a"), Some(InferType::int()));
        assert_eq!(ctx.lookup("b"), Some(InferType::bool()));
        assert_eq!(ctx.lookup("c"), Some(InferType::str()));
        ctx.pop_scope();
        assert_eq!(ctx.lookup("c"), None);
        assert_eq!(ctx.lookup("b"), Some(InferType::bool()));
        ctx.pop_scope();
        assert_eq!(ctx.lookup("b"), None);
        assert_eq!(ctx.lookup("a"), Some(InferType::int()));
    }

    #[test]
    fn test_root_scope_bind_mono_works_without_push() {
        // The root scope is pre-pushed — bind_mono should work immediately.
        let mut ctx = InferContext::default();
        ctx.bind_mono("x", InferType::int(), false);
        assert_eq!(ctx.lookup("x"), Some(InferType::int()));
    }

    #[test]
    fn test_env_free_vars_empty() {
        let ctx = InferContext::default();
        assert!(ctx.env_free_vars().is_empty());
    }

    #[test]
    fn test_env_free_vars_concrete_binding() {
        let mut ctx = InferContext::default();
        ctx.bind_mono("x", InferType::int(), false);
        assert!(ctx.env_free_vars().is_empty());
    }

    #[test]
    fn test_env_free_vars_var_binding() {
        let mut ctx = InferContext::default();
        let v = ctx.fresh_var(); // ?t0
        ctx.bind_mono("x", v, false);
        assert_eq!(ctx.env_free_vars(), [TypeVar(0)].into());
    }

    #[test]
    fn test_env_free_vars_across_scopes() {
        let mut ctx = InferContext::default();
        let v0 = ctx.fresh_var(); // ?t0
        ctx.bind_mono("x", v0, false);
        ctx.push_scope();
        let v1 = ctx.fresh_var(); // ?t1
        ctx.bind_mono("y", v1, false);
        // Both ?t0 and ?t1 should appear
        let fvs = ctx.env_free_vars();
        assert!(fvs.contains(&TypeVar(0)));
        assert!(fvs.contains(&TypeVar(1)));
    }

    #[test]
    fn test_env_free_vars_used_in_generalize() {
        // ?t0 is free in env — generalize should not capture it
        let mut ctx = InferContext::default();
        let _v0 = ctx.fresh_var(); // ?t0 — bound in env
        let _v1 = ctx.fresh_var(); // ?t1 — free in ty only
        ctx.bind_mono("x", InferType::Var(TypeVar(0)), false);

        // (?t0, ?t1) -> ?t1 — only ?t1 should be quantified
        let ty = InferType::fun(
            vec![InferType::Var(TypeVar(0)), InferType::Var(TypeVar(1))],
            Box::new(InferType::Var(TypeVar(1))),
        );
        let env_fvs = ctx.env_free_vars();
        let scheme = generalize(ty, &env_fvs);
        assert_eq!(scheme.quantified_vars, vec![TypeVar(1)]);
        assert!(!scheme.quantified_vars.contains(&TypeVar(0)));
    }
}

#[cfg(test)]
mod phase_8_known_limitations {
    use metel::ast::Span;
    use metel::typeinference::{
        instantiate, solve_constraints, Constraint, InferType, TypeScheme, TypeVar,
        TypeVarGenerator,
    };
    use std::collections::HashSet;

    fn span() -> Span {
        Span::new(0, 1, "test")
    }

    fn no_lit_vars() -> HashSet<TypeVar> {
        HashSet::new()
    }

    /// Rank-1 limitation: a function parameter is a monotype.
    ///
    /// When `f` (a function arg with no annotation) is called at two different
    /// concrete types within the same function body, the constraint solver sees
    /// a conflict. This is the rank-1 restriction: `∀` only at the outermost
    /// level, never in function argument position.
    ///
    /// See: typechecker.md § "Rank-1 Limitation"
    #[test]
    fn test_rank1_fn_arg_monotype_conflicts() {
        // fun apply_both(f, x: i64, y: boolean) { f(x); f(y) }
        //   f(x) emits: ?t0 = (i64) -> ?t1
        //   f(y) emits: ?t0 = (boolean) -> ?t2
        // After binding ?t0 = (i64) -> ?t1, the second constraint becomes
        // (i64) -> ?t1 = (boolean) -> ?t2 → i64 ≠ boolean → error
        let cs = vec![
            Constraint::new(
                InferType::var(TypeVar(0)),
                InferType::fun(vec![InferType::int()], Box::new(InferType::var(TypeVar(1)))),
                span(),
            ),
            Constraint::new(
                InferType::var(TypeVar(0)),
                InferType::fun(
                    vec![InferType::bool()],
                    Box::new(InferType::var(TypeVar(2))),
                ),
                span(),
            ),
        ];
        assert!(solve_constraints(cs, &no_lit_vars(), &no_lit_vars()).is_err());
    }

    /// Let-bound closures are NOT generalized into type schemes.
    ///
    /// `let id = (x) { x }` binds `id` as a monomorphic InferType::fun.
    /// Its type variable is unified at the first call site and cannot change.
    /// A second call at a different type produces the same constraint conflict
    /// as the rank-1 case above — the root cause is identical: no `∀` was
    /// introduced so the type variable is shared across all uses.
    ///
    /// See: typechecker.md § "Extension Points — Epic 003 — let_polymorphism"
    #[test]
    fn test_let_closure_monomorphic_conflicts_at_two_types() {
        // let identity = (x) { x }  →  identity : Fun([?t0], ?t0)
        // identity(42)   emits: Fun([?t0], ?t0) = Fun([i64], ?t1)  → ?t0 = i64
        // identity(true) emits: Fun([?t0], ?t0) = Fun([boolean], ?t2) → i64 ≠ boolean → error
        let cs = vec![
            Constraint::new(
                InferType::fun(
                    vec![InferType::var(TypeVar(0))],
                    Box::new(InferType::var(TypeVar(0))),
                ),
                InferType::fun(vec![InferType::int()], Box::new(InferType::var(TypeVar(1)))),
                span(),
            ),
            Constraint::new(
                InferType::fun(
                    vec![InferType::var(TypeVar(0))],
                    Box::new(InferType::var(TypeVar(0))),
                ),
                InferType::fun(
                    vec![InferType::bool()],
                    Box::new(InferType::var(TypeVar(2))),
                ),
                span(),
            ),
        ];
        assert!(solve_constraints(cs, &no_lit_vars(), &no_lit_vars()).is_err());
    }

    /// Contrast: a properly generalized scheme CAN be used at two types.
    ///
    /// This is what `fun id(x) { x }` (top-level declaration) produces today,
    /// and what `let id = (x) { x }` would produce once let-polymorphism
    /// is fully implemented. The scheme ∀?t0. (?t0) -> ?t0 is instantiated
    /// with fresh variables at each use site so the two calls are independent.
    #[test]
    fn test_poly_scheme_succeeds_at_two_types() {
        // ∀?t0. (?t0) -> ?t0, instantiated twice with fresh variables
        let scheme = TypeScheme {
            quantified_vars: vec![TypeVar(0)],
            param_names: vec![],
            bounds: vec![],
            neg_bounds: vec![],
            record_kinds: vec![],
            assoc_projections: vec![],
            assoc_eq_constraints: vec![],
            opaque_returns: vec![],
            ty: InferType::fun(
                vec![InferType::var(TypeVar(0))],
                Box::new(InferType::var(TypeVar(0))),
            ),
        };
        let mut var_gen = TypeVarGenerator::new();
        var_gen.fresh(); // burn TypeVar(0) — already used in the scheme

        let inst1 = instantiate(&scheme, &mut var_gen); // (?t1) -> ?t1
        let inst2 = instantiate(&scheme, &mut var_gen); // (?t2) -> ?t2
        let ret1 = InferType::Var(var_gen.fresh()); // ?t3
        let ret2 = InferType::Var(var_gen.fresh()); // ?t4

        let cs = vec![
            Constraint::new(
                inst1,
                InferType::fun(vec![InferType::int()], Box::new(ret1)),
                span(),
            ),
            Constraint::new(
                inst2,
                InferType::fun(vec![InferType::bool()], Box::new(ret2)),
                span(),
            ),
        ];
        assert!(
            solve_constraints(cs, &no_lit_vars(), &no_lit_vars()).is_ok(),
            "generalized scheme can be instantiated independently at i64 and boolean"
        );
    }

    /// Eager partial solve limitation: field access requires the receiver type
    /// to be concrete before any later constraints are processed.
    ///
    /// This is demonstrated at the full pipeline level in
    /// limit_03_field_access_needs_annotation.mtl. At the constraint level,
    /// the limitation manifests as: if a type variable stands for the receiver,
    /// `named_type_name` returns None and inference fails immediately (not via
    /// the constraint solver), so there is nothing to assert here about
    /// constraint soundness — the error is structural, not a solver conflict.
    ///
    /// See: typechecker.md § "Pass 1 — Eager Partial Solves"
    #[test]
    fn test_eager_partial_solve_var_has_no_named_type() {
        // Applying ctx.solve() to an unbound type variable leaves it as a Var.
        // named_type_name on a Var returns None — field lookup cannot proceed.
        use metel::typeinference::Substitution;

        let s = Substitution::new();
        let unresolved = s.apply(&InferType::var(TypeVar(0)));
        // An unresolved variable has no concrete struct name — this is what
        // triggers T0002 "cannot infer struct type for field access".
        assert!(matches!(unresolved, InferType::Var(_)));
    }
}
