use super::TypeDefinitionRegistry;
use crate::data::abstract_body::{
    AbstractBound, AbstractParameterFacts, AbstractType, equal_parameter_facts,
};
use crate::data::abstract_body::{ObligationResult, ObligationWitness, WitnessSource};
use crate::data::ast::{Bound, BoundHead, GenericParam, ImplBlock, Polarity, TypeExpr};
use crate::data::types::NominalId;
use crate::identity::symbols::SymbolId;
use std::collections::HashSet;

#[derive(Debug, Clone)]
pub(super) struct OwnershipRule {
    polarity: Polarity,
    conditions: Vec<Vec<(SymbolId, Polarity)>>,
}

impl TypeDefinitionRegistry {
    pub(in crate::pipeline) fn abstract_types_identical(
        &self,
        a: &AbstractType,
        b: &AbstractType,
    ) -> bool {
        same_goal_type(a, b)
    }

    pub(super) fn nominal_ownership_rule(
        &self,
        module: &[String],
        target: SymbolId,
        implementation: &ImplBlock,
    ) -> Option<OwnershipRule> {
        // Unsupported targets must still block the proof. The legacy
        // conditional tables erase patterns and resolved aspect identities.
        if !ordinary_where_clause(implementation) || !implementation.aspect_type_args.is_empty() {
            return None;
        }
        let TypeExpr::Named(_, arguments, _) = &implementation.target_type else {
            return None;
        };
        let count = self
            .struct_type_params
            .get(&target)
            .map(Vec::len)
            .or_else(|| {
                self.enum_env
                    .get(&target)
                    .map(|info| info.type_params.len())
            })?;
        if arguments.len() != count || implementation.generics.len() != count {
            return None;
        }
        let mut used = HashSet::new();
        let mut conditions = Vec::new();
        for argument in arguments {
            let TypeExpr::Named(name, inner, _) = argument else {
                return None;
            };
            if !inner.is_empty() || !used.insert(name) {
                return None;
            }
            let generic = implementation
                .generics
                .iter()
                .find(|generic| &generic.name == name)?;
            if generic.is_record || generic.is_row {
                return None;
            }
            conditions.push(self.ownership_conditions(module, generic, implementation)?);
        }
        Some(OwnershipRule {
            polarity: implementation.polarity,
            conditions,
        })
    }

    fn ownership_conditions(
        &self,
        module: &[String],
        generic: &GenericParam,
        implementation: &ImplBlock,
    ) -> Option<Vec<(SymbolId, Polarity)>> {
        let where_bounds = implementation
            .where_clause
            .iter()
            .flat_map(|clause| &clause.constraints)
            .filter(|constraint| constraint.name == generic.name)
            .flat_map(|constraint| &constraint.bounds);
        generic
            .bounds
            .iter()
            .chain(where_bounds)
            .map(|bound| self.ownership_condition(module, bound))
            .collect()
    }

    fn ownership_condition(
        &self,
        module: &[String],
        bound: &Bound,
    ) -> Option<(SymbolId, Polarity)> {
        let BoundHead::Aspect(TypeExpr::Named(name, arguments, _)) = &bound.head else {
            return None;
        };
        if !arguments.is_empty() || !bound.assoc_bindings.is_empty() {
            return None;
        }
        Some((self.resolve_type_id(module, name)?, bound.polarity))
    }

    pub(in crate::pipeline::type_checking) fn abstract_nominal_aspect(
        &self,
        identity: &NominalId,
        arguments: &[AbstractType],
        aspect: &str,
        facts: &[AbstractParameterFacts],
    ) -> Option<bool> {
        if let Some(result) = self.unconditional_nominal_aspect(identity, aspect) {
            return Some(result);
        }
        let ty = AbstractType::Named {
            name: String::new(),
            identity: identity.clone(),
            arguments: arguments.to_vec(),
        };
        match self.solve_abstract_aspect(&ty, aspect, facts) {
            ObligationResult::Yes(_) => Some(true),
            ObligationResult::No => Some(false),
            ObligationResult::Unknown => None,
        }
    }

    pub(in crate::pipeline) fn solve_abstract_aspect(
        &self,
        ty: &AbstractType,
        aspect: &str,
        facts: &[AbstractParameterFacts],
    ) -> ObligationResult {
        if format!("{ty:?}").len() > 65_536 {
            return ObligationResult::Unknown;
        }
        let Some(identity) = self.resolve_type_id(&["std".into(), "core".into()], aspect) else {
            return ObligationResult::Unknown;
        };
        self.solve_goal(ty, identity, facts, &mut Vec::new())
    }

    fn solve_goal(
        &self,
        ty: &AbstractType,
        aspect: SymbolId,
        facts: &[AbstractParameterFacts],
        active: &mut Vec<(AbstractType, SymbolId)>,
    ) -> ObligationResult {
        // Frozen types already have substitutions applied, but their ordinary
        // equality erases NominalId. Cycle detection must preserve that identity.
        if active.len() >= 64 {
            return ObligationResult::Unknown;
        }
        if active
            .iter()
            .any(|(t, a)| same_goal_type(t, ty) && *a == aspect)
        {
            // Only predicate queries exist today. Derivation coinduction must be
            // a separate mode, never enabled merely because the aspect is Clone.
            return ObligationResult::No;
        }
        active.push((ty.clone(), aspect));
        let result = self.solve_goal_inner(ty, aspect, facts, active);
        active.pop();
        result
    }

    fn solve_goal_inner(
        &self,
        ty: &AbstractType,
        aspect: SymbolId,
        facts: &[AbstractParameterFacts],
        active: &mut Vec<(AbstractType, SymbolId)>,
    ) -> ObligationResult {
        let core = ["std".into(), "core".into()];
        let name = ["Copy", "Clone", "Drop"]
            .into_iter()
            .find(|name| self.resolve_type_id(&core, name) == Some(aspect));
        let yes = |source, children| ObligationResult::Yes(ObligationWitness { source, children });
        match ty {
            AbstractType::Parameter(_) => {
                match parameter_condition(ty, aspect, Polarity::Positive, facts) {
                    Some(true) => yes(WitnessSource::Assumption, vec![]),
                    Some(false) => ObligationResult::No,
                    None => ObligationResult::Unknown,
                }
            }
            AbstractType::Concrete(t) => match name {
                Some(name) if self.type_satisfies_aspect(&core, t, name) => {
                    yes(WitnessSource::Concrete, vec![])
                }
                // Concrete failure is not evidence for an abstract negative bound.
                Some(_) => ObligationResult::No,
                None => ObligationResult::Unknown,
            },
            AbstractType::Reference(_) | AbstractType::Array(_) if name == Some("Copy") => {
                yes(WitnessSource::Compiler, vec![])
            }
            AbstractType::MutReference(_) if name == Some("Copy") => ObligationResult::No,
            AbstractType::Function { usage, .. } if name == Some("Copy") => {
                if *usage == crate::data::types::UseMultiplicity::Copy {
                    yes(WitnessSource::Compiler, vec![])
                } else {
                    ObligationResult::No
                }
            }
            AbstractType::Tuple(items)
            | AbstractType::Closure {
                owned_captures: items,
                ..
            } if name == Some("Copy") => self.solve_children(items.iter(), aspect, facts, active),
            AbstractType::SizedArray(item, _) if name == Some("Copy") => {
                self.solve_children(std::iter::once(item.as_ref()), aspect, facts, active)
            }
            AbstractType::Named {
                identity,
                arguments,
                ..
            } => {
                let Some(target) = identity.get() else {
                    return ObligationResult::Unknown;
                };
                if self.uncertain_ownership_impls.contains(&(None, aspect))
                    || (self.record_structs.contains(&target)
                        && self.uncertain_record_ownership_impls.contains(&aspect))
                {
                    return ObligationResult::Unknown;
                }
                let Some(rules) = self.ownership_rules.get(&(target, aspect)) else {
                    return ObligationResult::Unknown;
                };
                let mut candidates = Vec::new();
                let mut witnesses = Vec::new();
                for (index, rule) in rules.iter().enumerate() {
                    let Some(rule) = rule else {
                        return ObligationResult::Unknown;
                    };
                    if rule.conditions.len() != arguments.len() {
                        return ObligationResult::Unknown;
                    }
                    let mut proofs = Vec::new();
                    let mut children = Vec::new();
                    for (conditions, argument) in rule.conditions.iter().zip(arguments) {
                        for (required, polarity) in conditions {
                            // No-as-failure must never discharge a negative condition.
                            let proof = if *polarity == Polarity::Negative {
                                let proof =
                                    parameter_condition(argument, *required, *polarity, facts);
                                if proof == Some(true) {
                                    children.push(ObligationWitness {
                                        source: WitnessSource::Assumption,
                                        children: vec![],
                                    });
                                }
                                proof
                            } else {
                                match self.solve_goal(argument, *required, facts, active) {
                                    ObligationResult::Yes(w) => {
                                        children.push(w);
                                        Some(true)
                                    }
                                    ObligationResult::No => Some(false),
                                    ObligationResult::Unknown => None,
                                }
                            };
                            proofs.push(proof);
                        }
                    }
                    let applicable = conjunction(proofs.into_iter());
                    candidates.push((rule.polarity, applicable));
                    if rule.polarity == Polarity::Positive && applicable == Some(true) {
                        witnesses.push(ObligationWitness {
                            source: WitnessSource::Impl {
                                target,
                                aspect,
                                index,
                            },
                            children,
                        });
                    }
                }
                match select_ownership(&candidates) {
                    Some(true) if witnesses.len() == 1 => {
                        ObligationResult::Yes(witnesses.remove(0))
                    }
                    Some(false) => ObligationResult::No,
                    _ => ObligationResult::Unknown,
                }
            }
            _ => ObligationResult::Unknown,
        }
    }

    fn solve_children<'a>(
        &self,
        items: impl Iterator<Item = &'a AbstractType>,
        aspect: SymbolId,
        facts: &[AbstractParameterFacts],
        active: &mut Vec<(AbstractType, SymbolId)>,
    ) -> ObligationResult {
        let mut children = Vec::new();
        let mut unknown = false;
        for item in items {
            match self.solve_goal(item, aspect, facts, active) {
                ObligationResult::Yes(w) => children.push(w),
                ObligationResult::No => return ObligationResult::No,
                ObligationResult::Unknown => unknown = true,
            }
        }
        if unknown {
            ObligationResult::Unknown
        } else {
            ObligationResult::Yes(ObligationWitness {
                source: WitnessSource::Compiler,
                children,
            })
        }
    }
}

// Restrict exact-goal detection to the fragment with identity-safe equality.
fn same_goal_type(a: &AbstractType, b: &AbstractType) -> bool {
    match (a, b) {
        (
            AbstractType::Named {
                identity: a,
                arguments: aa,
                ..
            },
            AbstractType::Named {
                identity: b,
                arguments: ba,
                ..
            },
        ) => {
            a.get().is_some()
                && a.get() == b.get()
                && aa.len() == ba.len()
                && aa.iter().zip(ba).all(|(a, b)| same_goal_type(a, b))
        }
        (AbstractType::Parameter(a), AbstractType::Parameter(b)) => a == b,
        (AbstractType::Tuple(a), AbstractType::Tuple(b)) => {
            a.len() == b.len() && a.iter().zip(b).all(|(a, b)| same_goal_type(a, b))
        }
        (AbstractType::Reference(a), AbstractType::Reference(b))
        | (AbstractType::MutReference(a), AbstractType::MutReference(b))
        | (AbstractType::Array(a), AbstractType::Array(b)) => same_goal_type(a, b),
        (AbstractType::SizedArray(a, n), AbstractType::SizedArray(b, m)) => {
            n == m && same_goal_type(a, b)
        }
        (AbstractType::Never, AbstractType::Never) => true,
        // Concrete equality also erases nominal IDs. Debug preserves them;
        // aliases may miss a cycle, which reaches the depth limit conservatively.
        (AbstractType::Concrete(a), AbstractType::Concrete(b)) => {
            format!("{a:?}") == format!("{b:?}")
        }
        _ => false,
    }
}

fn ordinary_where_clause(implementation: &ImplBlock) -> bool {
    implementation.where_clause.as_ref().is_none_or(|clause| {
        clause.row_equations.is_empty()
            && clause.field_wise.is_empty()
            && clause.constraints.iter().all(|constraint| {
                !constraint.is_record
                    && implementation
                        .generics
                        .iter()
                        .any(|generic| generic.name == constraint.name)
            })
    })
}

fn parameter_condition(
    argument: &AbstractType,
    identity: SymbolId,
    polarity: Polarity,
    facts: &[AbstractParameterFacts],
) -> Option<bool> {
    let AbstractType::Parameter(parameter) = argument else {
        return None;
    };
    let equal = equal_parameter_facts(facts, *parameter);
    let granted = equal
        .iter()
        .any(|fact| has_aspect(&fact.positive, identity));
    let forbidden = equal
        .iter()
        .any(|fact| has_aspect(&fact.negative, identity));
    // Contradictory or absent grants cannot justify either result.
    match (granted, forbidden) {
        (true, false) => Some(polarity == Polarity::Positive),
        (false, true) => Some(polarity == Polarity::Negative),
        _ => None,
    }
}

fn has_aspect(bounds: &[AbstractBound], identity: SymbolId) -> bool {
    bounds.iter().any(|bound| {
        matches!(bound, AbstractBound::Aspect(aspect)
        if aspect.identity == identity && aspect.arguments.is_empty())
    })
}

fn conjunction(proofs: impl Iterator<Item = Option<bool>>) -> Option<bool> {
    let mut complete = true;
    for proof in proofs {
        match proof {
            Some(false) => return Some(false),
            Some(true) => {}
            None => complete = false,
        }
    }
    complete.then_some(true)
}

fn select_ownership(applicability: &[(Polarity, Option<bool>)]) -> Option<bool> {
    if applicability.contains(&(Polarity::Negative, Some(true))) {
        return Some(false);
    }
    let positives = applicability
        .iter()
        .filter(|(polarity, _)| *polarity == Polarity::Positive);
    if positives.clone().all(|(_, proof)| *proof == Some(false)) {
        return Some(false);
    }
    if positives.clone().any(|(_, proof)| *proof == Some(true))
        && applicability
            .iter()
            .filter(|(polarity, _)| *polarity == Polarity::Negative)
            .all(|(_, proof)| *proof == Some(false))
    {
        return Some(true);
    }
    None
}

#[cfg(test)]
mod spike_tests {
    use super::*;

    #[test]
    fn nested_witness_and_unsupported_candidate() {
        let mut registry = TypeDefinitionRegistry::new();
        let aspect = SymbolId::declared_for_test(9000);
        let leaf = SymbolId::declared_for_test(9001);
        let outer = SymbolId::declared_for_test(9002);
        registry.ownership_rules.insert(
            (leaf, aspect),
            vec![Some(OwnershipRule {
                polarity: Polarity::Positive,
                conditions: vec![],
            })],
        );
        registry.ownership_rules.insert(
            (outer, aspect),
            vec![Some(OwnershipRule {
                polarity: Polarity::Positive,
                conditions: vec![vec![(aspect, Polarity::Positive)]],
            })],
        );
        let ty = AbstractType::Named {
            name: "Outer".into(),
            identity: NominalId(Some(outer)),
            arguments: vec![AbstractType::Named {
                name: "Leaf".into(),
                identity: NominalId(Some(leaf)),
                arguments: vec![],
            }],
        };
        let ObligationResult::Yes(witness) = registry.solve_goal(&ty, aspect, &[], &mut vec![])
        else {
            panic!("missing nested proof")
        };
        assert!(
            matches!(witness.source, WitnessSource::Impl { target, index: 0, .. } if target == outer)
        );
        assert!(
            matches!(witness.children[0].source, WitnessSource::Impl { target, .. } if target == leaf)
        );
        registry
            .ownership_rules
            .get_mut(&(outer, aspect))
            .unwrap()
            .push(None);
        assert!(matches!(
            registry.solve_goal(&ty, aspect, &[], &mut vec![]),
            ObligationResult::Unknown
        ));
    }

    #[test]
    fn predicate_cycle_and_depth_limit() {
        let registry = TypeDefinitionRegistry::new();
        let aspect = SymbolId::declared_for_test(9000);
        let ty = AbstractType::Never;
        assert!(matches!(
            registry.solve_goal(&ty, aspect, &[], &mut vec![(ty.clone(), aspect)]),
            ObligationResult::No
        ));
        let other = SymbolId::declared_for_test(9001);
        assert!(matches!(
            registry.solve_goal(&ty, aspect, &[], &mut vec![(ty.clone(), other); 64]),
            ObligationResult::Unknown
        ));
    }
    #[test]
    fn exact_goals_preserve_identity_and_ignore_alias_spelling() {
        let a = AbstractType::Named {
            name: "One".into(),
            arguments: vec![],
            identity: NominalId::some(SymbolId::declared_for_test(9100)),
        };
        let b = AbstractType::Named {
            name: "One".into(),
            arguments: vec![],
            identity: NominalId::some(SymbolId::declared_for_test(9101)),
        };
        assert_eq!(a, b); // Existing equality deliberately erases nominal IDs.
        assert!(!same_goal_type(&a, &b));
        let alias = AbstractType::Named {
            name: "Alias".into(),
            arguments: vec![],
            identity: NominalId::some(SymbolId::declared_for_test(9100)),
        };
        assert!(same_goal_type(&a, &alias));
        let started = std::time::Instant::now();
        for _ in 0..100_000 {
            assert!(std::hint::black_box(same_goal_type(
                std::hint::black_box(&a),
                &alias
            )));
        }
        eprintln!(
            "100000 exact nominal goal comparisons: {:?}",
            started.elapsed()
        );
    }
}
