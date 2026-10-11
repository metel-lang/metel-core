use super::TypeDefinitionRegistry;
use crate::data::abstract_body::{
    AbstractBound, AbstractParameterFacts, AbstractType, equal_parameter_facts,
};
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
        let TypeExpr::Named(_, arguments) = &implementation.target_type else {
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
            let TypeExpr::Named(name, inner) = argument else {
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
        let BoundHead::Aspect(TypeExpr::Named(name, arguments)) = &bound.head else {
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
        let target = identity.get()?;
        let aspect_id = self.resolve_type_id(&["std".to_string(), "core".to_string()], aspect)?;
        if self.uncertain_ownership_impls.contains(&(None, aspect_id))
            || (self.record_structs.contains(&target)
                && self.uncertain_record_ownership_impls.contains(&aspect_id))
        {
            return None;
        }
        let rules = self.ownership_rules.get(&(target, aspect_id))?;
        // All candidates must be represented: an unsupported negative override
        // cannot be bypassed by proving a positive candidate.
        let supported = rules
            .iter()
            .map(Option::as_ref)
            .collect::<Option<Vec<_>>>()?;
        let applicability = supported
            .iter()
            .map(|rule| (rule.polarity, rule.applicability(arguments, facts)))
            .collect::<Vec<_>>();
        select_ownership(&applicability)
    }
}

impl OwnershipRule {
    fn applicability(
        &self,
        arguments: &[AbstractType],
        facts: &[AbstractParameterFacts],
    ) -> Option<bool> {
        if self.conditions.len() != arguments.len() {
            return None;
        }
        conjunction(
            self.conditions
                .iter()
                .zip(arguments)
                .flat_map(|(conditions, argument)| {
                    conditions.iter().map(move |(identity, polarity)| {
                        parameter_condition(argument, *identity, *polarity, facts)
                    })
                }),
        )
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
