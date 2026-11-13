use super::TypeDefinitionRegistry;
use crate::data::abstract_body::{
    AbstractBound, AbstractParameterFacts, AbstractType, equal_parameter_facts,
};
use crate::data::ast::{Bound, BoundHead, GenericParam, ImplBlock, Polarity, TypeExpr};
use crate::data::types::{NominalId, UseMultiplicity};
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

    /// Why a nominal application is not `Copy` (RFC-0224 section 2, metel-core#1959): the cause the stored
    /// rule or its absence names, or, when it names none, the checker limitation that stops it
    /// (an undecided component, a negative or several rules, a rule that is not a plain flow), so a
    /// message can say so instead of guessing. `None` only for a type with no identity.
    #[must_use]
    pub fn nominal_copy_blame(
        &self,
        identity: &NominalId,
        arguments: &[AbstractType],
        facts: &[AbstractParameterFacts],
    ) -> Option<CopyBlame> {
        if self.unconditional_nominal_aspect(identity, self.implicit_aspect_name()) == Some(false) {
            return Some(CopyBlame::NoDeclaration);
        }
        let (Some(target), Some(copy)) = (identity.get(), self.copy_aspect_id()) else {
            return None;
        };
        let [Some(rule)] = self.ownership_rules.get(&(target, copy))?.as_slice() else {
            return Some(CopyBlame::Limitation(
                "its `Copy` is given by several or unstored rules",
            ));
        };
        if rule.polarity != Polarity::Positive || rule.conditions.len() != arguments.len() {
            return Some(CopyBlame::Limitation(
                "its stored `Copy` rule is not a plain flow set",
            ));
        }
        let mut blamed = None;
        for (position, (conditions, argument)) in rule.conditions.iter().zip(arguments).enumerate()
        {
            let in_flow = conditions
                .iter()
                .any(|(aspect, polarity)| *aspect == copy && *polarity == Polarity::Positive);
            if !in_flow {
                continue;
            }
            match flow_condition(self, argument, copy, facts) {
                Some(true) => {}
                Some(false) => {
                    blamed.get_or_insert(position);
                }
                None => {
                    return Some(CopyBlame::Limitation(
                        "an argument of its flow is undecided (a `dyn` value, an open row or a residual)",
                    ));
                }
            }
        }
        Some(blamed.map_or(
            CopyBlame::Limitation("no argument of its flow is found to fail"),
            CopyBlame::Argument,
        ))
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
        // RFC-0224 prototype: consuming a stored `Copy` rule is class arithmetic over the flow set.
        let flow = self.copy_aspect_id() == Some(aspect_id);
        let applicability = supported
            .iter()
            .map(|rule| {
                (
                    rule.polarity,
                    rule.applicability(self, arguments, facts, flow),
                )
            })
            .collect::<Vec<_>>();
        select_ownership(&applicability)
    }
}

/// The cause of a nominal application not being `Copy` that its stored data names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CopyBlame {
    /// The type does not derive or implement `Copy` at all.
    NoDeclaration,
    /// The type is `Copy` only when its arguments in the flow are, and the argument at this position is not.
    Argument(usize),
    /// The checker cannot decide, or does not model the rule: the message says that, not why.
    Limitation(&'static str),
}

impl OwnershipRule {
    fn applicability(
        &self,
        registry: &TypeDefinitionRegistry,
        arguments: &[AbstractType],
        facts: &[AbstractParameterFacts],
        flow: bool,
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
                        if flow && *polarity == Polarity::Positive {
                            flow_condition(registry, argument, *identity, facts)
                        } else {
                            parameter_condition(argument, *identity, *polarity, facts)
                        }
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

/// RFC-0224 section 2. One atom `Param: Copy` of a stored flow set, evaluated for the argument at that
/// position, by the `Copy` rule of the argument's own type form (RFC-0206 section 2):
/// - a type parameter is `Copy` when a bound says so and otherwise is not known `Copy` (the value moves; this
///   is not evidence of `!Copy`);
/// - a nested application reduces through its own stored rule, a concrete type is asked directly;
/// - a tuple and a record are `Copy` when every component is; a sized array when its element is;
/// - a shared reference and the borrowed `T[]` view are always `Copy`, `&var T` never;
/// - a function type is `Copy` when it says so.
///
/// `None` is *undecided*: an open row, a residual, a `dyn` value, or a component that is. A component that is
/// definitely not `Copy` decides the whole conjunction.
fn flow_condition(
    registry: &TypeDefinitionRegistry,
    argument: &AbstractType,
    identity: SymbolId,
    facts: &[AbstractParameterFacts],
) -> Option<bool> {
    let all = |items: &mut dyn Iterator<Item = &AbstractType>| {
        conjunction(items.map(|item| flow_condition(registry, item, identity, facts)))
    };
    match argument {
        AbstractType::Parameter(parameter) => {
            let equal = equal_parameter_facts(facts, *parameter);
            let forbidden = equal
                .iter()
                .any(|fact| has_aspect(&fact.negative, identity));
            let granted = equal
                .iter()
                .any(|fact| has_aspect(&fact.positive, identity));
            Some(granted && !forbidden)
        }
        AbstractType::Named {
            identity: nominal,
            arguments,
            ..
        } => registry.abstract_nominal_aspect(
            nominal,
            arguments,
            registry.implicit_aspect_name(),
            facts,
        ),
        AbstractType::Concrete(ty) => Some(registry.type_is_copy(&[], ty)),
        AbstractType::Tuple(items) => all(&mut items.iter()),
        AbstractType::Record(fields) => all(&mut fields.iter().map(|(_, ty)| ty)),
        AbstractType::SizedArray(item, _) => flow_condition(registry, item, identity, facts),
        AbstractType::Reference(_) | AbstractType::Array(_) => Some(true),
        AbstractType::MutReference(_) => Some(false),
        AbstractType::Function { usage, .. } => Some(*usage == UseMultiplicity::Copy),
        _ => None,
    }
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
