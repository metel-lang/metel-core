use super::super::ResolvedInferenceFacts;
use super::{AbstractSignature, AbstractType, SignatureFreezer, ordered_variables};
use crate::data::abstract_body::{
    AbstractArgument, AbstractBinding, AbstractBlock, AbstractBody, AbstractBodyPreparation,
    AbstractBound, AbstractCall, AbstractCapture, AbstractCaptureMode, AbstractClosure,
    AbstractExpr, AbstractExprKind, AbstractFieldSelection, AbstractMethodCall,
    AbstractPassingMode, AbstractReceiverMode, AbstractRecordPattern, AbstractStatement,
};
use crate::data::ast::{AssignOp, AssignTarget, Decl, Expr, FunDecl, Pattern, Span, Stmt, UnaryOp};
use crate::identity::FrozenIdentity;
use crate::ownership::place::Projection;
use crate::pipeline::type_checking::type_engine::{TypeDefinitionRegistry, TypeScheme};
use std::cell::RefCell;
use std::collections::HashMap;

struct FrozenAssignmentPlace {
    binding: crate::identity::BindingId,
    projections: Vec<Projection>,
    selection: Option<AbstractFieldSelection>,
    inputs: Vec<AbstractExpr>,
}

struct BodyFreezer<'a, 'return_type> {
    types: SignatureFreezer<'a>,
    facts: &'a ResolvedInferenceFacts,
    signature: &'a AbstractSignature,
    identity: FrozenIdentity<'a>,
    return_type: &'return_type AbstractType,
    binding_names: &'a RefCell<HashMap<crate::identity::BindingId, String>>,
    closure_types: &'a RefCell<HashMap<crate::identity::BindingId, AbstractType>>,
    loop_results: RefCell<Vec<AbstractType>>,
    registry: &'a TypeDefinitionRegistry,
    nominal_ownership: &'a RefCell<Vec<crate::data::abstract_body::AbstractNominalOwnership>>,
}

pub(in crate::pipeline::type_checking) fn prepare_abstract_body(
    signature: &AbstractSignature,
    scheme: &TypeScheme,
    declaration: &FunDecl,
    facts: &ResolvedInferenceFacts,
    identity: Option<FrozenIdentity<'_>>,
    registry: &TypeDefinitionRegistry,
) -> AbstractBodyPreparation {
    if signature.facts.is_none() {
        return AbstractBodyPreparation::Pending {
            reason: "definition fact environment is not fully retained".to_string(),
        };
    }
    match freeze_body(signature, scheme, declaration, facts, identity, registry) {
        Ok(body) => AbstractBodyPreparation::Typed(body),
        Err(reason) => AbstractBodyPreparation::Pending { reason },
    }
}

fn freeze_body(
    signature: &AbstractSignature,
    scheme: &TypeScheme,
    declaration: &FunDecl,
    facts: &ResolvedInferenceFacts,
    identity: Option<FrozenIdentity<'_>>,
    registry: &TypeDefinitionRegistry,
) -> Result<AbstractBody, String> {
    let identity = identity.ok_or("definition has no frozen binding identities")?;
    let source_order: Vec<_> = declaration
        .generics
        .iter()
        .map(|generic| generic.name.as_str())
        .collect();
    let variables = ordered_variables(scheme, &source_order)
        .into_iter()
        .zip(signature.parameters.iter().map(|parameter| parameter.id))
        .collect();
    let AbstractType::Function {
        parameters, result, ..
    } = &signature.ty
    else {
        return Err("definition has no abstract function signature".to_string());
    };
    let binding_names = RefCell::new(HashMap::new());
    let closure_types = RefCell::new(HashMap::new());
    let nominal_ownership = RefCell::new(Vec::new());
    let freezer = BodyFreezer {
        types: SignatureFreezer {
            variables,
            names: signature
                .parameters
                .iter()
                .filter_map(|parameter| parameter.name.as_deref().map(|name| (name, parameter.id)))
                .collect(),
            span: &declaration.span,
        },
        facts,
        signature,
        identity,
        return_type: result,
        binding_names: &binding_names,
        closure_types: &closure_types,
        loop_results: RefCell::new(Vec::new()),
        registry,
        nominal_ownership: &nominal_ownership,
    };
    if parameters.len() != declaration.params.len() {
        return Err("definition parameter count disagrees with its abstract signature".to_string());
    }
    let parameters = declaration
        .params
        .iter()
        .zip(parameters)
        .map(|(parameter, ty)| freezer.binding(&parameter.name, &parameter.span, ty.clone()))
        .collect::<Result<_, _>>()?;
    let block = freezer.block(&declaration.body)?;
    BodyFreezer::check_branch_type(&block, result)?;
    Ok(AbstractBody {
        binder: signature.binder,
        parameters,
        binding_names: binding_names.into_inner(),
        nominal_ownership: nominal_ownership.into_inner(),
        block,
    })
}

impl BodyFreezer<'_, '_> {
    fn retain_nominal_ownership(&self, ty: &AbstractType) {
        match ty {
            AbstractType::Named {
                identity,
                arguments,
                ..
            } => {
                let mut retained = self.nominal_ownership.borrow_mut();
                if !retained.iter().any(|fact| &fact.ty == ty) {
                    retained.push(crate::data::abstract_body::AbstractNominalOwnership {
                        ty: ty.clone(),
                        copy: self.registry.abstract_nominal_aspect(
                            identity,
                            arguments,
                            "Copy",
                            self.signature.facts.as_deref().unwrap_or_default(),
                        ),
                        drop: self.registry.abstract_nominal_aspect(
                            identity,
                            arguments,
                            "Drop",
                            self.signature.facts.as_deref().unwrap_or_default(),
                        ),
                    });
                }
                drop(retained);
                for argument in arguments {
                    self.retain_nominal_ownership(argument);
                }
            }
            AbstractType::Tuple(items) => {
                for item in items {
                    self.retain_nominal_ownership(item);
                }
            }
            AbstractType::Record(fields) | AbstractType::Residual { fields, .. } => {
                for (_, ty) in fields {
                    self.retain_nominal_ownership(ty);
                }
            }
            AbstractType::OpenRecord { fields, tail } => {
                for (_, ty) in fields {
                    self.retain_nominal_ownership(ty);
                }
                self.retain_nominal_ownership(tail);
            }
            AbstractType::Array(inner)
            | AbstractType::SizedArray(inner, _)
            | AbstractType::Reference(inner)
            | AbstractType::MutReference(inner) => {
                self.retain_nominal_ownership(inner);
            }
            _ => {}
        }
    }

    fn loop_block(
        &self,
        block: &crate::data::ast::Block,
        result: AbstractType,
    ) -> Result<AbstractBlock, String> {
        self.loop_results.borrow_mut().push(result);
        let body = self.block(block);
        self.loop_results.borrow_mut().pop();
        body
    }

    fn binding(
        &self,
        name: &str,
        span: &Span,
        ty: AbstractType,
    ) -> Result<AbstractBinding, String> {
        self.retain_nominal_ownership(&ty);
        let identity = self
            .identity
            .binding_spans
            .get(span)
            .ok_or_else(|| format!("definition binding `{name}` has no frozen identity"))?;
        self.binding_names
            .borrow_mut()
            .entry(identity)
            .or_insert_with(|| name.to_string());
        if matches!(ty, AbstractType::Closure { .. }) {
            self.closure_types.borrow_mut().insert(identity, ty.clone());
        }
        Ok(AbstractBinding {
            identity,
            name: name.to_string(),
            ty,
        })
    }

    fn block(&self, block: &crate::data::ast::Block) -> Result<AbstractBlock, String> {
        let statements = block
            .stmts
            .iter()
            .map(|statement| self.statement(statement))
            .collect::<Result<_, _>>()?;
        let tail = block
            .tail
            .as_deref()
            .map(|expression| self.expression(expression).map(Box::new))
            .transpose()?;
        Ok(AbstractBlock {
            statements,
            tail,
            span: block.span.clone(),
        })
    }

    fn statement(&self, statement: &Decl) -> Result<AbstractStatement, String> {
        if let Decl::LetPattern(declaration) = statement {
            let value = self.expression(&declaration.value)?;
            return Ok(AbstractStatement::DestructureRecord {
                pattern: self.record_pattern(&declaration.pattern, &value.ty)?,
                mutable: declaration.mutable,
                value,
            });
        }
        let (name, span, mutable, annotation, expression) = match statement {
            Decl::Let(binding) => (
                &binding.name,
                &binding.span,
                false,
                &binding.type_ann,
                &binding.value,
            ),
            Decl::Mut(binding) => (
                &binding.name,
                &binding.span,
                true,
                &binding.type_ann,
                &binding.value,
            ),
            Decl::Stmt(statement) => match statement.as_ref() {
                Stmt::Expr(expression) => {
                    return self.expression(expression).map(AbstractStatement::Expr);
                }
                Stmt::While(loop_stmt) => {
                    return Ok(AbstractStatement::While {
                        condition: self.expression(&loop_stmt.condition)?,
                        body: self.loop_block(
                            &loop_stmt.body,
                            AbstractType::Concrete(crate::data::types::Type::Unit),
                        )?,
                        span: loop_stmt.span.clone(),
                    });
                }
                Stmt::ForIn(loop_stmt) => return self.for_in(loop_stmt),
                Stmt::For(loop_stmt) => return self.for_loop(loop_stmt),
            },
            _ => {
                return Err(
                    "nested declarations and patterns are not yet retained in abstract bodies"
                        .to_string(),
                );
            }
        };
        let value = self.expression(expression)?;
        let binding_type = if annotation.is_some() {
            let inferred = self
                .facts
                .definition_binding_type(span)
                .ok_or("annotated binding has no solved declared type fact")?;
            let declared = self
                .types
                .freeze(inferred)
                .map_err(|error| error.to_string())?;
            // A solved equality needs no new ownership operation. A coercion
            // may change consumption (for example read-copy through a borrow).
            if declared != value.ty {
                return Err(
                    "binding coercion facts are not yet retained in abstract bodies".to_string(),
                );
            }
            declared
        } else {
            value.ty.clone()
        };
        let binding = self.binding(name, span, binding_type)?;
        Ok(AbstractStatement::Bind {
            binding,
            mutable,
            value,
        })
    }

    fn for_loop(&self, loop_stmt: &crate::data::ast::ForStmt) -> Result<AbstractStatement, String> {
        use crate::data::ast::ForInit;
        let init = loop_stmt
            .init
            .as_ref()
            .map(|init| {
                let declaration = match init {
                    ForInit::Let(binding) => Decl::Let(binding.clone()),
                    ForInit::Mut(binding) => Decl::Mut(binding.clone()),
                    ForInit::Expr(expression) => {
                        Decl::Stmt(Box::new(Stmt::Expr(expression.clone())))
                    }
                };
                self.statement(&declaration).map(Box::new)
            })
            .transpose()?;
        Ok(AbstractStatement::For {
            init,
            condition: loop_stmt
                .condition
                .as_ref()
                .map(|expr| self.expression(expr).map(Box::new))
                .transpose()?,
            step: loop_stmt
                .step
                .as_ref()
                .map(|expr| self.expression(expr).map(Box::new))
                .transpose()?,
            body: self.loop_block(
                &loop_stmt.body,
                AbstractType::Concrete(crate::data::types::Type::Unit),
            )?,
            span: loop_stmt.span.clone(),
        })
    }

    fn for_in(&self, loop_stmt: &crate::data::ast::ForInStmt) -> Result<AbstractStatement, String> {
        let iterable = self.expression(&loop_stmt.iterable)?;
        let (iterable_type, _) = peel_references(&iterable.ty);
        let (element, mode) = match iterable_type {
            AbstractType::Array(element) => (
                element.as_ref(),
                crate::data::abstract_body::AbstractIterationMode::BorrowedArrayElement,
            ),
            AbstractType::SizedArray(element, _) => (
                element.as_ref(),
                crate::data::abstract_body::AbstractIterationMode::OwnedArrayElement,
            ),
            _ => return Err("abstract iteration dispatch facts are not yet retained".to_string()),
        };
        let recorded = self
            .facts
            .definition_binding_type(&loop_stmt.span)
            .ok_or("iteration binding has no retained element type")?;
        let recorded = self
            .types
            .freeze(recorded)
            .map_err(|error| error.to_string())?;
        if &recorded != element {
            return Err("iteration binding disagrees with its retained element type".to_string());
        }
        let binding = self.binding(&loop_stmt.binding, &loop_stmt.span, recorded)?;
        Ok(AbstractStatement::ForIn {
            binding,
            iterable,
            mode,
            body: self.loop_block(
                &loop_stmt.body,
                AbstractType::Concrete(crate::data::types::Type::Unit),
            )?,
            span: loop_stmt.span.clone(),
        })
    }

    fn record_pattern(
        &self,
        pattern: &Pattern,
        ty: &AbstractType,
    ) -> Result<AbstractRecordPattern, String> {
        let Pattern::Record {
            fields,
            field_spans,
            ignored_fields,
            rest_binding,
            span,
            rest: _,
        } = pattern
        else {
            return Err("non-record pattern operations are not yet retained".to_string());
        };
        let required: Vec<_> = fields
            .iter()
            .chain(ignored_fields)
            .map(String::as_str)
            .collect();
        let retained_shape = if let Some(shape) = self.facts.definition_record_shape(span) {
            self.types
                .freeze(shape)
                .map_err(|error| error.to_string())?
        } else {
            self.record_pattern_shape_in(ty, &required, &mut std::collections::HashSet::new())?
        };
        let (source_fields, tail) = match &retained_shape {
            AbstractType::Record(fields) => (fields, None),
            AbstractType::OpenRecord { fields, tail } => (fields, Some(tail)),
            _ => return Err("record pattern requires a retained structural row shape".to_string()),
        };
        if fields.len() != field_spans.len() {
            return Err("record pattern binding provenance is incomplete".to_string());
        }
        let field_type = |name: &str| {
            source_fields
                .iter()
                .find(|(label, _)| label == name)
                .map(|(_, ty)| ty.clone())
                .ok_or_else(|| "record pattern field type is not retained".to_string())
        };
        let bindings = fields
            .iter()
            .zip(field_spans)
            .map(|(name, span)| self.binding(name, span, field_type(name)?))
            .collect::<Result<_, _>>()?;
        let discarded = ignored_fields
            .iter()
            .map(|name| Ok((name.clone(), field_type(name)?)))
            .collect::<Result<_, String>>()?;
        let remainder = rest_binding
            .as_ref()
            .map(|(name, span)| {
                let fields: Vec<_> = source_fields
                    .iter()
                    .filter(|(label, _)| !fields.contains(label) && !ignored_fields.contains(label))
                    .cloned()
                    .collect();
                let ty = if let Some(tail) = tail
                    && fields.is_empty()
                {
                    tail.as_ref().clone()
                } else if let Some(tail) = tail {
                    AbstractType::OpenRecord {
                        fields,
                        tail: tail.clone(),
                    }
                } else {
                    AbstractType::Record(fields)
                };
                self.binding(name, span, ty)
            })
            .transpose()?;
        Ok(AbstractRecordPattern {
            bindings,
            discarded,
            remainder,
        })
    }

    fn record_pattern_shape_in(
        &self,
        ty: &AbstractType,
        required: &[&str],
        active: &mut std::collections::HashSet<crate::data::abstract_body::AbstractParameterId>,
    ) -> Result<AbstractType, String> {
        if let AbstractType::OpenRecord { fields, tail } = ty {
            let missing: Vec<_> = required
                .iter()
                .copied()
                .filter(|label| !fields.iter().any(|(name, _)| name == label))
                .collect();
            if missing.is_empty() {
                return Ok(ty.clone());
            }
            if let Ok(AbstractType::OpenRecord {
                fields: additional,
                tail,
            }) = self.record_pattern_shape_in(tail, &missing, active)
            {
                let mut combined = fields.clone();
                combined.extend(additional);
                combined.sort_by(|(a, _), (b, _)| a.cmp(b));
                return Ok(AbstractType::OpenRecord {
                    fields: combined,
                    tail,
                });
            }
            return Err("record pattern field type is not retained".to_string());
        }
        let AbstractType::Parameter(parameter) = ty else {
            return Ok(ty.clone());
        };
        if !active.insert(*parameter) {
            return Err("cyclic abstract row decomposition".to_string());
        }
        let facts = self
            .signature
            .facts
            .as_ref()
            .ok_or("row facts are not retained")?;
        let sources = crate::data::abstract_body::equal_parameter_facts(facts, *parameter);
        if !sources
            .iter()
            .any(|fact| fact.row_kind || fact.open_row_parameter)
        {
            return Err("record pattern requires a retained structural row shape".to_string());
        }
        for bound in sources.iter().flat_map(|source| &source.positive) {
            let AbstractBound::Row { fields, open } = bound else {
                continue;
            };
            let Some(fields) = fields
                .iter()
                .map(|(name, ty)| ty.as_ref().map(|ty| (name.clone(), ty.clone())))
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            if !open
                && required
                    .iter()
                    .all(|label| fields.iter().any(|(name, _)| name == label))
            {
                active.remove(parameter);
                return Ok(AbstractType::Record(fields));
            }
            let mut labels: Vec<_> = fields.iter().map(|(name, _)| name.clone()).collect();
            labels.sort();
            labels.dedup();
            let remainder = facts.iter().find(|facts| {
                facts.row_kind
                    && facts.remainders.iter().any(|equation| {
                        let mut removed = equation.removed.clone();
                        removed.sort();
                        removed.dedup();
                        sources
                            .iter()
                            .any(|source| source.parameter == equation.source)
                            && removed == labels
                    })
            });
            if let Some(remainder) = remainder {
                let shape = AbstractType::OpenRecord {
                    fields,
                    tail: Box::new(AbstractType::Parameter(remainder.parameter)),
                };
                if let Ok(shape) =
                    self.record_pattern_shape_in(&shape, required, &mut active.clone())
                {
                    active.remove(parameter);
                    return Ok(shape);
                }
            }
        }
        active.remove(parameter);
        Err("record pattern requires a retained structural row shape".to_string())
    }

    fn expression_type(&self, expression: &Expr) -> Result<AbstractType, String> {
        if let Expr::Ident(_, span) = expression
            && let Some(binding) = self.identity.binding_spans.get(span)
            && let Some(ty) = self.closure_types.borrow().get(&binding)
        {
            return Ok(ty.clone());
        }
        let inferred = self
            .facts
            .definition_expression_types()
            .get(expression.span())
            .ok_or("definition expression has no solved type fact")?;
        if matches!(expression, Expr::Loop { .. })
            && self.facts.definition_loop_diverges(expression.span())
        {
            Ok(AbstractType::Never)
        } else {
            let ty = self
                .types
                .freeze(inferred)
                .map_err(|error| error.to_string())?;
            self.retain_nominal_ownership(&ty);
            Ok(ty)
        }
    }

    fn expression(&self, expression: &Expr) -> Result<AbstractExpr, String> {
        let ty = self.expression_type(expression)?;
        let kind = match expression {
            Expr::Ident(name, span) => self.identifier(name, span)?,
            Expr::Literal(literal, _) => AbstractExprKind::Literal(literal.clone()),
            Expr::Path(_, _, span) => self.selected_path(span)?,
            Expr::ResolvedPath {
                symbol_id: Some(id),
                ..
            } => AbstractExprKind::Binding(crate::identity::BindingId::Global(*id)),
            Expr::Cast { expr, .. } => self.numeric_cast(expr, &ty)?,
            Expr::Ascribe { expr, .. } => {
                let value = self.expression(expr)?;
                if value.ty != ty {
                    return Err("ascription coercion facts are not yet retained".to_string());
                }
                return Ok(value);
            }
            Expr::Tuple(items, _) => AbstractExprKind::Tuple(self.items(items)?),
            Expr::Array(items, _) => AbstractExprKind::Array(self.items(items)?),
            Expr::RecordLiteral { fields, spread, .. } => {
                self.record_literal(fields, spread.as_ref())?
            }
            Expr::StructLiteral { fields, .. } => self.struct_literal(fields)?,
            Expr::RecordProjection {
                path_span, fields, ..
            } => self.record_projection(path_span, fields)?,
            Expr::Assign {
                target, op, value, ..
            } => self.assignment(target, op, value)?,
            Expr::Closure {
                captures,
                call_multiplicity,
                call_mutation,
                params,
                body,
                span,
                ..
            } => self.closure(
                captures,
                (*call_multiplicity, *call_mutation),
                params,
                body,
                &ty,
                span,
            )?,
            Expr::RepeatArray(value, length, _) => AbstractExprKind::RepeatArray {
                value: Box::new(self.expression(value)?),
                length: *length,
            },
            Expr::UnaryOp(UnaryOp::Ref | UnaryOp::RefMut, value, _) => {
                let value = self.expression(value)?;
                if matches!(value.ty, AbstractType::Closure { .. }) {
                    return Err(
                        "borrowed closure ownership contracts are not yet retained".to_string()
                    );
                }
                AbstractExprKind::Borrow {
                    temporary: value.place().is_none(),
                    value: Box::new(value),
                    mutable: matches!(expression, Expr::UnaryOp(UnaryOp::RefMut, ..)),
                }
            }
            Expr::UnaryOp(UnaryOp::Deref, value, _) => {
                AbstractExprKind::Dereference(Box::new(self.expression(value)?))
            }
            Expr::TupleAccess { object, index, .. } => self.tuple_field(object, *index, &ty)?,
            Expr::Index { object, index, .. } => self.index(object, index, &ty)?,
            Expr::Call {
                callee, args, span, ..
            } => AbstractExprKind::Call(self.call(callee, args, span, &ty)?),
            Expr::FieldAccess {
                object,
                field,
                span,
            } => self.field(object, field, span, &ty)?,
            Expr::MethodCall {
                receiver,
                method,
                args,
                span,
                ..
            } => {
                if self.facts.definition_array_length(span) {
                    AbstractExprKind::ArrayLength(Box::new(self.expression(receiver)?))
                } else {
                    AbstractExprKind::MethodCall(
                        self.method_call(receiver, method, args, span, &ty)?,
                    )
                }
            }
            Expr::Match(matched) => self.match_expression(matched, &ty)?,
            Expr::Return(_)
            | Expr::If { .. }
            | Expr::Loop { .. }
            | Expr::Break(_)
            | Expr::Continue(_) => self.control_flow(expression, &ty)?,
            _ => self.operator(expression, &ty)?,
        };
        Self::finish_expression(ty, kind, expression.span())
    }

    fn identifier(&self, name: &str, span: &Span) -> Result<AbstractExprKind, String> {
        if self.facts.definition_path(span).is_some() {
            return self.selected_path(span);
        }
        let binding = self
            .identity
            .binding_spans
            .get(span)
            .ok_or("definition reference has no frozen binding identity")?;
        self.binding_names
            .borrow_mut()
            .entry(binding)
            .or_insert_with(|| name.to_string());
        Ok(AbstractExprKind::Binding(binding))
    }

    fn selected_path(&self, span: &Span) -> Result<AbstractExprKind, String> {
        use super::super::super::type_engine::DefinitionPathFact;
        match self.facts.definition_path(span) {
            Some(DefinitionPathFact::StaticMember { owner, member }) => {
                Ok(AbstractExprKind::StaticMember {
                    owner: *owner,
                    member: member.clone(),
                })
            }
            Some(DefinitionPathFact::UnitVariant(id)) => Ok(AbstractExprKind::UnitVariant(*id)),
            None => Err("value path selection contract is not retained".to_string()),
        }
    }

    fn match_expression(
        &self,
        matched: &crate::data::ast::MatchExpr,
        result: &AbstractType,
    ) -> Result<AbstractExprKind, String> {
        use super::super::super::type_engine::DefinitionMatchPatternKind;
        use crate::data::abstract_body::AbstractMatchPattern;
        let scrutinee = self.expression(&matched.scrutinee)?;
        let mut covers_true = false;
        let mut covers_false = false;
        let mut catch_all = false;
        let mut variants = std::collections::HashSet::new();
        let mut required_variants = Vec::new();
        let mut arms = Vec::new();
        for arm in &matched.arms {
            if arm.guard.is_some() {
                return Err("match guard flow facts are not yet retained".to_string());
            }
            let fact = self
                .facts
                .definition_match_pattern(&arm.span)
                .ok_or("match selection/binding facts are not yet retained")?;
            let binding = |name: &str, span: &Span, ty| {
                self.binding(
                    name,
                    span,
                    self.types.freeze(ty).map_err(|error| error.to_string())?,
                )
            };
            let pattern = match &fact.kind {
                DefinitionMatchPatternKind::Wildcard => {
                    catch_all = true;
                    AbstractMatchPattern::Wildcard
                }
                DefinitionMatchPatternKind::Literal(literal) => {
                    if let crate::data::ast::Literal::Boolean(value) = literal {
                        covers_true |= *value;
                        covers_false |= !value;
                    }
                    AbstractMatchPattern::Literal(literal.clone())
                }
                DefinitionMatchPatternKind::Binding => {
                    catch_all = true;
                    let (_, name, span, ty) = fact
                        .bindings
                        .first()
                        .ok_or("match binding fact is absent")?;
                    AbstractMatchPattern::Binding(binding(name, span, ty)?)
                }
                DefinitionMatchPatternKind::Variant(identity) => {
                    variants.insert(*identity);
                    required_variants.clone_from(&fact.enum_variants);
                    AbstractMatchPattern::Variant {
                        identity: *identity,
                        bindings: fact
                            .bindings
                            .iter()
                            .map(|(id, name, span, ty)| {
                                Ok((
                                    id.ok_or("match field identity is absent")?,
                                    binding(name, span, ty)?,
                                ))
                            })
                            .collect::<Result<_, String>>()?,
                    }
                }
            };
            let body = self.block(&arm.body)?;
            Self::check_branch_type(&body, result)?;
            arms.push((pattern, body));
        }
        let exhaustive = catch_all
            || (scrutinee.ty == AbstractType::Concrete(crate::data::types::Type::Boolean)
                && covers_true
                && covers_false)
            || (!required_variants.is_empty()
                && required_variants.iter().all(|id| variants.contains(id)));
        if !exhaustive {
            return Err("match exhaustiveness facts are not yet sufficient".to_string());
        }
        Ok(AbstractExprKind::Match {
            scrutinee: Box::new(scrutinee),
            arms,
        })
    }

    fn finish_expression(
        mut ty: AbstractType,
        kind: AbstractExprKind,
        span: &Span,
    ) -> Result<AbstractExpr, String> {
        if let AbstractExprKind::Closure(closure) = &kind {
            ty = AbstractType::Closure {
                signature: Box::new(ty),
                owned_captures: closure
                    .captures
                    .iter()
                    .filter(|capture| {
                        matches!(
                            capture.mode,
                            AbstractCaptureMode::Owned
                                | AbstractCaptureMode::Clone
                                | AbstractCaptureMode::ImplicitCopy,
                        )
                    })
                    .map(|capture| capture.ty.clone())
                    .collect(),
            };
        }
        let aggregates = match &kind {
            AbstractExprKind::Tuple(items) | AbstractExprKind::Array(items) => items
                .iter()
                .any(|value| matches!(value.ty, AbstractType::Closure { .. })),
            AbstractExprKind::StructLiteral { fields }
            | AbstractExprKind::RecordLiteral { fields, .. } => fields
                .iter()
                .any(|(_, value)| matches!(value.ty, AbstractType::Closure { .. })),
            AbstractExprKind::RepeatArray { value, .. } => {
                matches!(value.ty, AbstractType::Closure { .. })
            }
            _ => false,
        };
        if aggregates {
            return Err("aggregate closure ownership contracts are not yet retained".to_string());
        }
        Ok(AbstractExpr {
            ty,
            kind,
            span: span.clone(),
        })
    }

    fn items(&self, items: &[Expr]) -> Result<Vec<AbstractExpr>, String> {
        items.iter().map(|item| self.expression(item)).collect()
    }

    fn numeric_cast(
        &self,
        expression: &Expr,
        result: &AbstractType,
    ) -> Result<AbstractExprKind, String> {
        let operand = self.expression(expression)?;
        let (AbstractType::Concrete(source), AbstractType::Concrete(target)) =
            (&operand.ty, result)
        else {
            return Err("cast dispatch and ownership contracts are not yet retained".to_string());
        };
        if !source.is_numeric() || !target.is_numeric() {
            return Err("cast dispatch and ownership contracts are not yet retained".to_string());
        }
        Ok(AbstractExprKind::NumericCast(Box::new(operand)))
    }

    fn operator(
        &self,
        expression: &Expr,
        result: &AbstractType,
    ) -> Result<AbstractExprKind, String> {
        match expression {
            Expr::BinOp(left, operator, right, _) => {
                self.binary_operator(left, operator, right, result)
            }
            Expr::UnaryOp(operator @ (UnaryOp::Neg | UnaryOp::Not), operand, _) => {
                let operand = self.expression(operand)?;
                let legal = match (&operand.ty, operator) {
                    (AbstractType::Concrete(ty), UnaryOp::Neg) => ty.is_numeric(),
                    (AbstractType::Concrete(crate::data::types::Type::Boolean), UnaryOp::Not) => {
                        true
                    }
                    _ => false,
                };
                if !legal || &operand.ty != result {
                    return Err("unary operator legality facts are not yet retained".to_string());
                }
                Ok(AbstractExprKind::Unary {
                    operator: operator.clone(),
                    operand: Box::new(operand),
                })
            }
            _ => Err(
                "expression selection/control-flow facts are not yet retained in abstract bodies"
                    .to_string(),
            ),
        }
    }

    fn binary_operator(
        &self,
        left: &Expr,
        operator: &crate::data::ast::BinOp,
        right: &Expr,
        result: &AbstractType,
    ) -> Result<AbstractExprKind, String> {
        use crate::data::ast::BinOp;
        use crate::data::types::Type;
        let left = self.expression(left)?;
        let right = self.expression(right)?;
        let (AbstractType::Concrete(left_type), AbstractType::Concrete(right_type)) =
            (&left.ty, &right.ty)
        else {
            return Err("abstract operator selection facts are not yet retained".to_string());
        };
        // Only built-in selections established by the solved operand types are
        // retained here. A parameter must not acquire an operator from a sample.
        let legal = left_type == right_type
            && match operator {
                BinOp::Add => left_type.is_numeric() || *left_type == Type::Str,
                BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => left_type.is_numeric(),
                BinOp::Eq | BinOp::Ne => {
                    left_type.is_numeric()
                        || matches!(left_type, Type::Str | Type::Char | Type::Boolean)
                }
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    left_type.is_numeric() || matches!(left_type, Type::Str | Type::Char)
                }
                BinOp::And | BinOp::Or => *left_type == Type::Boolean,
                BinOp::Range | BinOp::RangeInclusive => *left_type == Type::I64,
            };
        let result_agrees = match operator {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => result == &left.ty,
            BinOp::Range | BinOp::RangeInclusive => {
                matches!(result, AbstractType::Named { name, arguments, .. } if name == "Range" && arguments == &[AbstractType::Concrete(Type::I64)])
            }
            _ => *result == AbstractType::Concrete(Type::Boolean),
        };
        if !legal || !result_agrees {
            return Err("binary operator legality facts are not yet retained".to_string());
        }
        Ok(AbstractExprKind::Binary {
            operator: operator.clone(),
            left: Box::new(left),
            right: Box::new(right),
        })
    }

    fn record_literal(
        &self,
        fields: &[(String, Expr)],
        spread: Option<&(Box<Expr>, usize, Span)>,
    ) -> Result<AbstractExprKind, String> {
        Ok(AbstractExprKind::RecordLiteral {
            fields: self.named_items(fields)?,
            spread: spread
                .map(|(value, position, _)| {
                    self.expression(value)
                        .map(|value| (Box::new(value), *position))
                })
                .transpose()?,
        })
    }

    fn struct_literal(&self, fields: &[(String, Expr)]) -> Result<AbstractExprKind, String> {
        Ok(AbstractExprKind::StructLiteral {
            fields: self.named_items(fields)?,
        })
    }

    fn named_items(&self, items: &[(String, Expr)]) -> Result<Vec<(String, AbstractExpr)>, String> {
        items
            .iter()
            .map(|(name, value)| Ok((name.clone(), self.expression(value)?)))
            .collect()
    }

    fn record_projection(
        &self,
        path_span: &Span,
        fields: &[String],
    ) -> Result<AbstractExprKind, String> {
        let inferred = self
            .facts
            .definition_expression_types()
            .get(path_span)
            .ok_or("record projection source has no solved type fact")?;
        let source = AbstractExpr {
            ty: self
                .types
                .freeze(inferred)
                .map_err(|error| error.to_string())?,
            kind: AbstractExprKind::Binding(
                self.identity
                    .binding_spans
                    .get(path_span)
                    .ok_or("record projection source has no frozen binding identity")?,
            ),
            span: path_span.clone(),
        };
        Ok(AbstractExprKind::RecordProjection {
            source: Box::new(source),
            fields: fields.to_vec(),
        })
    }

    fn assignment(
        &self,
        target: &AssignTarget,
        operator: &AssignOp,
        value: &Expr,
    ) -> Result<AbstractExprKind, String> {
        let target_span = assignment_target_span(target);
        let target_type = self
            .facts
            .definition_expression_types()
            .get(target_span)
            .ok_or("assignment target has no solved type fact")?;
        let target_type = self
            .types
            .freeze(target_type)
            .map_err(|error| error.to_string())?;
        if !matches!(operator, AssignOp::Assign)
            && !matches!(&target_type, AbstractType::Concrete(ty) if ty.is_numeric())
        {
            return Err("compound assignment operator contract is not yet retained".to_string());
        }
        let FrozenAssignmentPlace {
            binding: target,
            projections,
            selection,
            inputs,
        } = self.assignment_place(target, target_span, &target_type)?;
        if self.closure_types.borrow().contains_key(&target) {
            return Err(
                "closure reassignment ownership contracts are not yet retained".to_string(),
            );
        }
        let value = self.expression(value)?;
        if value.ty != target_type && value.ty != AbstractType::Never {
            return Err("assignment storage contract is not yet retained".to_string());
        }
        Ok(AbstractExprKind::Assign {
            operator: operator.clone(),
            target,
            projections,
            target_type,
            selection,
            inputs,
            value: Box::new(value),
        })
    }

    fn assignment_place(
        &self,
        target: &AssignTarget,
        target_span: &Span,
        target_type: &AbstractType,
    ) -> Result<FrozenAssignmentPlace, String> {
        match target {
            AssignTarget::Ident(_, span) => Ok(FrozenAssignmentPlace {
                binding: self
                    .identity
                    .binding_spans
                    .get(span)
                    .ok_or("assignment target has no frozen binding identity")?,
                projections: Vec::new(),
                selection: None,
                inputs: Vec::new(),
            }),
            AssignTarget::FieldAccess { object, field, .. } => {
                let object = self.expression(object)?;
                let mut place = object
                    .place()
                    .ok_or("field assignment base is not a retained place")?;
                let (base, dereferences) = peel_references(&object.ty);
                place
                    .projections
                    .extend(std::iter::repeat_n(Projection::Deref, dereferences));
                let selection =
                    self.assignment_field_selection(base, field, target_span, target_type)?;
                let field_id = match &selection {
                    AbstractFieldSelection::Nominal { field, .. } => Some(*field),
                    AbstractFieldSelection::Structural { .. }
                    | AbstractFieldSelection::Granted { .. } => None,
                };
                place
                    .projections
                    .push(Projection::field_with_id(field.clone(), field_id));
                let inputs = Self::assignment_inputs(&object)?;
                Ok(FrozenAssignmentPlace {
                    binding: place.binding,
                    projections: place.projections,
                    selection: Some(selection),
                    inputs,
                })
            }
            AssignTarget::TupleAccess { object, index, .. } => {
                let object = self.expression(object)?;
                let mut place = object
                    .place()
                    .ok_or("tuple assignment base is not a retained place")?;
                let (_, dereferences) = peel_references(&object.ty);
                place
                    .projections
                    .extend(std::iter::repeat_n(Projection::Deref, dereferences));
                place.projections.push(Projection::TupleIndex(*index));
                let inputs = Self::assignment_inputs(&object)?;
                Ok(FrozenAssignmentPlace {
                    binding: place.binding,
                    projections: place.projections,
                    selection: None,
                    inputs,
                })
            }
            AssignTarget::Deref { object, .. } => {
                let object = self.expression(object)?;
                let mut place = object
                    .place()
                    .ok_or("dereference assignment base is not a retained place")?;
                place.projections.push(Projection::Deref);
                let inputs = Self::assignment_inputs(&object)?;
                Ok(FrozenAssignmentPlace {
                    binding: place.binding,
                    projections: place.projections,
                    selection: None,
                    inputs,
                })
            }
            AssignTarget::Index { object, index, .. } => {
                let indexed = AbstractExpr {
                    ty: target_type.clone(),
                    kind: self.index(object, index, target_type)?,
                    span: target_span.clone(),
                };
                let place = indexed
                    .place()
                    .ok_or("indexed assignment base is not a retained place")?;
                let inputs = Self::assignment_inputs(&indexed)?;
                Ok(FrozenAssignmentPlace {
                    binding: place.binding,
                    projections: place.projections,
                    selection: None,
                    inputs,
                })
            }
        }
    }

    fn assignment_inputs(expression: &AbstractExpr) -> Result<Vec<AbstractExpr>, String> {
        match &expression.kind {
            AbstractExprKind::Binding(_) => Ok(Vec::new()),
            AbstractExprKind::Index { object, index, .. } => {
                let mut inputs = Self::assignment_inputs(object)?;
                inputs.push(index.as_ref().clone());
                Ok(inputs)
            }
            AbstractExprKind::Dereference(object)
            | AbstractExprKind::TupleAccess { object, .. }
            | AbstractExprKind::FieldAccess { object, .. } => Self::assignment_inputs(object),
            _ => Err("assignment input operations are not retained".to_string()),
        }
    }

    fn assignment_field_selection(
        &self,
        base: &AbstractType,
        label: &str,
        span: &Span,
        field_type: &AbstractType,
    ) -> Result<AbstractFieldSelection, String> {
        if let Some(field) = self.facts.definition_nominal_fields().get(span) {
            return Ok(AbstractFieldSelection::Nominal {
                label: label.to_string(),
                field: *field,
            });
        }
        self.field_selection(base, label, span, field_type)
    }

    fn closure(
        &self,
        captures: &[crate::data::ast::CaptureSpec],
        axes: (
            crate::data::types::CallMultiplicity,
            crate::data::types::CallMutation,
        ),
        parameters: &[crate::data::ast::Param],
        body: &crate::data::ast::Block,
        ty: &AbstractType,
        span: &Span,
    ) -> Result<AbstractExprKind, String> {
        let (call, mutation) = axes;
        let AbstractType::Function {
            parameters: parameter_types,
            result,
            call: inferred_call,
            mutation: inferred_mutation,
            ..
        } = ty
        else {
            return Err("closure has no retained function type".to_string());
        };
        if parameter_types.len() != parameters.len()
            || *inferred_call != call
            || *inferred_mutation != mutation
        {
            return Err("closure syntax disagrees with its retained function type".to_string());
        }
        let implicit_captures = if captures.is_empty() {
            self.facts
                .definition_implicit_captures(span)
                .ok_or("implicit closure captures have no retained entry facts")?
                .iter()
                .map(|capture| {
                    self.capture_entry(
                        &capture.name,
                        &capture.span,
                        AbstractCaptureMode::ImplicitCopy,
                        &capture.ty,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?
        } else {
            Vec::new()
        };
        let parameters = parameters
            .iter()
            .zip(parameter_types)
            .map(|(parameter, ty)| self.binding(&parameter.name, &parameter.span, ty.clone()))
            .collect::<Result<_, _>>()?;
        let mut captures: Vec<_> = captures
            .iter()
            .map(|capture| self.capture(capture))
            .collect::<Result<_, _>>()?;
        captures.extend(implicit_captures);
        let nested = BodyFreezer {
            types: self.types.clone(),
            facts: self.facts,
            signature: self.signature,
            identity: self.identity,
            return_type: result,
            binding_names: self.binding_names,
            closure_types: self.closure_types,
            loop_results: RefCell::new(Vec::new()),
            registry: self.registry,
            nominal_ownership: self.nominal_ownership,
        };
        Ok(AbstractExprKind::Closure(AbstractClosure {
            captures,
            call,
            mutation,
            parameters,
            body: nested.block(body)?,
        }))
    }

    fn capture(&self, capture: &crate::data::ast::CaptureSpec) -> Result<AbstractCapture, String> {
        let (name, span, mode) = match capture {
            crate::data::ast::CaptureSpec::Owned { name, span } => {
                (name, span, AbstractCaptureMode::Owned)
            }
            crate::data::ast::CaptureSpec::SharedRef { name, span } => {
                (name, span, AbstractCaptureMode::SharedReference)
            }
            crate::data::ast::CaptureSpec::MutRef { name, span } => {
                (name, span, AbstractCaptureMode::MutableReference)
            }
            crate::data::ast::CaptureSpec::Clone { name, span } => {
                (name, span, AbstractCaptureMode::Clone)
            }
        };
        self.capture_entry(
            name,
            span,
            mode,
            self.facts
                .definition_capture_type(span)
                .ok_or("closure capture has no retained entry type")?,
        )
    }

    fn capture_entry(
        &self,
        name: &str,
        span: &Span,
        mode: AbstractCaptureMode,
        ty: &crate::pipeline::type_checking::type_engine::InferType,
    ) -> Result<AbstractCapture, String> {
        let binding = self
            .identity
            .binding_spans
            .get(span)
            .ok_or("closure capture has no frozen binding identity")?;
        let ty = self
            .closure_types
            .borrow()
            .get(&binding)
            .cloned()
            .map_or_else(
                || self.types.freeze(ty).map_err(|error| error.to_string()),
                Ok,
            )?;
        Ok(AbstractCapture {
            binding,
            name: name.to_string(),
            span: span.clone(),
            mode,
            ty,
        })
    }

    fn return_expr(&self, ret: &crate::data::ast::ReturnExpr) -> Result<AbstractExprKind, String> {
        let value = ret
            .value
            .as_deref()
            .map(|value| self.expression(value).map(Box::new))
            .transpose()?;
        if let Some(value) = &value {
            Self::check_value_type(&value.ty, self.return_type)?;
        }
        Ok(AbstractExprKind::Return(value))
    }

    fn control_flow(
        &self,
        expression: &Expr,
        ty: &AbstractType,
    ) -> Result<AbstractExprKind, String> {
        match expression {
            Expr::Return(ret) => self.return_expr(ret),
            Expr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => self.conditional(condition, then_branch, else_branch.as_ref(), ty),
            Expr::Loop { body, .. } => {
                Ok(AbstractExprKind::Loop(self.loop_block(body, ty.clone())?))
            }
            Expr::Break(exit) => {
                let value = exit
                    .value
                    .as_deref()
                    .map(|value| self.expression(value).map(Box::new))
                    .transpose()?;
                let results = self.loop_results.borrow();
                let result = results
                    .last()
                    .ok_or("break has no retained enclosing loop result")?;
                let unit = AbstractType::Concrete(crate::data::types::Type::Unit);
                Self::check_value_type(value.as_ref().map_or(&unit, |value| &value.ty), result)?;
                Ok(AbstractExprKind::Break(value))
            }
            Expr::Continue(_) => Ok(AbstractExprKind::Continue),
            _ => Err("unsupported abstract control-flow expression".to_string()),
        }
    }

    fn tuple_field(
        &self,
        object: &Expr,
        index: usize,
        ty: &AbstractType,
    ) -> Result<AbstractExprKind, String> {
        let object = self.expression(object)?;
        let (base, auto_dereferences) = peel_references(&object.ty);
        let AbstractType::Tuple(fields) = base else {
            return Err("tuple selection has no retained tuple shape".to_string());
        };
        let field = fields
            .get(index)
            .ok_or("tuple selection disagrees with retained tuple shape")?;
        Self::check_value_type(field, ty)?;
        Ok(AbstractExprKind::TupleAccess {
            object: Box::new(object),
            index,
            auto_dereferences,
        })
    }

    fn index(
        &self,
        object: &Expr,
        index: &Expr,
        ty: &AbstractType,
    ) -> Result<AbstractExprKind, String> {
        let object = self.expression(object)?;
        let mut retained_index = self.expression(index)?;
        // Construction applies the u64 expectation to an unsuffixed literal,
        // not to an arbitrary i64 expression. Retain that same contextual
        // literal contract without changing the solved type of any binding.
        if matches!(index, Expr::Literal(crate::data::ast::Literal::Int(value), _) if *value >= 0) {
            retained_index.ty = AbstractType::Concrete(crate::data::types::Type::U64);
        }
        if retained_index.ty != AbstractType::Concrete(crate::data::types::Type::U64) {
            return Err("array index coercion facts are not yet retained".to_string());
        }
        let (base, auto_dereferences) = peel_references(&object.ty);
        let item = match base {
            AbstractType::SizedArray(_, 0)
                if matches!(
                    index,
                    Expr::Literal(
                        crate::data::ast::Literal::Int(_)
                            | crate::data::ast::Literal::SizedInt { .. },
                        _
                    )
                ) =>
            {
                return Err("empty array index validation is not yet retained".to_string());
            }
            AbstractType::Array(item) | AbstractType::SizedArray(item, _) => item,
            _ => return Err("array index has no retained array shape".to_string()),
        };
        Self::check_value_type(item, ty)?;
        Ok(AbstractExprKind::Index {
            object: Box::new(object),
            index: Box::new(retained_index),
            auto_dereferences,
        })
    }

    fn conditional(
        &self,
        condition: &Expr,
        then_branch: &crate::data::ast::Block,
        else_branch: Option<&crate::data::ast::Block>,
        ty: &AbstractType,
    ) -> Result<AbstractExprKind, String> {
        let then_branch = self.block(then_branch)?;
        let else_branch = else_branch.map(|block| self.block(block)).transpose()?;
        Self::check_branch_type(&then_branch, ty)?;
        if let Some(branch) = &else_branch {
            Self::check_branch_type(branch, ty)?;
        }
        Ok(AbstractExprKind::If {
            condition: Box::new(self.expression(condition)?),
            then_branch,
            else_branch,
        })
    }

    fn call(
        &self,
        callee: &Expr,
        args: &[Expr],
        span: &Span,
        result: &AbstractType,
    ) -> Result<AbstractCall, String> {
        let contract = self
            .facts
            .definition_call_types()
            .get(span)
            .ok_or("call selection contract is not retained")?;
        let signature = self
            .types
            .freeze(contract)
            .map_err(|error| error.to_string())?;
        let AbstractType::Function {
            parameters,
            result: returned,
            ..
        } = &signature
        else {
            return Err("call has no retained callable contract".to_string());
        };
        Self::check_value_type(returned, result)?;
        if parameters.len() != args.len() {
            return Err("call argument count disagrees with its retained contract".to_string());
        }
        let arguments = args
            .iter()
            .zip(parameters)
            .map(|(arg, parameter)| {
                let value = self.expression(arg)?;
                Self::check_value_type(&value.ty, parameter)?;
                let mode = match parameter {
                    AbstractType::Reference(_) => AbstractPassingMode::SharedReference,
                    AbstractType::MutReference(_) => AbstractPassingMode::MutableReference,
                    _ => AbstractPassingMode::Value,
                };
                Ok(AbstractArgument { value, mode })
            })
            .collect::<Result<_, String>>()?;
        let callee = if self
            .facts
            .definition_expression_types()
            .contains_key(callee.span())
        {
            self.expression(callee)?
        } else {
            // Named generic calls bypass ordinary expression inference. Their
            // instantiated contract belongs to this use, while lexical resolution
            // still supplies the declaration identity (including recursive calls).
            if !matches!(callee, Expr::Ident(..) | Expr::ResolvedPath { .. }) {
                return Err("call target selection is not fully retained".to_string());
            }
            let binding = self
                .identity
                .binding_spans
                .get(callee.span())
                .ok_or("call target has no frozen identity")?;
            // Name-keyed scheme lookup can find an outer generic even when a
            // local callable shadows it. Without an expression fact tying the
            // contract to that local binding, its ownership axes are unproven.
            if !matches!(binding, crate::identity::BindingId::Global(_)) {
                return Err("local generic call target contract is not fully retained".to_string());
            }
            AbstractExpr {
                ty: signature.clone(),
                kind: AbstractExprKind::Binding(binding),
                span: callee.span().clone(),
            }
        };
        let auto_dereference = matches!(
            callee.ty,
            AbstractType::Reference(_) | AbstractType::MutReference(_)
        );
        let (callable, dereferences) = peel_references(&callee.ty);
        let callable = if let AbstractType::Closure { signature, .. } = callable {
            signature.as_ref()
        } else {
            callable
        };
        if dereferences > 1 || *callable != signature {
            return Err("call target coercion facts are not fully retained".to_string());
        }
        Ok(AbstractCall {
            callee: Box::new(callee),
            signature,
            arguments,
            auto_dereference,
        })
    }

    fn check_branch_type(block: &AbstractBlock, result: &AbstractType) -> Result<(), String> {
        // Unequal branch types may require ownership-affecting row coercions.
        // Their proof must be retained before lowering, not recovered here.
        if let Some(tail) = &block.tail {
            Self::check_value_type(&tail.ty, result)?;
        }
        Ok(())
    }

    fn field(
        &self,
        object: &Expr,
        label: &str,
        span: &Span,
        ty: &AbstractType,
    ) -> Result<AbstractExprKind, String> {
        let object = self.expression(object)?;
        let (base, auto_dereferences) = peel_references(&object.ty);
        let selection = self.field_selection(base, label, span, ty)?;
        Ok(AbstractExprKind::FieldAccess {
            object: Box::new(object),
            selection,
            auto_dereferences,
        })
    }

    fn method_call(
        &self,
        receiver: &Expr,
        method: &str,
        args: &[Expr],
        span: &Span,
        result: &AbstractType,
    ) -> Result<AbstractMethodCall, String> {
        let fact = self
            .facts
            .definition_method_facts()
            .get(span)
            .ok_or("method dispatch contract is not retained")?;
        let signature = self
            .types
            .freeze(&fact.contract)
            .map_err(|error| error.to_string())?;
        let AbstractType::Function {
            parameters,
            result: returned,
            ..
        } = &signature
        else {
            return Err("method dispatch has no retained callable contract".to_string());
        };
        let (receiver_parameter, parameters) = parameters
            .split_first()
            .ok_or("method dispatch has no receiver contract")?;
        Self::check_value_type(returned, result)?;
        if parameters.len() != args.len() {
            return Err("method argument count disagrees with its retained contract".to_string());
        }
        let receiver = self.expression(receiver)?;
        let (receiver_base, _) = peel_references(&receiver.ty);
        Self::check_value_type(receiver_base, receiver_parameter)?;
        let arguments = args
            .iter()
            .zip(parameters)
            .map(|(arg, parameter)| {
                let value = self.expression(arg)?;
                Self::check_value_type(&value.ty, parameter)?;
                let mode = match parameter {
                    AbstractType::Reference(_) => AbstractPassingMode::SharedReference,
                    AbstractType::MutReference(_) => AbstractPassingMode::MutableReference,
                    _ => AbstractPassingMode::Value,
                };
                Ok(AbstractArgument { value, mode })
            })
            .collect::<Result<_, String>>()?;
        let receiver_mode = match fact.receiver {
            crate::data::ast::ReceiverKind::Value => AbstractReceiverMode::Value,
            crate::data::ast::ReceiverKind::Ref => AbstractReceiverMode::SharedReference,
            crate::data::ast::ReceiverKind::RefMut => AbstractReceiverMode::MutableReference,
        };
        Ok(AbstractMethodCall {
            receiver: Box::new(receiver),
            receiver_mode,
            method: method.to_string(),
            origin: fact.origin.clone(),
            signature,
            arguments,
        })
    }

    fn field_selection(
        &self,
        base: &AbstractType,
        label: &str,
        span: &Span,
        ty: &AbstractType,
    ) -> Result<AbstractFieldSelection, String> {
        match base {
            AbstractType::Named { .. } => {
                let field = self
                    .facts
                    .definition_nominal_fields()
                    .get(span)
                    .ok_or("nominal field selection identity is not retained")?;
                Ok(AbstractFieldSelection::Nominal {
                    label: label.to_string(),
                    field: *field,
                })
            }
            AbstractType::Record(fields) | AbstractType::Residual { fields, .. } => {
                let (_, field_ty) = fields
                    .iter()
                    .find(|(name, _)| name == label)
                    .ok_or("structural field selection is not retained")?;
                Self::check_value_type(field_ty, ty)?;
                Ok(AbstractFieldSelection::Structural {
                    label: label.to_string(),
                })
            }
            AbstractType::OpenRecord { fields, tail } => {
                if let Some((_, field_ty)) = fields.iter().find(|(name, _)| name == label) {
                    Self::check_value_type(field_ty, ty)?;
                    Ok(AbstractFieldSelection::Structural {
                        label: label.to_string(),
                    })
                } else {
                    self.field_selection(tail, label, span, ty)
                }
            }
            AbstractType::Parameter(parameter) => {
                let facts = self
                    .signature
                    .facts
                    .as_ref()
                    .and_then(|facts| facts.iter().find(|fact| fact.parameter == *parameter))
                    .ok_or("field grant facts are not retained")?;
                let field_ty = facts
                    .positive
                    .iter()
                    .find_map(|bound| match bound {
                        AbstractBound::Row { fields, .. } => fields
                            .iter()
                            .find(|(name, _)| name == label)
                            .and_then(|(_, ty)| ty.as_ref()),
                        _ => None,
                    })
                    .ok_or("typed field grant is not retained")?;
                Self::check_value_type(field_ty, ty)?;
                Ok(AbstractFieldSelection::Granted {
                    label: label.to_string(),
                    parameter: *parameter,
                })
            }
            _ => Err("field selection contract is not fully retained".to_string()),
        }
    }

    fn check_value_type(value: &AbstractType, result: &AbstractType) -> Result<(), String> {
        if value != result && *value != AbstractType::Never {
            return Err(
                "branch/return coercion facts are not yet retained in abstract bodies".to_string(),
            );
        }
        Ok(())
    }
}

fn peel_references(mut ty: &AbstractType) -> (&AbstractType, usize) {
    let mut depth = 0;
    while let AbstractType::Reference(inner) | AbstractType::MutReference(inner) = ty {
        ty = inner;
        depth += 1;
    }
    (ty, depth)
}

fn assignment_target_span(target: &AssignTarget) -> &Span {
    match target {
        AssignTarget::Ident(_, span)
        | AssignTarget::Deref { span, .. }
        | AssignTarget::Index { span, .. }
        | AssignTarget::FieldAccess { span, .. }
        | AssignTarget::TupleAccess { span, .. } => span,
    }
}
