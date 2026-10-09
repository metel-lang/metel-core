use super::super::ResolvedInferenceFacts;
use super::{AbstractSignature, AbstractType, SignatureFreezer, ordered_variables};
use crate::data::abstract_body::{
    AbstractArgument, AbstractBinding, AbstractBlock, AbstractBody, AbstractBodyPreparation,
    AbstractBound, AbstractCall, AbstractCapture, AbstractCaptureMode, AbstractClosure,
    AbstractExpr, AbstractExprKind, AbstractFieldSelection, AbstractMethodCall,
    AbstractPassingMode, AbstractReceiverMode, AbstractStatement,
};
use crate::data::ast::{AssignOp, AssignTarget, Decl, Expr, FunDecl, Span, Stmt, UnaryOp};
use crate::identity::FrozenIdentity;
use crate::pipeline::type_checking::type_engine::TypeScheme;

struct BodyFreezer<'a, 'return_type> {
    types: SignatureFreezer<'a>,
    facts: &'a ResolvedInferenceFacts,
    signature: &'a AbstractSignature,
    identity: FrozenIdentity<'a>,
    return_type: &'return_type AbstractType,
}

pub(in crate::pipeline::type_checking) fn prepare_abstract_body(
    signature: &AbstractSignature,
    scheme: &TypeScheme,
    declaration: &FunDecl,
    facts: &ResolvedInferenceFacts,
    identity: Option<FrozenIdentity<'_>>,
) -> AbstractBodyPreparation {
    if signature.facts.is_none() {
        return AbstractBodyPreparation::Pending {
            reason: "definition fact environment is not fully retained".to_string(),
        };
    }
    match freeze_body(signature, scheme, declaration, facts, identity) {
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
        block,
    })
}

impl BodyFreezer<'_, '_> {
    fn binding(
        &self,
        name: &str,
        span: &Span,
        ty: AbstractType,
    ) -> Result<AbstractBinding, String> {
        let identity = self
            .identity
            .binding_spans
            .get(span)
            .ok_or_else(|| format!("definition binding `{name}` has no frozen identity"))?;
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
                        body: self.block(&loop_stmt.body)?,
                        span: loop_stmt.span.clone(),
                    });
                }
                _ => {
                    return Err(
                        "loop operations are not yet retained in abstract bodies".to_string()
                    );
                }
            },
            _ => {
                return Err(
                    "nested declarations and patterns are not yet retained in abstract bodies"
                        .to_string(),
                );
            }
        };
        if annotation.is_some() {
            return Err(
                "binding coercion facts are not yet retained in abstract bodies".to_string(),
            );
        }
        let value = self.expression(expression)?;
        let binding = self.binding(name, span, value.ty.clone())?;
        Ok(AbstractStatement::Bind {
            binding,
            mutable,
            value,
        })
    }

    fn expression(&self, expression: &Expr) -> Result<AbstractExpr, String> {
        let inferred = self
            .facts
            .definition_expression_types()
            .get(expression.span())
            .ok_or("definition expression has no solved type fact")?;
        let ty = self
            .types
            .freeze(inferred)
            .map_err(|error| error.to_string())?;
        let kind = match expression {
            Expr::Ident(_, span) => AbstractExprKind::Binding(
                self.identity
                    .binding_spans
                    .get(span)
                    .ok_or("definition reference has no frozen binding identity")?,
            ),
            Expr::Literal(literal, _) => AbstractExprKind::Literal(literal.clone()),
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
                target,
                op: AssignOp::Assign,
                value,
                ..
            } => self.assignment(target, value)?,
            Expr::Closure {
                captures,
                call_multiplicity,
                call_mutation,
                params,
                body,
                ..
            } => self.closure(
                captures,
                *call_multiplicity,
                *call_mutation,
                params,
                body,
                &ty,
            )?,
            Expr::RepeatArray(value, length, _) => AbstractExprKind::RepeatArray {
                value: Box::new(self.expression(value)?),
                length: *length,
            },
            Expr::UnaryOp(UnaryOp::Ref | UnaryOp::RefMut, value, _) => {
                let value = self.expression(value)?;
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
            } => AbstractExprKind::MethodCall(self.method_call(receiver, method, args, span, &ty)?),
            Expr::Return(_)
            | Expr::If { .. }
            | Expr::Loop { .. }
            | Expr::Break(_)
            | Expr::Continue(_) => self.control_flow(expression, &ty)?,
            _ => return Err(
                "expression selection/control-flow facts are not yet retained in abstract bodies"
                    .to_string(),
            ),
        };
        Ok(AbstractExpr {
            ty,
            kind,
            span: expression.span().clone(),
        })
    }

    fn items(&self, items: &[Expr]) -> Result<Vec<AbstractExpr>, String> {
        items.iter().map(|item| self.expression(item)).collect()
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

    fn assignment(&self, target: &AssignTarget, value: &Expr) -> Result<AbstractExprKind, String> {
        let AssignTarget::Ident(_, span) = target else {
            return Err(
                "assignment place facts are not yet retained in abstract bodies".to_string(),
            );
        };
        let target = self
            .identity
            .binding_spans
            .get(span)
            .ok_or("assignment target has no frozen binding identity")?;
        Ok(AbstractExprKind::Assign {
            target,
            value: Box::new(self.expression(value)?),
        })
    }

    fn closure(
        &self,
        captures: &[crate::data::ast::CaptureSpec],
        call: crate::data::types::CallMultiplicity,
        mutation: crate::data::types::CallMutation,
        parameters: &[crate::data::ast::Param],
        body: &crate::data::ast::Block,
        ty: &AbstractType,
    ) -> Result<AbstractExprKind, String> {
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
        let parameters = parameters
            .iter()
            .zip(parameter_types)
            .map(|(parameter, ty)| self.binding(&parameter.name, &parameter.span, ty.clone()))
            .collect::<Result<_, _>>()?;
        let captures = captures
            .iter()
            .map(|capture| self.capture(capture))
            .collect::<Result<_, _>>()?;
        let nested = BodyFreezer {
            types: self.types.clone(),
            facts: self.facts,
            signature: self.signature,
            identity: self.identity,
            return_type: result,
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
        let (span, mode) = match capture {
            crate::data::ast::CaptureSpec::Owned { span, .. } => (span, AbstractCaptureMode::Owned),
            crate::data::ast::CaptureSpec::SharedRef { span, .. } => {
                (span, AbstractCaptureMode::SharedReference)
            }
            crate::data::ast::CaptureSpec::MutRef { span, .. } => {
                (span, AbstractCaptureMode::MutableReference)
            }
            crate::data::ast::CaptureSpec::Clone { span, .. } => (span, AbstractCaptureMode::Clone),
        };
        Ok(AbstractCapture {
            binding: self
                .identity
                .binding_spans
                .get(span)
                .ok_or("closure capture has no frozen binding identity")?,
            mode,
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
                if !matches!(
                    ty,
                    AbstractType::Never | AbstractType::Concrete(crate::data::types::Type::Unit)
                ) {
                    return Err(
                        "value-producing loop coercion facts are not yet retained in abstract bodies"
                            .to_string(),
                    );
                }
                Ok(AbstractExprKind::Loop(self.block(body)?))
            }
            Expr::Break(exit) => {
                if exit.value.is_some() {
                    return Err(
                        "break-value coercion facts are not yet retained in abstract bodies"
                            .to_string(),
                    );
                }
                Ok(AbstractExprKind::Break(None))
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
            aspect: fact.aspect,
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
