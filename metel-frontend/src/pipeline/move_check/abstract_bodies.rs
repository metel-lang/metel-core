//! Ownership of retained definition-time operations (ADR-0063).

use std::collections::{HashMap, HashSet};

use crate::data::abstract_body::{
    AbstractBinding, AbstractBlock, AbstractBodyPreparation, AbstractBound, AbstractCaptureMode,
    AbstractClosure, AbstractExpr, AbstractExprKind, AbstractFieldSelection, AbstractMatchPattern,
    AbstractParameterFacts, AbstractParameterId, AbstractPassingMode, AbstractPlace,
    AbstractReceiverMode, AbstractRecordPattern, AbstractStatement, AbstractType,
};
use crate::data::typed_ast::TypedFunDecl;
use crate::data::types::{CallMultiplicity, Type, UseMultiplicity};
use crate::identity::BindingId;

use super::{Checker, FlowState, MoveCause, MoveViolationKind, Place, Projection};

#[derive(Clone)]
struct Environment<'a> {
    facts: &'a [AbstractParameterFacts],
    nominal_ownership: &'a [crate::data::abstract_body::AbstractNominalOwnership],
    module: &'a [String],
    types: HashMap<BindingId, AbstractType>,
    names: HashMap<String, String>,
    borrowed_captures: HashSet<BindingId>,
    borrowed_array_bindings: HashSet<BindingId>,
}

impl Environment<'_> {
    fn bind(&mut self, binding: &AbstractBinding, state: &mut FlowState) {
        let key = binding_key(binding.identity);
        self.names.insert(key.clone(), binding.name.clone());
        self.types.insert(binding.identity, binding.ty.clone());
        state.bind(&key);
    }

    fn parameter(&self, id: AbstractParameterId) -> Result<&AbstractParameterFacts, String> {
        self.facts
            .iter()
            .find(|facts| facts.parameter == id)
            .ok_or_else(|| "abstract parameter has no retained fact environment".to_string())
    }

    fn equal_parameter_facts(
        &self,
        id: AbstractParameterId,
    ) -> Result<Vec<&AbstractParameterFacts>, String> {
        self.parameter(id)?;
        Ok(crate::data::abstract_body::equal_parameter_facts(
            self.facts, id,
        ))
    }

    fn present_fields(ty: &AbstractType) -> Option<&[(String, AbstractType)]> {
        match ty {
            AbstractType::Record(fields) | AbstractType::Residual { fields, .. } => Some(fields),
            _ => None,
        }
    }
}

impl Checker<'_> {
    /// Analyse a generic definition from its retained abstract body. When that cannot
    /// complete the body is recorded as unanalysed, so `--move-check` fails with `I0011`
    /// rather than passing on a partial result (ADR-0063).
    // arch-implements: ["arch.move-check.requirement-6", "arch.move-check.requirement-10"]
    pub(super) fn analyze_generic_definition(&mut self, fun: &TypedFunDecl, module: &[String]) {
        if self.check_retained_abstract_body(fun, module) {
            return;
        }
        let reason = self.report.abstract_body_fallbacks.last().map_or_else(
            || "abstract analysis did not complete".to_string(),
            |fallback| fallback.reason.clone(),
        );
        self.record_skipped_generic_body(&fun.span, reason);
    }

    pub(super) fn check_retained_abstract_body(
        &mut self,
        fun: &TypedFunDecl,
        module: &[String],
    ) -> bool {
        let body = match &fun.abstract_body {
            Some(AbstractBodyPreparation::Typed(body)) => body,
            Some(AbstractBodyPreparation::Pending { reason }) => {
                return self.record_abstract_fallback(
                    fun,
                    super::AbstractBodyFallbackStage::Preparation,
                    reason.clone(),
                );
            }
            None => {
                return self.record_abstract_fallback(
                    fun,
                    super::AbstractBodyFallbackStage::Preparation,
                    "definition has no retained abstract body".to_string(),
                );
            }
        };
        let Some(signature) = &fun.abstract_signature else {
            return self.record_abstract_fallback(
                fun,
                super::AbstractBodyFallbackStage::Preparation,
                "definition has no retained abstract signature".to_string(),
            );
        };
        let Some(facts) = signature.facts.as_deref() else {
            return self.record_abstract_fallback(
                fun,
                super::AbstractBodyFallbackStage::Preparation,
                "definition has no retained abstract fact environment".to_string(),
            );
        };
        let mut env = Environment {
            facts,
            nominal_ownership: &body.nominal_ownership,
            module,
            types: HashMap::new(),
            names: body
                .binding_names
                .iter()
                .map(|(binding, name)| (binding_key(*binding), name.clone()))
                .collect(),
            borrowed_captures: HashSet::new(),
            borrowed_array_bindings: HashSet::new(),
        };
        let mark = self.report.mark();
        // A definition's exits cannot reach a loop surrounding its declaration.
        let enclosing_loops = std::mem::take(&mut self.loop_frames);
        let mut state = FlowState::default();
        state.push_scope();
        for (parameter, source) in body.parameters.iter().zip(&fun.params) {
            env.bind(parameter, &mut state);
            // Inference retains bare Self even for a borrowed receiver. Ownership
            // must preserve the receiver declaration's access, not grant ownership.
            if matches!(
                source.receiver,
                Some(crate::data::ast::ReceiverKind::Ref | crate::data::ast::ReceiverKind::RefMut)
            ) {
                env.borrowed_captures.insert(parameter.identity);
            }
        }
        let result = self.check_abstract_block(&body.block, &mut env, &mut state);
        self.loop_frames = enclosing_loops;
        if let Err(reason) = result {
            // No partial analysis is presented as a complete ownership result.
            self.report.rewind_to(mark);
            return self.record_abstract_fallback(
                fun,
                super::AbstractBodyFallbackStage::Ownership,
                reason,
            );
        }
        for violation in &mut self.report.violations[mark.violations..] {
            if let Some(name) = env.names.get(violation.use_place.root()) {
                violation.binding.clone_from(name);
                violation.use_place = display_place(&violation.use_place, name);
                violation.moved_place = display_place(&violation.moved_place, name);
            }
        }
        self.report
            .checked_abstract_generic_bodies
            .push(fun.span.clone());
        true
    }

    fn record_abstract_fallback(
        &mut self,
        fun: &TypedFunDecl,
        stage: super::AbstractBodyFallbackStage,
        reason: String,
    ) -> bool {
        self.report
            .abstract_body_fallbacks
            .push(super::AbstractBodyFallback {
                span: fun.span.clone(),
                stage,
                reason,
            });
        false
    }

    fn check_abstract_block(
        &mut self,
        block: &AbstractBlock,
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        state.push_scope();
        for statement in &block.statements {
            self.check_abstract_statement(statement, env, state)?;
        }
        if let Some(tail) = &block.tail {
            self.consume_abstract_expr(tail, env, state, MoveCause::Other)?;
        }
        state.pop_scope();
        Ok(())
    }

    fn check_abstract_statement(
        &mut self,
        statement: &AbstractStatement,
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        if state.diverged {
            return Ok(());
        }
        match statement {
            AbstractStatement::DestructureRecord { pattern, value, .. } => {
                self.check_abstract_record_pattern(pattern, value, env, state)?;
            }
            AbstractStatement::Bind { binding, value, .. } => {
                self.consume_abstract_expr(value, env, state, MoveCause::Other)?;
                env.bind(binding, state);
            }
            AbstractStatement::Expr(expression) => {
                self.observe_abstract_expr(expression, env, state)?;
            }
            AbstractStatement::While {
                condition, body, ..
            } => self.check_abstract_loop(Some(condition), body, env, state)?,
            AbstractStatement::ForIn {
                binding,
                iterable,
                mode,
                body,
                ..
            } => {
                self.check_abstract_for_in(binding, iterable, *mode, body, env, state)?;
            }
            AbstractStatement::For {
                init,
                condition,
                step,
                body,
                ..
            } => {
                state.push_scope();
                if let Some(init) = init {
                    self.check_abstract_statement(init, env, state)?;
                }
                if state.diverged {
                    state.pop_scope();
                    return Ok(());
                }
                let mut result = Ok(());
                self.check_loop_body(
                    env.module,
                    state,
                    condition
                        .as_ref()
                        .is_some_and(|condition| condition.ty != AbstractType::Never),
                    |checker, _, state| {
                        if result.is_ok() {
                            result = checker.check_abstract_for_pass(
                                condition.as_deref(),
                                step.as_deref(),
                                body,
                                env,
                                state,
                            );
                        }
                    },
                );
                state.pop_scope();
                result?;
            }
        }
        Ok(())
    }

    fn check_abstract_for_pass(
        &mut self,
        condition: Option<&AbstractExpr>,
        step: Option<&AbstractExpr>,
        body: &AbstractBlock,
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        if let Some(condition) = condition {
            self.observe_abstract_expr(condition, env, state)?;
        }
        if state.diverged {
            return Ok(());
        }
        let step_scope = state.clone();
        self.check_abstract_block(body, env, state)?;
        // Continue states must pass through the step before becoming back edges.
        // Break and return states must never execute it.
        let frame = self
            .loop_frames
            .last_mut()
            .ok_or("for loop has no flow frame")?;
        let continued = frame.continue_reached;
        frame.continue_reached = false;
        let back_edge = std::mem::take(&mut frame.back_edge);
        if continued {
            if state.diverged {
                // Back-edge unions contain moves, not binding/scope metadata.
                *state = step_scope;
                state.clear_moved();
                state.union_from(&back_edge);
            } else {
                state.union_from(&back_edge);
            }
            state.diverged = false;
        }
        if !state.diverged
            && let Some(step) = step
        {
            self.observe_abstract_expr(step, env, state)?;
        }
        Ok(())
    }

    fn consume_abstract_expr(
        &mut self,
        expr: &AbstractExpr,
        env: &mut Environment<'_>,
        state: &mut FlowState,
        cause: MoveCause,
    ) -> Result<(), String> {
        if state.diverged {
            return Ok(());
        }
        let Some(abstract_place) = expr.place() else {
            if let AbstractExprKind::Tuple(items) | AbstractExprKind::Array(items) = &expr.kind {
                return self.consume_abstract_items(items.iter(), env, state);
            }
            return self.observe_abstract_expr(expr, env, state);
        };
        self.observe_abstract_place_inputs(expr, env, state)?;
        self.consume_abstract_place(expr, &abstract_place, env, state, cause)
    }

    // Pattern projections share one already-evaluated scrutinee. Re-evaluating
    // its indices for each bound field would duplicate their ownership effects.
    fn consume_abstract_place(
        &mut self,
        expr: &AbstractExpr,
        abstract_place: &AbstractPlace,
        env: &Environment<'_>,
        state: &mut FlowState,
        cause: MoveCause,
    ) -> Result<(), String> {
        let place = ownership_place(abstract_place.binding, &abstract_place.projections);
        let copy = self.abstract_is_copy(&expr.ty, env)?;
        if !copy
            && env
                .borrowed_array_bindings
                .contains(&abstract_place.binding)
        {
            self.report_illegal_move(
                &place,
                expr.span.clone(),
                abstract_type_bucket(&expr.ty),
                MoveViolationKind::BorrowedArrayElementMove,
            );
            return Ok(());
        }
        if !copy && env.borrowed_captures.contains(&abstract_place.binding) {
            let diagnostic_place = source_place(expr).unwrap_or_else(|| place.clone());
            self.report_illegal_move(
                &diagnostic_place,
                expr.span.clone(),
                abstract_type_bucket(&expr.ty),
                MoveViolationKind::MoveOutOfReference,
            );
            return Ok(());
        }
        if !copy && let Some(kind) = self.abstract_illegal_move(expr, env)? {
            let diagnostic_place = source_place(expr).unwrap_or_else(|| place.clone());
            self.report_illegal_move(
                &diagnostic_place,
                expr.span.clone(),
                abstract_type_bucket(&expr.ty),
                kind,
            );
            return Ok(());
        }
        self.observe_abstract_place(expr, &place, env, state);
        let empty_residual =
            matches!(&expr.ty, AbstractType::Residual { fields, .. } if fields.is_empty());
        let nominal_remainder = if empty_residual && place.projections().is_empty() {
            env.types
                .get(&abstract_place.binding)
                .map_or(Ok(false), |root| {
                    self.abstract_is_copy(root, env).map(|copy| !copy)
                })?
        } else {
            false
        };
        if !copy || nominal_remainder {
            state.record_move(
                place,
                expr.span.clone(),
                cause,
                abstract_type_bucket(&expr.ty),
            );
        }
        Ok(())
    }

    fn check_abstract_record_pattern(
        &mut self,
        pattern: &AbstractRecordPattern,
        value: &AbstractExpr,
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        self.abstract_record_destructor_absence(&value.ty, env)?;
        if let Some(place) = value.place() {
            self.observe_abstract_place_inputs(value, env, state)?;
            let ownership = ownership_place(place.binding, &place.projections);
            if !self.record_descendant_use_if_moved(&ownership, &value.span, state) {
                self.consume_abstract_record_pattern(pattern, value, &place, env, state)?;
            }
        } else {
            self.consume_abstract_expr(value, env, state, MoveCause::Other)?;
        }
        for binding in pattern
            .bindings
            .iter()
            .filter_map(|field| field.binding.as_ref())
            .chain(pattern.remainder.iter())
        {
            env.bind(binding, state);
        }
        Ok(())
    }

    fn consume_abstract_record_pattern(
        &mut self,
        pattern: &AbstractRecordPattern,
        value: &AbstractExpr,
        place: &AbstractPlace,
        env: &Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        if pattern.remainder.is_some() {
            return self.consume_abstract_place(value, place, env, state, MoveCause::Other);
        }
        for field in pattern.bindings.iter().chain(&pattern.discarded) {
            let field = AbstractExpr {
                ty: field.ty.clone(),
                kind: AbstractExprKind::FieldAccess {
                    object: Box::new(value.clone()),
                    selection: field.selection.clone(),
                    auto_dereferences: 0,
                },
                span: value.span.clone(),
            };
            let place = field
                .place()
                .ok_or("record pattern field has no retained place")?;
            self.consume_abstract_place(&field, &place, env, state, MoveCause::Other)?;
        }
        Ok(())
    }

    fn abstract_record_destructor_absence(
        &self,
        ty: &AbstractType,
        env: &Environment<'_>,
    ) -> Result<(), String> {
        let AbstractType::Parameter(parameter) = ty else {
            return Ok(());
        };
        let facts = env.equal_parameter_facts(*parameter)?;
        if facts
            .iter()
            .any(|fact| fact.record_kind || fact.row_kind || fact.open_row_parameter)
        {
            return Ok(());
        }
        let drop = self
            .registry
            .resolve_type_id(&["std".to_string(), "core".to_string()], "Drop");
        if self.abstract_is_copy(ty, env)? || facts.iter().any(|fact| fact.negative.iter().any(|bound| matches!(bound, AbstractBound::Aspect(aspect) if Some(aspect.identity) == drop))) {
            return Ok(());
        }
        Err("record destructuring requires retained destructor-absence evidence".to_string())
    }

    fn observe_abstract_place(
        &mut self,
        expr: &AbstractExpr,
        place: &Place,
        _env: &Environment<'_>,
        state: &FlowState,
    ) {
        let narrowed_intact = place.projections().is_empty()
            && Environment::present_fields(&expr.ty).is_some_and(|fields| {
                state.moved_record_for_descendant_use(place).is_none()
                    && fields.iter().all(|(label, _)| {
                        state
                            .moved_record_for_whole_use(
                                &place
                                    .clone()
                                    .with_projection(Projection::field(label.clone())),
                            )
                            .is_none()
                    })
            });
        if !narrowed_intact {
            self.record_whole_use_if_moved(place, &expr.span, state, None);
        }
    }

    fn observe_abstract_expr(
        &mut self,
        expr: &AbstractExpr,
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        if let Some(place) = expr.place() {
            self.observe_abstract_place_inputs(expr, env, state)?;
            let place = ownership_place(place.binding, &place.projections);
            self.observe_abstract_place(expr, &place, env, state);
            return Ok(());
        }
        match &expr.kind {
            AbstractExprKind::ArrayView(value) => self.borrow_abstract_receiver(value, env, state),
            AbstractExprKind::SharedReferenceView(value)
            | AbstractExprKind::CallableView(value)
            | AbstractExprKind::RowView(value)
            | AbstractExprKind::RepeatArray { value, .. } => {
                self.consume_abstract_expr(value, env, state, MoveCause::Other)
            }
            AbstractExprKind::Literal(_)
            | AbstractExprKind::StaticMember { .. }
            | AbstractExprKind::UnitVariant(_) => Ok(()),
            AbstractExprKind::ArrayLength(receiver) => {
                self.borrow_abstract_receiver(receiver, env, state)
            }
            AbstractExprKind::Binary { left, right, .. } => {
                self.observe_abstract_expr(left, env, state)?;
                self.observe_abstract_expr(right, env, state)
            }
            AbstractExprKind::Unary { operand, .. } | AbstractExprKind::NumericCast(operand) => {
                self.observe_abstract_expr(operand, env, state)
            }
            AbstractExprKind::Tuple(items) | AbstractExprKind::Array(items) => {
                for item in items {
                    self.observe_abstract_expr(item, env, state)?;
                }
                Ok(())
            }
            AbstractExprKind::StructLiteral { fields } => {
                self.consume_abstract_items(fields.iter().map(|(_, value)| value), env, state)
            }
            AbstractExprKind::RecordLiteral { fields, spread } => {
                self.consume_abstract_record(fields, spread.as_ref(), env, state)
            }
            AbstractExprKind::Borrow {
                value, temporary, ..
            } => {
                if *temporary {
                    self.consume_abstract_expr(value, env, state, MoveCause::Other)
                } else {
                    self.observe_abstract_expr(value, env, state)
                }
            }
            AbstractExprKind::Assign { .. } => self.observe_abstract_assignment(expr, env, state),
            AbstractExprKind::Call(call) => {
                let AbstractType::Function {
                    call: multiplicity, ..
                } = &call.signature
                else {
                    return Err("abstract call has no callable contract".to_string());
                };
                if *multiplicity == CallMultiplicity::Once {
                    self.consume_abstract_receiver(&call.callee, env, state, MoveCause::Other)?;
                } else {
                    self.observe_abstract_expr(&call.callee, env, state)?;
                }
                self.consume_abstract_arguments(&call.arguments, env, state)
            }
            AbstractExprKind::MethodCall(call) => {
                self.observe_abstract_method_call(call, env, state)
            }
            _ => self.observe_abstract_control_flow(expr, env, state),
        }
    }

    fn observe_abstract_assignment(
        &mut self,
        expr: &AbstractExpr,
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        let AbstractExprKind::Assign {
            operator,
            target,
            projections,
            inputs,
            value,
            ..
        } = &expr.kind
        else {
            return Err("abstract assignment lost its retained operation".to_string());
        };
        self.consume_abstract_expr(value, env, state, MoveCause::Other)?;
        if state.diverged {
            return Ok(());
        }
        let base_moved = if let Some((_, base)) = projections.split_last() {
            let base = ownership_place(*target, base);
            self.record_descendant_use_if_moved(&base, &expr.span, state)
        } else {
            false
        };
        for input in inputs {
            self.observe_abstract_expr(input, env, state)?;
            if state.diverged {
                return Ok(());
            }
        }
        let place = ownership_place(*target, projections);
        if !base_moved && !matches!(operator, crate::data::ast::AssignOp::Assign) {
            self.record_whole_use_if_moved(&place, &expr.span, state, None);
        }
        state.reinitialize(&place);
        Ok(())
    }

    fn borrow_abstract_receiver(
        &mut self,
        receiver: &AbstractExpr,
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        if receiver.place().is_some() {
            self.observe_abstract_expr(receiver, env, state)
        } else {
            self.consume_abstract_expr(receiver, env, state, MoveCause::Other)
        }
    }

    fn observe_abstract_method_call(
        &mut self,
        call: &crate::data::abstract_body::AbstractMethodCall,
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        if call.receiver_mode == AbstractReceiverMode::Value {
            self.consume_abstract_receiver(&call.receiver, env, state, MoveCause::ByValueReceiver)?;
        } else {
            self.borrow_abstract_receiver(&call.receiver, env, state)?;
        }
        self.consume_abstract_arguments(&call.arguments, env, state)
    }

    fn observe_abstract_place_inputs(
        &mut self,
        expr: &AbstractExpr,
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        match &expr.kind {
            AbstractExprKind::Index { object, index, .. } => {
                self.observe_abstract_place_inputs(object, env, state)?;
                self.observe_abstract_expr(index, env, state)
            }
            AbstractExprKind::Dereference(object)
            | AbstractExprKind::TupleAccess { object, .. }
            | AbstractExprKind::FieldAccess { object, .. } => {
                self.observe_abstract_place_inputs(object, env, state)
            }
            _ => Ok(()),
        }
    }

    fn consume_abstract_items<'a>(
        &mut self,
        items: impl Iterator<Item = &'a AbstractExpr>,
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        for item in items {
            self.consume_abstract_expr(item, env, state, MoveCause::Other)?;
        }
        Ok(())
    }

    fn consume_abstract_record(
        &mut self,
        fields: &[(String, AbstractExpr)],
        spread: Option<&(Box<AbstractExpr>, usize)>,
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        for index in 0..=fields.len() {
            if let Some((value, position)) = spread
                && *position == index
            {
                self.consume_abstract_expr(value, env, state, MoveCause::Other)?;
            }
            if let Some((_, value)) = fields.get(index) {
                self.consume_abstract_expr(value, env, state, MoveCause::Other)?;
            }
        }
        Ok(())
    }

    fn consume_abstract_arguments(
        &mut self,
        arguments: &[crate::data::abstract_body::AbstractArgument],
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        for argument in arguments {
            if argument.mode == AbstractPassingMode::MutableReference {
                self.observe_abstract_expr(&argument.value, env, state)?;
            } else {
                self.consume_abstract_expr(&argument.value, env, state, MoveCause::Other)?;
            }
        }
        Ok(())
    }

    fn consume_abstract_receiver(
        &mut self,
        receiver: &AbstractExpr,
        env: &mut Environment<'_>,
        state: &mut FlowState,
        cause: MoveCause,
    ) -> Result<(), String> {
        let mut receiver = receiver.clone();
        while let Some(ty) = dereferenced_type(&receiver.ty) {
            receiver = AbstractExpr {
                span: receiver.span.clone(),
                ty,
                kind: AbstractExprKind::Dereference(Box::new(receiver)),
            };
        }
        self.consume_abstract_expr(&receiver, env, state, cause)
    }

    fn check_abstract_closure(
        &mut self,
        closure: &AbstractClosure,
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        let mut inner = env.clone();
        let mut closure_state = FlowState::default();
        closure_state.push_scope();
        for capture in &closure.captures {
            if capture.mode == AbstractCaptureMode::ImplicitCopy
                && !self.abstract_is_copy(&capture.ty, env)?
            {
                return Err(
                    "implicit closure capture lacks a definition-time Copy proof".to_string(),
                );
            }
            let owned = matches!(
                capture.mode,
                AbstractCaptureMode::Owned
                    | AbstractCaptureMode::Clone
                    | AbstractCaptureMode::ImplicitCopy
            );
            let value = AbstractExpr {
                ty: capture.ty.clone(),
                kind: AbstractExprKind::Binding(capture.binding),
                span: capture.span.clone(),
            };
            env.names
                .insert(binding_key(capture.binding), capture.name.clone());
            if capture.mode == AbstractCaptureMode::Owned {
                self.consume_abstract_expr(&value, env, state, MoveCause::Other)?;
            } else {
                self.observe_abstract_expr(&value, env, state)?;
            }
            inner.bind(
                &AbstractBinding {
                    identity: capture.binding,
                    name: capture.name.clone(),
                    ty: capture.ty.clone(),
                },
                &mut closure_state,
            );
            if owned {
                inner.borrowed_captures.remove(&capture.binding);
                inner.borrowed_array_bindings.remove(&capture.binding);
            } else {
                inner.borrowed_captures.insert(capture.binding);
            }
        }
        for parameter in &closure.parameters {
            inner.bind(parameter, &mut closure_state);
        }
        let enclosing_loops = std::mem::take(&mut self.loop_frames);
        let result = self.check_abstract_block(&closure.body, &mut inner, &mut closure_state);
        self.loop_frames = enclosing_loops;
        env.names.extend(inner.names);
        result
    }

    fn observe_abstract_control_flow(
        &mut self,
        expr: &AbstractExpr,
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        match &expr.kind {
            AbstractExprKind::Return(value) | AbstractExprKind::Break(value) => {
                if let Some(value) = value {
                    self.consume_abstract_expr(value, env, state, MoveCause::Other)?;
                }
                if state.diverged {
                    return Ok(());
                }
                if matches!(expr.kind, AbstractExprKind::Break(_)) {
                    self.reach_loop_exit(state);
                }
                state.diverged = true;
                Ok(())
            }
            AbstractExprKind::Continue => {
                self.reach_back_edge(state);
                Ok(())
            }
            AbstractExprKind::Match { scrutinee, arms } => {
                if scrutinee.place().is_some() {
                    self.observe_abstract_expr(scrutinee, env, state)?;
                } else {
                    self.consume_abstract_expr(scrutinee, env, state, MoveCause::Other)?;
                }
                if state.diverged {
                    return Ok(());
                }
                let mut joined = state.clone();
                joined.clear_moved();
                let mut every_arm_diverged = true;
                for (pattern, body) in arms {
                    let mut arm_state = state.clone();
                    arm_state.push_scope();
                    self.apply_abstract_match_pattern(pattern, scrutinee, env, &mut arm_state)?;
                    self.check_abstract_block(body, env, &mut arm_state)?;
                    arm_state.pop_scope();
                    if !arm_state.diverged {
                        joined.union_from(&arm_state);
                        every_arm_diverged = false;
                    }
                }
                joined.diverged = every_arm_diverged;
                *state = joined;
                Ok(())
            }
            AbstractExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.observe_abstract_expr(condition, env, state)?;
                let mut then_state = state.clone();
                self.check_abstract_block(then_branch, env, &mut then_state)?;
                let mut joined = state.clone();
                joined.clear_moved();
                if !then_state.diverged {
                    joined.union_from(&then_state);
                }
                let mut else_state = state.clone();
                if let Some(else_branch) = else_branch {
                    self.check_abstract_block(else_branch, env, &mut else_state)?;
                }
                if !else_state.diverged {
                    joined.union_from(&else_state);
                }
                joined.diverged = then_state.diverged && else_state.diverged;
                *state = joined;
                Ok(())
            }
            AbstractExprKind::Loop(body) => self.check_abstract_loop(None, body, env, state),
            AbstractExprKind::Closure(closure) => self.check_abstract_closure(closure, env, state),
            AbstractExprKind::RecordProjection { .. } => {
                Err("abstract projection consumer is not yet complete".to_string())
            }
            AbstractExprKind::Index { object, index, .. } => {
                if !self.abstract_is_copy(&expr.ty, env)? {
                    return Err(
                        "temporary index ownership contract is not yet retained".to_string()
                    );
                }
                self.consume_abstract_expr(object, env, state, MoveCause::Other)?;
                if state.diverged {
                    return Ok(());
                }
                self.observe_abstract_expr(index, env, state)
            }
            // `*f(x)`: the operand is a temporary reference with no retained place (a place
            // rooted at a binding was handled above). The operand is evaluated once, so a
            // call consumes its arguments; reading through the temporary is a copy, because
            // moving out of a reference is not allowed (RFC-0185).
            AbstractExprKind::Dereference(operand) => {
                if !self.abstract_is_copy(&expr.ty, env)? {
                    return Err("dereference of a temporary reference is not a copy".to_string());
                }
                self.observe_abstract_expr(operand, env, state)
            }
            AbstractExprKind::Binding(_)
            | AbstractExprKind::TupleAccess { .. }
            | AbstractExprKind::FieldAccess { .. } => {
                Err("abstract projection base is not a retained place".to_string())
            }
            _ => Err("abstract operation has no ownership consumer".to_string()),
        }
    }

    fn check_abstract_for_in(
        &mut self,
        binding: &AbstractBinding,
        iterable: &AbstractExpr,
        mode: crate::data::abstract_body::AbstractIterationMode,
        body: &AbstractBlock,
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        self.observe_abstract_expr(iterable, env, state)?;
        let mut result = Ok(());
        self.check_loop_body(env.module, state, true, |checker, _, state| {
            if result.is_err() {
                return;
            }
            state.push_scope();
            env.bind(binding, state);
            if mode == crate::data::abstract_body::AbstractIterationMode::BorrowedArrayElement {
                env.borrowed_array_bindings.insert(binding.identity);
            }
            result = checker.check_abstract_block(body, env, state);
            state.pop_scope();
        });
        result
    }

    fn check_abstract_loop(
        &mut self,
        condition: Option<&AbstractExpr>,
        body: &AbstractBlock,
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        let mut result = Ok(());
        self.check_loop_body(
            env.module,
            state,
            condition.is_some(),
            |checker, _, state| {
                if result.is_err() {
                    return;
                }
                result = condition
                    .map_or(Ok(()), |condition| {
                        checker.observe_abstract_expr(condition, env, state)
                    })
                    .and_then(|()| checker.check_abstract_block(body, env, state));
            },
        );
        result
    }

    fn abstract_illegal_move(
        &self,
        expr: &AbstractExpr,
        env: &Environment<'_>,
    ) -> Result<Option<MoveViolationKind>, String> {
        if expr.place().is_some_and(|place| {
            place
                .projections
                .iter()
                .any(|projection| matches!(projection, Projection::OpaqueIndex))
        }) {
            return Ok(Some(MoveViolationKind::ArrayElementMove));
        }
        let (AbstractExprKind::Dereference(object)
        | AbstractExprKind::TupleAccess { object, .. }
        | AbstractExprKind::FieldAccess { object, .. }) = &expr.kind
        else {
            return Ok(None);
        };
        if dereferenced_type(&object.ty).is_some() {
            return Ok(Some(MoveViolationKind::MoveOutOfReference));
        }
        if self.abstract_has_aspect(&object.ty, env, "Drop")? {
            return Ok(Some(MoveViolationKind::PartialMoveOfDropType));
        }
        self.abstract_illegal_move(object, env)
    }

    fn abstract_is_copy(&self, ty: &AbstractType, env: &Environment<'_>) -> Result<bool, String> {
        self.abstract_is_copy_in(ty, env, &mut HashSet::new())
    }

    fn apply_abstract_match_pattern(
        &mut self,
        pattern: &AbstractMatchPattern,
        scrutinee: &AbstractExpr,
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        let bindings = match pattern {
            AbstractMatchPattern::Wildcard | AbstractMatchPattern::Literal(_) => return Ok(()),
            AbstractMatchPattern::Binding(binding) => vec![binding],
            AbstractMatchPattern::Tuple(patterns) => {
                return self.check_abstract_tuple_pattern(patterns, scrutinee, env, state);
            }
            AbstractMatchPattern::Array {
                elements,
                remainder,
            } => {
                if let Some(place) = scrutinee.place() {
                    self.consume_abstract_place(scrutinee, &place, env, state, MoveCause::Other)?;
                }
                Self::bind_abstract_pattern_values(elements, env, state);
                if let Some(binding) = remainder {
                    env.bind(binding, state);
                }
                return Ok(());
            }
            AbstractMatchPattern::Record(pattern) => {
                return self.check_abstract_record_pattern(pattern, scrutinee, env, state);
            }
            AbstractMatchPattern::Variant { bindings, .. } => {
                bindings.iter().map(|(_, binding)| binding).collect()
            }
        };
        if bindings.is_empty() {
            return Ok(());
        }
        if matches!(
            scrutinee.ty,
            AbstractType::Reference(_) | AbstractType::MutReference(_)
        ) {
            return Err("borrowed match binding move contracts are not yet retained".to_string());
        }
        // The match already evaluated the scrutinee and its indices. Pattern
        // extraction consumes the saved place, not the expression a second time.
        if let Some(place) = scrutinee.place() {
            self.consume_abstract_place(scrutinee, &place, env, state, MoveCause::Other)?;
        }
        for binding in bindings {
            env.bind(binding, state);
        }
        Ok(())
    }

    fn bind_abstract_pattern_values(
        patterns: &[AbstractMatchPattern],
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) {
        for pattern in patterns {
            match pattern {
                AbstractMatchPattern::Binding(binding) => env.bind(binding, state),
                AbstractMatchPattern::Tuple(items) => {
                    Self::bind_abstract_pattern_values(items, env, state);
                }
                AbstractMatchPattern::Array {
                    elements,
                    remainder,
                } => {
                    Self::bind_abstract_pattern_values(elements, env, state);
                    if let Some(binding) = remainder {
                        env.bind(binding, state);
                    }
                }
                AbstractMatchPattern::Wildcard
                | AbstractMatchPattern::Literal(_)
                | AbstractMatchPattern::Record(_)
                | AbstractMatchPattern::Variant { .. } => {}
            }
        }
    }

    fn check_abstract_tuple_pattern(
        &mut self,
        patterns: &[AbstractMatchPattern],
        value: &AbstractExpr,
        env: &mut Environment<'_>,
        state: &mut FlowState,
    ) -> Result<(), String> {
        let AbstractType::Tuple(items) = &value.ty else {
            return Err("tuple pattern has no retained tuple shape".to_string());
        };
        if patterns.len() != items.len() {
            return Err("tuple pattern arity is not retained".to_string());
        }
        for (index, (pattern, item)) in patterns.iter().zip(items).enumerate() {
            let item = AbstractExpr {
                ty: item.clone(),
                kind: AbstractExprKind::TupleAccess {
                    object: Box::new(value.clone()),
                    index,
                    auto_dereferences: 0,
                },
                span: value.span.clone(),
            };
            self.apply_abstract_match_pattern(pattern, &item, env, state)?;
        }
        Ok(())
    }

    // arch-implements: ["arch.move-check.requirement-8"]
    fn abstract_is_copy_in(
        &self,
        ty: &AbstractType,
        env: &Environment<'_>,
        active: &mut HashSet<AbstractParameterId>,
    ) -> Result<bool, String> {
        match ty {
            AbstractType::Closure { owned_captures, .. } => {
                self.abstract_items_copy(owned_captures.iter(), env, active)
            }
            AbstractType::Reference(_) | AbstractType::Array(_) => Ok(true),
            AbstractType::MutReference(_) => Ok(false),
            AbstractType::Function { usage, .. } => Ok(*usage == UseMultiplicity::Copy),
            AbstractType::Tuple(items) => self.abstract_items_copy(items.iter(), env, active),
            AbstractType::Record(fields) | AbstractType::Residual { fields, .. } => {
                self.abstract_items_copy(fields.iter().map(|(_, ty)| ty), env, active)
            }
            AbstractType::OpenRecord { fields, tail } => {
                Ok(
                    self.abstract_items_copy(fields.iter().map(|(_, ty)| ty), env, active)?
                        && self.abstract_is_copy_in(tail, env, active)?,
                )
            }
            AbstractType::SizedArray(item, _) => self.abstract_is_copy_in(item, env, active),
            AbstractType::Parameter(id) => {
                if !active.insert(*id) {
                    return Err(
                        "recursive abstract Copy entailment is not yet supported".to_string()
                    );
                }
                let result = self.abstract_parameter_copy(*id, env, active);
                active.remove(id);
                result
            }
            _ => match self.abstract_has_aspect(ty, env, "Copy") {
                Ok(copy) => Ok(copy),
                Err(reason)
                    if reason
                        == "abstract conditional nominal aspect entailment is not yet retained"
                        && self.is_nominal_record(ty) =>
                {
                    // The standard record `Copy` implementation is conditional
                    // on its row. Without a proof a generic body may still
                    // consume the record, so model this operation as a move.
                    Ok(false)
                }
                Err(reason) => Err(reason),
            },
        }
    }

    fn is_nominal_record(&self, ty: &AbstractType) -> bool {
        matches!(
            ty,
            AbstractType::Named { identity, .. }
                if identity.get().and_then(|id| self.registry.visible_type_kind_by_id(id))
                    == Some(crate::pipeline::type_checking::type_engine::VisibleTypeKind::Record)
        )
    }

    fn abstract_items_copy<'a>(
        &self,
        items: impl Iterator<Item = &'a AbstractType>,
        env: &Environment<'_>,
        active: &mut HashSet<AbstractParameterId>,
    ) -> Result<bool, String> {
        for item in items {
            if !self.abstract_is_copy_in(item, env, active)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn abstract_parameter_copy(
        &self,
        id: AbstractParameterId,
        env: &Environment<'_>,
        active: &mut HashSet<AbstractParameterId>,
    ) -> Result<bool, String> {
        let equal_facts = env.equal_parameter_facts(id)?;
        let identity = self
            .registry
            .resolve_type_id(&["std".to_string(), "core".to_string()], "Copy");
        let structural = equal_facts
            .iter()
            .any(|facts| facts.row_kind || facts.open_row_parameter);
        let granted = equal_facts.iter().any(|facts| {
            facts.positive.iter().any(|bound| match bound {
                AbstractBound::Aspect(aspect) => Some(aspect.identity) == identity,
                AbstractBound::AllFields { aspects, except } => {
                    structural
                        && except.is_empty()
                        && aspects
                            .iter()
                            .any(|aspect| Some(aspect.identity) == identity)
                }
                AbstractBound::Row { .. } => false,
            })
        });
        if granted {
            return Ok(true);
        }
        if structural {
            let composed = self.abstract_composed_row_copy(&equal_facts, env, active);
            let remainder = self.abstract_remainder_copy(id, env, active);
            if matches!(composed, Ok(Some(true))) || matches!(remainder, Ok(Some(true))) {
                return Ok(true);
            }
            let composed = composed?;
            let remainder = remainder?;
            if composed == Some(false) || remainder == Some(false) {
                return Ok(false);
            }
        }
        // A known non-Copy head disproves field-wise Copy independently of
        // whether the open tail's ownership facts are complete.
        if structural
            && equal_facts
                .iter()
                .flat_map(|facts| &facts.positive)
                .any(|bound| {
                    let AbstractBound::Row { fields, .. } = bound else {
                        return false;
                    };
                    fields
                        .iter()
                        .filter_map(|(_, ty)| ty.as_ref())
                        .any(|ty| matches!(self.abstract_is_copy_in(ty, env, active), Ok(false)))
                })
        {
            return Ok(false);
        }
        let conditional_fieldwise = equal_facts.iter().any(|facts| facts.positive.iter().any(|bound| {
            matches!(bound, AbstractBound::AllFields { aspects, except }
                if !except.is_empty() && aspects.iter().any(|aspect| Some(aspect.identity) == identity))
        }));
        // All retained subtraction/composition rules have been searched above.
        // An otherwise unbounded remainder grants no Copy permission, just as
        // an ordinary unbounded row does. That is not an analysis fallback.
        if conditional_fieldwise {
            return Err("derived abstract Copy entailment is not yet retained".to_string());
        }
        Ok(false)
    }

    fn abstract_composed_row_copy(
        &self,
        sources: &[&AbstractParameterFacts],
        env: &Environment<'_>,
        active: &mut HashSet<AbstractParameterId>,
    ) -> Result<Option<bool>, String> {
        let mut unproven = None;
        let mut incomplete = None;
        for tail in env.facts {
            for equation in &tail.remainders {
                if equation.removed.is_empty()
                    || !sources
                        .iter()
                        .any(|source| source.parameter == equation.source)
                {
                    continue;
                }
                let fields = equation
                    .removed
                    .iter()
                    .map(|label| {
                        sources
                            .iter()
                            .flat_map(|source| &source.positive)
                            .find_map(|bound| {
                                let AbstractBound::Row { fields, .. } = bound else {
                                    return None;
                                };
                                fields
                                    .iter()
                                    .find(|(name, _)| name == label)
                                    .and_then(|(_, ty)| ty.as_ref())
                            })
                    })
                    .collect::<Option<Vec<_>>>();
                let Some(fields) = fields else { continue };
                match self.abstract_items_copy(fields.into_iter(), env, active) {
                    Ok(true) => {}
                    Ok(false) => {
                        unproven = Some(false);
                        continue;
                    }
                    Err(reason) => {
                        incomplete = Some(reason);
                        continue;
                    }
                }
                match self.abstract_is_copy_in(
                    &AbstractType::Parameter(tail.parameter),
                    env,
                    active,
                ) {
                    Ok(true) => return Ok(Some(true)),
                    Ok(false) => unproven = Some(false),
                    Err(reason) => incomplete = Some(reason),
                }
            }
        }
        incomplete.map_or(Ok(unproven), Err)
    }

    /// Follow only retained subtraction equations, from a remainder to its
    /// source. Copy of the remainder never proves Copy of the removed fields.
    fn abstract_remainder_copy(
        &self,
        id: AbstractParameterId,
        env: &Environment<'_>,
        active: &mut HashSet<AbstractParameterId>,
    ) -> Result<Option<bool>, String> {
        let identity = self
            .registry
            .resolve_type_id(&["std".to_string(), "core".to_string()], "Copy");
        let mut pending = vec![(id, Vec::<String>::new())];
        let mut visited = HashSet::new();
        let mut unproven = None;
        let mut incomplete = None;
        while let Some((parameter, removed)) = pending.pop() {
            if !visited.insert((parameter, removed.clone())) {
                continue;
            }
            let equal_facts = env.equal_parameter_facts(parameter)?;
            if equal_facts.iter().any(|facts| {
                facts.positive.iter().any(|bound| {
                    matches!(bound, AbstractBound::AllFields { aspects, except }
                        if except.iter().all(|label| removed.contains(label))
                            && aspects.iter().any(|aspect| Some(aspect.identity) == identity))
                        || matches!(bound, AbstractBound::Aspect(aspect)
                            if Some(aspect.identity) == identity
                                && (facts.row_kind || facts.open_row_parameter))
                })
            }) {
                return Ok(Some(true));
            }
            for facts in equal_facts {
                if let Some(fields) = facts.positive.iter().find_map(|bound| match bound {
                    AbstractBound::Row {
                        fields,
                        open: false,
                    } => Some(fields),
                    _ => None,
                }) {
                    let remaining: Vec<_> = fields
                        .iter()
                        .filter(|(label, _)| !removed.contains(label))
                        .cloned()
                        .collect();
                    match self.abstract_closed_row_copy(&remaining, env, active) {
                        Ok(true) => return Ok(Some(true)),
                        Ok(false) => unproven = Some(false),
                        Err(reason) => incomplete = Some(reason),
                    }
                }
                for remainder in &facts.remainders {
                    if remainder.removed.is_empty() {
                        continue;
                    }
                    let mut combined = removed.clone();
                    combined.extend(remainder.removed.iter().cloned());
                    combined.sort();
                    combined.dedup();
                    pending.push((remainder.source, combined));
                }
            }
        }
        incomplete.map_or(Ok(unproven), Err)
    }

    fn abstract_closed_row_copy(
        &self,
        fields: &[(String, Option<AbstractType>)],
        env: &Environment<'_>,
        active: &mut HashSet<AbstractParameterId>,
    ) -> Result<bool, String> {
        for (_, field) in fields {
            let field = field
                .as_ref()
                .ok_or("closed abstract row field has no type evidence")?;
            if !self.abstract_is_copy_in(field, env, active)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn abstract_has_aspect(
        &self,
        ty: &AbstractType,
        env: &Environment<'_>,
        name: &str,
    ) -> Result<bool, String> {
        match ty {
            AbstractType::Concrete(ty) => {
                Ok(self.registry.type_satisfies_aspect(env.module, ty, name))
            }
            AbstractType::Parameter(id) => {
                let equal_facts = env.equal_parameter_facts(*id)?;
                let identity = self
                    .registry
                    .resolve_type_id(&["std".to_string(), "core".to_string()], name);
                Ok(equal_facts.iter().any(|facts| facts.positive.iter().any(|bound| {
                    matches!(bound, AbstractBound::Aspect(aspect) if Some(aspect.identity) == identity)
                })))
            }
            AbstractType::Named { .. } => env
                .nominal_ownership
                .iter()
                .find(|fact| &fact.ty == ty)
                .and_then(|fact| match name {
                    "Copy" => match fact.copy {
                        crate::data::abstract_body::AbstractNominalAspect::Proven(value) => {
                            Some(value)
                        }
                        crate::data::abstract_body::AbstractNominalAspect::Conditional => None,
                    },
                    "Drop" => match fact.drop {
                        crate::data::abstract_body::AbstractNominalAspect::Proven(value) => {
                            Some(value)
                        }
                        crate::data::abstract_body::AbstractNominalAspect::Conditional => None,
                    },
                    _ => None,
                })
                .ok_or_else(|| {
                    "abstract conditional nominal aspect entailment is not yet retained".to_string()
                }),
            // A residual exists only after a partial move, and partially moving a `Drop`
            // type is itself rejected, so a residual never carries `Drop`. Drop dispatch
            // against a narrowed residual is specified as not implemented.
            AbstractType::Residual { .. } if name == "Drop" => Ok(false),
            AbstractType::Residual { .. } | AbstractType::Dyn { .. } => {
                Err("abstract nominal aspect entailment is not yet retained".to_string())
            }
            _ => Ok(false),
        }
    }
}

// The shared flow lattice uses textual roots. Its adapter keys are an injective
// encoding of resolved identities; source names enter only diagnostic rendering.
fn binding_key(binding: BindingId) -> String {
    match binding {
        BindingId::Global(id) => format!("global:{id:?}"),
        BindingId::Local(id) => format!("local:{}", id.0),
    }
}

fn ownership_place(binding: BindingId, projections: &[Projection]) -> Place {
    projections
        .iter()
        .fold(Place::new(binding_key(binding)), |place, projection| {
            place.with_projection(projection.clone())
        })
}

// Auto-dereferences are ownership projections, not source spelling. Explicit
// dereferences remain visible so diagnostics distinguish the two operations.
fn source_place(expr: &AbstractExpr) -> Option<Place> {
    match &expr.kind {
        AbstractExprKind::Binding(binding) => Some(ownership_place(*binding, &[])),
        AbstractExprKind::Dereference(object) => {
            Some(source_place(object)?.with_projection(Projection::Deref))
        }
        AbstractExprKind::FieldAccess {
            object, selection, ..
        } => {
            let label = match selection {
                AbstractFieldSelection::Nominal { label, .. }
                | AbstractFieldSelection::Structural { label }
                | AbstractFieldSelection::Granted { label, .. } => label,
            };
            Some(source_place(object)?.with_projection(Projection::field(label.clone())))
        }
        AbstractExprKind::TupleAccess { object, index, .. } => {
            Some(source_place(object)?.with_projection(Projection::TupleIndex(*index)))
        }
        AbstractExprKind::Index { object, .. } => {
            Some(source_place(object)?.with_projection(Projection::OpaqueIndex))
        }
        _ => None,
    }
}

fn display_place(place: &Place, name: &str) -> Place {
    place
        .projections()
        .iter()
        .fold(Place::new(name.to_string()), |place, projection| {
            place.with_projection(projection.clone())
        })
}

fn abstract_type_bucket(ty: &AbstractType) -> String {
    match ty {
        AbstractType::Concrete(ty) => super::type_bucket(ty),
        AbstractType::Parameter(_) => "abstract parameter".to_string(),
        AbstractType::Reference(_) => "&T".to_string(),
        AbstractType::MutReference(_) => "&var T".to_string(),
        AbstractType::Array(_) => "[T]".to_string(),
        AbstractType::SizedArray(_, _) => "[T; N]".to_string(),
        AbstractType::Tuple(_) => "tuple".to_string(),
        AbstractType::Record(_) | AbstractType::OpenRecord { .. } => "record".to_string(),
        AbstractType::Function { .. } | AbstractType::Closure { .. } => "fun".to_string(),
        AbstractType::Named { name, .. } => format!("named:{name}"),
        AbstractType::Residual { brand, .. } => format!("named:{brand}"),
        AbstractType::Never => super::type_bucket(&Type::Never),
        AbstractType::Dyn { aspect, .. } => format!("dyn {aspect}"),
    }
}

fn dereferenced_type(ty: &AbstractType) -> Option<AbstractType> {
    match ty {
        AbstractType::Reference(inner) | AbstractType::MutReference(inner) => {
            Some((**inner).clone())
        }
        AbstractType::Concrete(Type::Reference(inner) | Type::MutReference(inner)) => {
            Some(AbstractType::Concrete((**inner).clone()))
        }
        _ => None,
    }
}
