use std::collections::{HashMap, HashSet};

use crate::ast::{GenericParam, Polarity, ReceiverKind, Span};
use crate::error::{MetelError, TypeErrorCode};
use crate::typed_ast::{
    FunBody, MethodDispatch, TypedBlock, TypedDecl, TypedExpr, TypedForInit, TypedModule,
    TypedModuleGraph, TypedPattern, TypedPlace, TypedStmt,
};
use crate::typeinference::{
    type_to_infer, AspectAssumptions, GenericBound, InferType, Substitution, TypeCtx,
    TypeDefinitionRegistry, TypeScheme, TypeVar, TypeVarGenerator,
};
use crate::types::Type;

use crate::place::{from_expr as place_from_expr, from_typed_place, Place, Projection};

#[derive(Debug, Clone)]
pub struct MoveViolation {
    pub binding: String,
    pub use_place: Place,
    pub moved_place: Place,
    pub kind: MoveViolationKind,
    pub moved_by_value_receiver: bool,
    /// Coarse shape of the value that moved, for triage: which of these
    /// violations would disappear if a given type became `Copy`. Notably
    /// `T[]`, whose ownership is RFC-0124's open question.
    pub moved_type: String,
    /// Whether the move happened on an earlier iteration of an enclosing loop.
    /// When it did, `use_span` and `moved_span` are often the same site, and the
    /// message has to say so or it reads as pointing at itself.
    pub moved_in_previous_iteration: bool,
    pub use_span: Span,
    pub moved_span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MoveViolationKind {
    UseAfterMove,
    PartialMoveUsedAsWhole,
    PartialMoveOfDropType,
    ArrayElementMove,
    BorrowedArrayElementMove,
    MovedMutReferenceWithoutReborrow,
    MoveOutOfReference,
}

/// Whether a whole-value use of `root`, at a *narrowed* type `ty` (a
/// `Type::Residual` or a narrower `Type::Record`), touches no moved field — in
/// which case it is legal despite `root` being partially moved. Narrowing
/// (RFC-0137 / RFC-0117) removes exactly the moved labels, so this holds by
/// construction; the check is a guard against a stale or wrong type stamp.
///
/// `Named` (the full struct) and every non-row type return `false` here — those
/// are not narrowed, so the ordinary partial-move rule applies.
#[must_use]
fn whole_use_of_narrowed_value_is_intact(state: &FlowState, root: &str, ty: &Type) -> bool {
    let present: Vec<&str> = match ty {
        Type::Residual { fields, .. } | Type::Record(fields) => {
            fields.iter().map(|(name, _)| name.as_str()).collect()
        }
        _ => return false,
    };
    let moved: Vec<Projection> = state.moved_shallow_projections(root);
    // Every field the narrowed type still names must be un-moved.
    present.iter().all(|label| {
        !moved
            .iter()
            .any(|p| matches!(p, Projection::Field { name, .. } if name == label))
    })
}

/// A coarse bucket for `ty`, enough to separate the sequence types from
/// everything else without exploding into one label per user struct.
#[must_use]
pub(crate) fn type_bucket(ty: &Type) -> String {
    match ty {
        Type::Array(_) => "T[]".to_string(),
        Type::SizedArray(_, _) => "[T; N]".to_string(),
        Type::Tuple(_) => "tuple".to_string(),
        Type::Record(_) => "record".to_string(),
        Type::Str => "String".to_string(),
        Type::Reference(_) => "&T".to_string(),
        Type::MutReference(_) => "&var T".to_string(),
        Type::Fun(..) => "fun".to_string(),
        Type::Named(name, _) => format!("named:{}", name.rsplit("::").next().unwrap_or(name)),
        other => format!("other:{other}"),
    }
}

#[derive(Debug, Clone, Default)]
pub struct MoveCheckReport {
    pub violations: Vec<MoveViolation>,
    pub skipped_generic_bodies_user: usize,
    pub skipped_generic_bodies_embedded_std: usize,
    pub unchecked_generic_bodies: Vec<UncheckedGenericBody>,
}

#[derive(Debug, Clone)]
pub struct UncheckedGenericBody {
    pub span: Span,
    pub reason: String,
}

/// Everything a report accumulates, captured so a speculative pass can be undone.
#[derive(Debug, Clone, Copy)]
struct ReportMark {
    violations: usize,
    skipped_user: usize,
    skipped_embedded_std: usize,
    unchecked: usize,
}

impl MoveCheckReport {
    #[must_use]
    pub fn violation_count(&self) -> usize {
        self.violations.len()
    }

    fn mark(&self) -> ReportMark {
        ReportMark {
            violations: self.violations.len(),
            skipped_user: self.skipped_generic_bodies_user,
            skipped_embedded_std: self.skipped_generic_bodies_embedded_std,
            unchecked: self.unchecked_generic_bodies.len(),
        }
    }

    /// Drop everything recorded since `mark`. Used for the probe passes a loop
    /// makes while widening its entry state: those walk the same code the final
    /// pass will walk, and must not report it twice.
    fn rewind_to(&mut self, mark: ReportMark) {
        self.violations.truncate(mark.violations);
        self.skipped_generic_bodies_user = mark.skipped_user;
        self.skipped_generic_bodies_embedded_std = mark.skipped_embedded_std;
        self.unchecked_generic_bodies.truncate(mark.unchecked);
    }

    #[must_use]
    pub fn skipped_generic_bodies_total(&self) -> usize {
        self.skipped_generic_bodies_user + self.skipped_generic_bodies_embedded_std
    }
}

#[must_use]
pub fn collect_graph_violations(graph: &TypedModuleGraph) -> MoveCheckReport {
    let mut checker = Checker::new(&graph.type_registry);
    for module in &graph.modules {
        checker.check_module(module);
    }
    checker.report
}

/// Run the move checker, convert the first violation into a user-facing type error,
/// and return diagnostics for bodies that could not be checked.
///
/// # Errors
/// Returns `T0019` when the graph contains a move-checking violation.
pub fn check_graph(graph: &TypedModuleGraph) -> Result<Vec<String>, MetelError> {
    let report = collect_graph_violations(graph);
    if let Some(violation) = report
        .violations
        .into_iter()
        .find(|violation| !is_embedded_std_span(&violation.use_span))
    {
        let span = violation.use_span.clone();
        return Err(MetelError::type_error(
            TypeErrorCode::T0019,
            violation_message(&violation),
            &span,
        ));
    }
    Ok(report
        .unchecked_generic_bodies
        .into_iter()
        .map(|unchecked| {
            format!(
                "move checking could not analyze generic body at {}:{}:{}: {}",
                unchecked.span.filename, unchecked.span.line, unchecked.span.col, unchecked.reason
            )
        })
        .collect())
}

use crate::flow_state::{FlowState, MoveCause, MoveRecord};

#[derive(Debug, Clone, Default)]
struct GenericMoveEnv {
    placeholders: HashMap<String, TypeVar>,
    assumptions: AspectAssumptions,
    symbolic_aspects: HashMap<String, HashSet<String>>,
    arg_types: Vec<Type>,
}

struct Checker<'a> {
    registry: &'a TypeDefinitionRegistry,
    report: MoveCheckReport,
    type_ctx: Option<TypeCtx>,
    generic_envs: Vec<GenericMoveEnv>,
    /// One frame per enclosing loop body currently being walked, innermost last.
    loop_frames: Vec<LoopFrame>,
}

/// The two ways out of one loop body, plus what a jump out of it has to unwind.
#[derive(Debug, Clone, Default)]
struct LoopFrame {
    /// How deep the scope stack was when this body's pass began. A `break` or
    /// `continue` jumps out of every scope opened since, and the state it
    /// contributes has to be unwound to here first — otherwise a binding that
    /// *shadows* one from outside the loop is still in effect in the recorded
    /// state, hiding the outer binding it displaced (#343).
    scope_depth: usize,
    /// States that reach the loop's back edge through a `continue`, so they
    /// enter the next iteration without falling out of the bottom of the body.
    back_edge: FlowState,
    /// Whether any `break` was reached. Not the same as `exit` being non-empty:
    /// a `break` that moved nothing still means the loop can be left, which is
    /// what decides whether a `loop` hands control back at all.
    exit_reached: bool,
    /// States that leave through a `break` — invisible to the next iteration,
    /// visible after the loop.
    exit: FlowState,
}

/// How many times a loop body may be re-walked while its entry state grows.
///
/// Widening is monotone, so a body converges in one extra pass unless moves
/// cascade through several bindings. Stopping at the cap can only lose a
/// violation the next pass would have found, never invent one.
const MAX_LOOP_PASSES: usize = 8;

impl<'a> Checker<'a> {
    fn new(registry: &'a TypeDefinitionRegistry) -> Self {
        Self {
            registry,
            report: MoveCheckReport::default(),
            type_ctx: None,
            generic_envs: Vec::new(),
            loop_frames: Vec::new(),
        }
    }

    fn check_module(&mut self, module: &TypedModule) {
        let mut state = FlowState::default();
        self.type_ctx = Some(TypeCtx {
            scheme_env: module.scheme_env.clone(),
            registry: self.registry.clone(),
            // The move-checker reconstructs a generic body without identity
            // context — see `TypeCtx::members`'s doc.
            members: None,
            binding_spans: None,
            // metel-core#1125: the move-checker never had a `symbols` table
            // to draw on to begin with (unlike `evaluate_graph_with_options`'s
            // `RuntimeIdentity`), so this stays empty, same as `members` above.
            symbols: None,
            current_module: module.module_path.clone(),
        });
        state.push_scope();
        for decl in &module.decls {
            self.check_decl(decl, &module.module_path, &mut state);
        }
        state.pop_scope();
    }

    fn check_decl(&mut self, decl: &TypedDecl, current_module: &[String], state: &mut FlowState) {
        match decl {
            TypedDecl::Let(let_decl) => {
                self.consume_expr(&let_decl.value, current_module, state);
                state.bind_typed(&let_decl.name, let_decl.value.ty());
            }
            TypedDecl::Mut(mut_decl) => {
                self.consume_expr(&mut_decl.value, current_module, state);
                state.bind_typed(&mut_decl.name, mut_decl.value.ty());
            }
            TypedDecl::Fun(fun) => {
                state.bind(&fun.name);
                match &fun.body {
                    FunBody::Typed(body) => {
                        let mut fn_state = FlowState::default();
                        fn_state.push_scope();
                        for param in &fun.params {
                            fn_state.bind(&param.name);
                        }
                        self.check_block(body, current_module, &mut fn_state);
                        fn_state.pop_scope();
                    }
                    FunBody::Generic(body) => {
                        self.check_generic_body(
                            &fun.name,
                            &fun.generics,
                            &fun.params,
                            body,
                            &fun.span,
                            current_module,
                        );
                    }
                    FunBody::Native(_) => {}
                }
            }
            TypedDecl::Stmt(stmt) => self.check_stmt(stmt, current_module, state),
            TypedDecl::Impl(ib) => {
                // The typechecker itself binds `self` to the bare target type in
                // *every* receiver form — `self`, `&self`, and `&var self` all get
                // the identical unwrapped type internally; `&self`/`&var self` are
                // distinguished only by a separate mutability flag, never by an
                // actual reference type (confirmed by reading both
                // `typechecker/inference.rs` and `typechecker/construction.rs`'s
                // `self`-binding code — a real gap, filed as metel-core#650, far
                // larger than this checker and not fixed here). Move-checking needs
                // to know `self`'s *real* reference-ness to catch #648 (moving a
                // value out of `self` inside a `&self`/`&var self` method), so it
                // tracks a corrected type for `self` in its own `FlowState` — a
                // local, checker-only view, not a change to what the rest of the
                // typechecker believes.
                let self_ty = match &ib.target_type {
                    crate::ast::TypeExpr::Named(name, _) => Some(
                        primitive_type_from_name(name)
                            .unwrap_or_else(|| Type::Named(name.clone(), vec![])),
                    ),
                    _ => None,
                };
                for method in &ib.methods {
                    match &method.body {
                        FunBody::Typed(body) => {
                            let mut fn_state = FlowState::default();
                            fn_state.push_scope();
                            for param in &method.params {
                                let corrected_self_ty = (param.name == "self")
                                    .then_some(())
                                    .and(self_ty.as_ref())
                                    .map(|base| match param.receiver {
                                        Some(ReceiverKind::Ref) => {
                                            Type::Reference(Box::new(base.clone()))
                                        }
                                        Some(ReceiverKind::RefMut) => {
                                            Type::MutReference(Box::new(base.clone()))
                                        }
                                        Some(ReceiverKind::Value) | None => base.clone(),
                                    });
                                match corrected_self_ty {
                                    Some(ty) => fn_state.bind_typed(&param.name, &ty),
                                    None => fn_state.bind(&param.name),
                                }
                            }
                            self.check_block(body, current_module, &mut fn_state);
                            fn_state.pop_scope();
                        }
                        FunBody::Generic(body) => {
                            self.check_generic_method_body(ib, method, body, current_module);
                        }
                        FunBody::Native(_) => {}
                    }
                }
            }
            TypedDecl::Struct(_) | TypedDecl::Enum(_) | TypedDecl::Aspect(_) => {}
        }
    }

    fn check_generic_body(
        &mut self,
        name: &str,
        generics: &[GenericParam],
        params: &[crate::ast::Param],
        body: &crate::ast::Block,
        span: &Span,
        current_module: &[String],
    ) {
        if let Some((typed_body, generic_env)) =
            self.construct_generic_body_for_move(name, generics, params, body, span)
        {
            let mut fn_state = FlowState::default();
            fn_state.push_scope();
            for (param, ty) in params.iter().zip(&generic_env.arg_types) {
                fn_state.bind_typed(&param.name, ty);
            }
            self.generic_envs.push(generic_env);
            self.check_block(&typed_body, current_module, &mut fn_state);
            fn_state.pop_scope();
            self.generic_envs.pop();
        }
    }

    fn construct_generic_body_for_move(
        &mut self,
        name: &str,
        generics: &[GenericParam],
        params: &[crate::ast::Param],
        body: &crate::ast::Block,
        span: &Span,
    ) -> Option<(TypedBlock, GenericMoveEnv)> {
        let Some(type_ctx) = self.type_ctx.as_ref() else {
            self.record_skipped_generic_body(span, "type context was unavailable");
            return None;
        };
        let Some(raw_scheme) = type_ctx.scheme_env.get(name) else {
            self.record_skipped_generic_body(span, "function type scheme was unavailable");
            return None;
        };
        let scheme = scheme_with_source_generics(raw_scheme, generics);
        let Some((arg_types, generic_env)) = Self::generic_sample_args(&scheme, &type_ctx.registry)
        else {
            self.record_skipped_generic_body(
                span,
                "function type scheme could not be converted to symbolic arguments",
            );
            return None;
        };
        let symbolic_type_ctx = type_ctx_with_symbolic_aspect_methods(type_ctx, &generic_env);
        match crate::typechecker::construct_generic_body(
            &scheme,
            params,
            &arg_types,
            body,
            span,
            &symbolic_type_ctx,
            None,
        ) {
            Ok(typed_body) => Some((typed_body, generic_env)),
            Err(error) => {
                let reason =
                    symbolic_method_ambiguity_reason(&error, &generic_env, &type_ctx.registry)
                        .unwrap_or_else(|| error.to_string());
                self.record_skipped_generic_body(span, reason);
                None
            }
        }
    }

    fn check_generic_method_body(
        &mut self,
        impl_block: &crate::typed_ast::TypedImplBlock,
        method: &crate::typed_ast::TypedFunDecl,
        body: &crate::ast::Block,
        current_module: &[String],
    ) {
        if self.type_ctx.is_none() {
            self.record_skipped_generic_body(&method.span, "type context was unavailable");
            return;
        }
        let raw_scheme = self
            .registry
            .generic_method_scheme_for_decl(&method.span)
            .cloned()
            .or_else(|| {
                crate::typechecker::symbolic_impl_method_scheme(
                    self.registry,
                    &impl_block.generics,
                    &method.generics,
                    &impl_block.target_type,
                    impl_block.aspect_name.as_deref(),
                    &method.params,
                    method.return_type.as_ref(),
                )
            });
        let Some(raw_scheme) = raw_scheme else {
            self.record_skipped_generic_body(&method.span, "method type scheme was unavailable");
            return;
        };
        let mut source_generics = impl_block.generics.clone();
        source_generics.extend_from_slice(&method.generics);
        let scheme = scheme_with_source_generics(&raw_scheme, &source_generics);
        let Some(type_ctx) = self.type_ctx.as_ref() else {
            self.record_skipped_generic_body(&method.span, "type context was unavailable");
            return;
        };
        let Some((arg_types, generic_env)) = Self::generic_sample_args(&scheme, &type_ctx.registry)
        else {
            self.record_skipped_generic_body(
                &method.span,
                "method type scheme could not be converted to symbolic arguments",
            );
            return;
        };
        let symbolic_type_ctx = type_ctx_with_symbolic_aspect_methods(type_ctx, &generic_env);
        match crate::typechecker::construct_generic_body(
            &scheme,
            &method.params,
            &arg_types,
            body,
            &method.span,
            &symbolic_type_ctx,
            None,
        ) {
            Ok(typed_body) => {
                let mut fn_state = FlowState::default();
                fn_state.push_scope();
                for (param, ty) in method.params.iter().zip(&generic_env.arg_types) {
                    fn_state.bind_typed(&param.name, ty);
                }
                self.generic_envs.push(generic_env);
                self.check_block(&typed_body, current_module, &mut fn_state);
                fn_state.pop_scope();
                self.generic_envs.pop();
            }
            Err(error) => {
                let reason =
                    symbolic_method_ambiguity_reason(&error, &generic_env, &type_ctx.registry)
                        .unwrap_or_else(|| error.to_string());
                self.record_skipped_generic_body(&method.span, reason);
            }
        }
    }

    fn generic_sample_args(
        scheme: &TypeScheme,
        registry: &TypeDefinitionRegistry,
    ) -> Option<(Vec<Type>, GenericMoveEnv)> {
        let mut subst = Substitution::new();
        let mut generic_env = GenericMoveEnv::default();
        let mut named_samples = HashMap::new();
        for (index, var) in scheme.quantified_vars.iter().enumerate() {
            let placeholder = generic_placeholder_name(*var);
            let sample = Type::Named(placeholder.clone(), Vec::new());
            if let Some(name) = scheme.param_names.get(index) {
                named_samples.insert(name.clone(), type_to_infer(&sample));
            }
            generic_env.placeholders.insert(placeholder, *var);
            if let Some(bounds) = scheme.bounds.get(index) {
                let assumed: HashSet<String> = bounds
                    .iter()
                    .filter_map(GenericBound::aspect_name)
                    .map(ToOwned::to_owned)
                    .collect();
                if !assumed.is_empty() {
                    generic_env.assumptions.insert(*var, assumed);
                }
            }
            subst.bind(*var, type_to_infer(&sample));
        }
        generic_env.symbolic_aspects = symbolic_aspect_assumptions(
            registry,
            &generic_env.placeholders,
            &generic_env.assumptions,
        );
        let InferType::Fun(params, ..) = &scheme.ty else {
            return None;
        };
        let arg_types = params
            .iter()
            .map(|param| {
                let substituted = subst.apply(param);
                infer_to_type(&substitute_named_generics(&substituted, &named_samples))
            })
            .collect::<Option<Vec<_>>>()?;
        generic_env.arg_types.clone_from(&arg_types);
        Some((arg_types, generic_env))
    }

    /// Walk a loop body until the state *entering* it stops growing, then walk it
    /// once more with reporting enabled.
    ///
    /// A single pass cannot see a move that only becomes a violation on the
    /// second iteration: the body's exit state was unioned outwards but never fed
    /// back in, so `loop { let n = eat(s); }` looked clean (#291). Each pass here
    /// therefore collects the state that reaches the loop's *back edge* — the
    /// bottom of the body when control falls through it, plus every `continue`
    /// site — and folds that into the entry state for the next pass.
    ///
    /// Paths that leave through `break` or `return` are excluded from the back
    /// edge, so `loop { let n = eat(s); break; }` stays accepted: the move
    /// happens, but no second iteration observes it. Widening with the body's
    /// whole exit state instead would reject that program — see adr-0045.
    ///
    /// Only the final pass reports. The intermediate ones walk the same code and
    /// would otherwise duplicate every diagnostic inside the body.
    fn check_loop_body(
        &mut self,
        current_module: &[String],
        state: &mut FlowState,
        exits_without_break: bool,
        mut pass: impl FnMut(&mut Self, &[String], &mut FlowState),
    ) {
        let mut entry = state.clone();
        for iteration in 0..MAX_LOOP_PASSES {
            let mark = self.report.mark();
            let mut body_state = entry.clone();
            body_state.diverged = false;
            let scope_depth = body_state.scope_depth();
            self.loop_frames.push(LoopFrame {
                scope_depth,
                ..LoopFrame::default()
            });
            pass(self, current_module, &mut body_state);
            let frame = self.loop_frames.pop().unwrap_or_default();
            let mut back_edge = frame.back_edge;
            let exit = frame.exit;
            // Falling out of the bottom of the body reaches the back edge too.
            // Its scopes are already balanced by the pass, so unwinding is a
            // no-op here — done anyway so the two routes agree by construction.
            if !body_state.diverged {
                back_edge.union_from(&body_state.unwound_to(scope_depth));
            }

            let mut widened = entry.clone();
            widened.union_from(&back_edge);
            if widened.moved_fingerprint() == entry.moved_fingerprint()
                || iteration + 1 == MAX_LOOP_PASSES
            {
                // Settled: this pass saw everything a further one would, so its
                // diagnostics are the ones to keep.
                //
                // After the loop, both ways out are possible: falling out of the
                // bottom (unless every path diverged) and every `break`.
                if !body_state.diverged {
                    state.union_from(&body_state);
                }
                state.union_from(&exit);
                // A `loop` with no reachable `break` never hands control back,
                // so the code around it inherits that. Without this, an outer
                // loop treats its own back edge as live even though an inner
                // `loop { return; }` guarantees it is never taken.
                if !exits_without_break && !frame.exit_reached {
                    state.diverged = true;
                }
                return;
            }
            self.report.rewind_to(mark);
            widened.mark_moves_as_carried_from(&entry);
            entry = widened;
        }
    }

    /// Route the current state to the innermost loop's back edge, as `continue`
    /// does: it reaches the next iteration without falling out of the bottom of
    /// the body, and then this path goes no further.
    fn reach_back_edge(&mut self, state: &mut FlowState) {
        if let Some(depth) = self.loop_frames.last().map(|frame| frame.scope_depth) {
            let unwound = state.unwound_to(depth);
            if let Some(frame) = self.loop_frames.last_mut() {
                frame.back_edge.union_from(&unwound);
            }
        }
        state.diverged = true;
    }

    /// Record a `break`: this path leaves the innermost loop, so what it moved
    /// is visible after the loop but not to the next iteration.
    fn reach_loop_exit(&mut self, state: &FlowState) {
        let Some(depth) = self.loop_frames.last().map(|frame| frame.scope_depth) else {
            return;
        };
        let unwound = state.unwound_to(depth);
        if let Some(frame) = self.loop_frames.last_mut() {
            frame.exit_reached = true;
            frame.exit.union_from(&unwound);
        }
    }

    fn check_stmt(&mut self, stmt: &TypedStmt, current_module: &[String], state: &mut FlowState) {
        match stmt {
            TypedStmt::Expr(expr) => self.observe_expr(expr, current_module, state),
            // The condition is walked inside the pass because the back edge
            // returns to it: `while (peek(s)) { eat(s); }` reads `s` after the
            // first iteration moved it.
            TypedStmt::While(while_stmt) => {
                self.check_loop_body(
                    current_module,
                    state,
                    true,
                    |checker, module, body_state| {
                        checker.observe_expr(&while_stmt.condition, module, body_state);
                        checker.check_block(&while_stmt.body, module, body_state);
                    },
                );
            }
            TypedStmt::For(for_stmt) => {
                state.push_scope();
                if let Some(init) = &for_stmt.init {
                    match init {
                        TypedForInit::Let(let_decl) => {
                            self.consume_expr(&let_decl.value, current_module, state);
                            state.bind_typed(&let_decl.name, let_decl.value.ty());
                        }
                        TypedForInit::Mut(mut_decl) => {
                            self.consume_expr(&mut_decl.value, current_module, state);
                            state.bind_typed(&mut_decl.name, mut_decl.value.ty());
                        }
                        TypedForInit::Expr(expr) => self.observe_expr(expr, current_module, state),
                    }
                }
                // `init` ran once above; condition, body and step all repeat.
                self.check_loop_body(
                    current_module,
                    state,
                    true,
                    |checker, module, body_state| {
                        if let Some(condition) = &for_stmt.condition {
                            checker.observe_expr(condition, module, body_state);
                        }
                        checker.check_block(&for_stmt.body, module, body_state);
                        if let Some(step) = &for_stmt.step {
                            checker.observe_expr(step, module, body_state);
                        }
                    },
                );
                state.pop_scope();
            }
            TypedStmt::ForIn(for_in) => {
                // The iterable is evaluated once, before any iteration.
                self.observe_expr(&for_in.iterable, current_module, state);
                let iterable_ty = peel_type_references(for_in.iterable.ty());
                self.check_loop_body(
                    current_module,
                    state,
                    true,
                    |checker, module, body_state| {
                        body_state.push_scope();
                        match iterable_ty {
                            Type::Array(element_ty) => {
                                body_state.bind_borrowed_array_element(&for_in.binding, element_ty);
                            }
                            Type::SizedArray(element_ty, _) => {
                                body_state.bind_typed(&for_in.binding, element_ty);
                            }
                            _ => body_state.bind(&for_in.binding),
                        }
                        checker.check_block(&for_in.body, module, body_state);
                        body_state.pop_scope();
                    },
                );
            }
        }
    }

    fn check_block(
        &mut self,
        block: &TypedBlock,
        current_module: &[String],
        state: &mut FlowState,
    ) {
        state.push_scope();
        for decl in &block.stmts {
            self.check_decl(decl, current_module, state);
        }
        if let Some(tail) = &block.tail {
            self.consume_expr(tail, current_module, state);
        }
        state.pop_scope();
    }

    // One exhaustive match over every `TypedExpr` variant; splitting it does not
    // shrink the logic, only hides the exhaustiveness check that matters here.
    // Same precedent as `evaluator/display.rs`, `coherence.rs`, `typechecker/
    // conversions.rs`, `path_normalizer.rs`, `evaluator/lvalue.rs`.
    #[allow(clippy::too_many_lines)]
    fn observe_expr(&mut self, expr: &TypedExpr, current_module: &[String], state: &mut FlowState) {
        if let Some(place) = place_from_expr(expr) {
            let narrowed = place.projections().is_empty().then(|| expr.ty());
            self.record_whole_use_if_moved(&place, expr.span(), state, narrowed);
        }
        match expr {
            TypedExpr::Literal(..) | TypedExpr::Ident(..) | TypedExpr::Path { .. } => {}
            TypedExpr::Continue(_) => self.reach_back_edge(state),
            TypedExpr::Tuple(items, ..) | TypedExpr::Array(items, ..) => {
                for item in items {
                    self.observe_expr(item, current_module, state);
                }
            }
            TypedExpr::RecordLiteral { fields, .. } | TypedExpr::StructLiteral { fields, .. } => {
                for (_, value) in fields {
                    self.consume_expr_with_cause(value, current_module, state, MoveCause::Other);
                }
            }
            TypedExpr::RepeatArray(value, ..) => self.consume_expr(value, current_module, state),
            TypedExpr::BinOp(left, _, right, ..) => {
                self.observe_expr(left, current_module, state);
                self.observe_expr(right, current_module, state);
            }
            TypedExpr::UnaryOp(_, inner, ..) => self.observe_expr(inner, current_module, state),
            // `init`'s value is moved into the fresh cell the temporary reference
            // wraps, the same as RepeatArray's element or a struct field's value —
            // it is not itself a place being read, so it's consumed, not observed.
            TypedExpr::RefTemp { init, .. } => self.consume_expr(init, current_module, state),
            TypedExpr::Assign { target, value, .. } => {
                self.observe_assignment_target(target, current_module, state);
                self.consume_expr(value, current_module, state);
                if let Some(place) = from_typed_place(target) {
                    state.reinitialize(&place);
                }
            }
            TypedExpr::Call { callee, args, .. } => {
                self.observe_call_expr(callee, args, current_module, state);
            }
            TypedExpr::MethodCall {
                receiver,
                method,
                args,
                dispatch,
                ..
            } => {
                self.observe_method_call_expr(
                    receiver,
                    method,
                    args,
                    dispatch,
                    current_module,
                    state,
                );
            }
            TypedExpr::FieldAccess { object, .. } | TypedExpr::TupleAccess { object, .. } => {
                self.observe_projection_base_expr(object, current_module, state);
            }
            TypedExpr::Index { object, index, .. } => {
                self.observe_projection_base_expr(object, current_module, state);
                self.observe_expr(index, current_module, state);
            }
            TypedExpr::Cast { expr, .. }
            | TypedExpr::SingletonCoerce { inner: expr, .. }
            | TypedExpr::DynCoerce { inner: expr, .. } => {
                self.observe_expr(expr, current_module, state);
            }
            TypedExpr::Match(m) => self.observe_match_expr(m, current_module, state),
            TypedExpr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => self.observe_if_expr(
                condition,
                then_branch,
                else_branch.as_ref(),
                current_module,
                state,
            ),
            TypedExpr::Loop { body, .. } => self.observe_loop_expr(body, current_module, state),
            TypedExpr::Closure {
                params, body, span, ..
            } => self.observe_closure_expr(params, body, span, current_module, state),
            TypedExpr::GenericClosure {
                name,
                params,
                body,
                span,
                ..
            } => {
                if let Some(name) = name {
                    self.observe_generic_closure_expr(
                        name,
                        params,
                        body,
                        span,
                        current_module,
                        state,
                    );
                } else {
                    self.record_skipped_generic_body(
                        span,
                        "anonymous generic closure has no type scheme lookup key",
                    );
                }
            }
            // `return` and `break` both leave the loop iteration, so whatever
            // they moved never reaches a following iteration.
            TypedExpr::Return(ret) => {
                if let Some(value) = &ret.value {
                    self.consume_expr_with_cause(value, current_module, state, MoveCause::Other);
                }
                state.diverged = true;
            }
            TypedExpr::Break(brk) => {
                if let Some(value) = &brk.value {
                    self.consume_expr(value, current_module, state);
                }
                self.reach_loop_exit(state);
                state.diverged = true;
            }
        }
    }

    fn observe_call_expr(
        &mut self,
        callee: &TypedExpr,
        args: &[TypedExpr],
        current_module: &[String],
        state: &mut FlowState,
    ) {
        if matches!(
            callee.ty(),
            Type::Fun(_, _, crate::types::CallMultiplicity::Once, ..)
        ) {
            // RFC-0134: calling a once closure consumes its callee place even
            // when the body returns early.
            self.consume_expr(callee, current_module, state);
        } else {
            self.observe_expr(callee, current_module, state);
        }
        self.observe_call_args(
            args,
            function_param_types(callee.ty()),
            current_module,
            state,
        );
    }

    fn observe_method_call_expr(
        &mut self,
        receiver: &TypedExpr,
        method: &str,
        args: &[TypedExpr],
        dispatch: &MethodDispatch,
        current_module: &[String],
        state: &mut FlowState,
    ) {
        self.consume_method_receiver(receiver, method, dispatch, current_module, state);
        let param_types = self.method_param_types(receiver.ty(), method, current_module, dispatch);
        self.observe_call_args(args, param_types.as_deref(), current_module, state);
    }

    fn observe_call_args(
        &mut self,
        args: &[TypedExpr],
        param_types: Option<&[Type]>,
        current_module: &[String],
        state: &mut FlowState,
    ) {
        for (index, arg) in args.iter().enumerate() {
            let reborrow = param_types
                .and_then(|params| params.get(index))
                .is_some_and(|param_ty| is_reborrow(arg, param_ty));
            if reborrow {
                self.observe_expr(arg, current_module, state);
            } else {
                self.consume_expr(arg, current_module, state);
            }
        }
    }

    fn observe_match_expr(
        &mut self,
        m: &crate::typed_ast::TypedMatchExpr,
        current_module: &[String],
        state: &mut FlowState,
    ) {
        self.observe_expr(&m.scrutinee, current_module, state);
        let mut joined = state.clone();
        joined.clear_moved();
        // Control reaches the code after a `match` only if some arm falls out of
        // it. An empty match has no arm to fall out of, but it also cannot be
        // entered, so treat it as not diverging rather than as diverging.
        let mut every_arm_diverged = !m.arms.is_empty();
        for arm in &m.arms {
            let mut arm_state = state.clone();
            arm_state.push_scope();
            self.apply_pattern_moves(&arm.pattern, &m.scrutinee, current_module, &mut arm_state);
            if let Some(guard) = &arm.guard {
                self.observe_expr(guard, current_module, &mut arm_state);
            }
            self.check_block(&arm.body, current_module, &mut arm_state);
            arm_state.pop_scope();
            if !arm_state.diverged {
                joined.union_from(&arm_state);
            }
            every_arm_diverged = every_arm_diverged && arm_state.diverged;
        }
        state.union_from(&joined);
        state.diverged = state.diverged || every_arm_diverged;
    }

    fn observe_if_expr(
        &mut self,
        condition: &TypedExpr,
        then_branch: &TypedBlock,
        else_branch: Option<&TypedBlock>,
        current_module: &[String],
        state: &mut FlowState,
    ) {
        self.observe_expr(condition, current_module, state);
        let mut then_state = state.clone();
        self.check_block(then_branch, current_module, &mut then_state);
        let mut joined = state.clone();
        // A branch that ends in `break`, `continue` or `return` never reaches
        // the code after the `if`, so what it moved must not be joined into it
        // (adr-0045). Its moves were already routed to the loop's exit or back
        // edge, so dropping them here loses nothing.
        if !then_state.diverged {
            joined.union_from(&then_state);
        }
        // Without an `else`, the false path always falls through, so the `if` as
        // a whole cannot divert control.
        let mut both_branches_diverged = false;
        if let Some(else_branch) = else_branch {
            let mut else_state = state.clone();
            self.check_block(else_branch, current_module, &mut else_state);
            if !else_state.diverged {
                joined.union_from(&else_state);
            }
            both_branches_diverged = then_state.diverged && else_state.diverged;
        }
        state.union_from(&joined);
        state.diverged = state.diverged || both_branches_diverged;
    }

    fn observe_loop_expr(
        &mut self,
        body: &TypedBlock,
        current_module: &[String],
        state: &mut FlowState,
    ) {
        self.check_loop_body(
            current_module,
            state,
            false,
            |checker, module, body_state| {
                checker.check_block(body, module, body_state);
            },
        );
    }

    fn observe_closure_expr(
        &mut self,
        params: &[crate::ast::Param],
        body: &TypedBlock,
        span: &Span,
        current_module: &[String],
        state: &mut FlowState,
    ) {
        self.capture_closure(
            body,
            params.iter().map(|param| param.name.as_str()),
            span,
            state,
        );
        let mut closure_state = FlowState::default();
        closure_state.push_scope();
        for captured in collect_free_roots_from_typed_block(body, &HashSet::new()) {
            closure_state.bind(&captured.name);
        }
        for param in params {
            closure_state.bind(&param.name);
        }
        self.check_block(body, current_module, &mut closure_state);
        closure_state.pop_scope();
    }

    fn observe_generic_closure_expr(
        &mut self,
        name: &str,
        params: &[crate::ast::Param],
        body: &crate::ast::Block,
        span: &Span,
        current_module: &[String],
        state: &mut FlowState,
    ) {
        if let Some((typed_body, generic_env)) =
            self.construct_generic_body_for_move(name, &[], params, body, span)
        {
            self.capture_closure(
                &typed_body,
                params.iter().map(|param| param.name.as_str()),
                span,
                state,
            );
            let mut closure_state = FlowState::default();
            closure_state.push_scope();
            for captured in collect_free_roots_from_typed_block(&typed_body, &HashSet::new()) {
                closure_state.bind(&captured.name);
            }
            for (param, ty) in params.iter().zip(&generic_env.arg_types) {
                closure_state.bind_typed(&param.name, ty);
            }
            self.generic_envs.push(generic_env);
            self.check_block(&typed_body, current_module, &mut closure_state);
            closure_state.pop_scope();
            self.generic_envs.pop();
        }
    }

    fn consume_expr(&mut self, expr: &TypedExpr, current_module: &[String], state: &mut FlowState) {
        self.consume_expr_with_cause(expr, current_module, state, MoveCause::Other);
    }

    fn consume_expr_with_cause(
        &mut self,
        expr: &TypedExpr,
        current_module: &[String],
        state: &mut FlowState,
        cause: MoveCause,
    ) {
        if let Some(place) = place_from_expr(expr) {
            let root_ty = state
                .binding_type(place.root())
                .cloned()
                .or_else(|| root_place_ty_from_expr(expr).cloned())
                .unwrap_or_else(|| expr.ty().clone());
            match expr {
                TypedExpr::Index { index, .. } => {
                    self.consume_place(&place, &root_ty, expr.span(), current_module, state, cause);
                    self.observe_expr(index, current_module, state);
                }
                TypedExpr::FieldAccess { object, .. } | TypedExpr::TupleAccess { object, .. } => {
                    self.consume_place(&place, &root_ty, expr.span(), current_module, state, cause);
                    self.observe_projection_base_expr(object, current_module, state);
                }
                _ => {
                    // A bare whole-value use: prefer `expr.ty()`, the (possibly
                    // narrowed) type construction stamped on the use site, over
                    // the binding-time type in `state` — so `consume_place` sees
                    // a `Residual` / narrower `Record` and does not flag a legal
                    // use of a narrowed binding (metel-core#950).
                    let use_ty = if place.projections().is_empty() {
                        expr.ty().clone()
                    } else {
                        root_ty.clone()
                    };
                    self.consume_place(&place, &use_ty, expr.span(), current_module, state, cause);
                }
            }
            return;
        }
        // A tuple or array literal takes ownership of its elements, so building
        // one *consumes* them. `observe_expr`'s arm only reads them, which let a
        // banned move slip past every guard `consume_place` applies —
        // `(h.name, 1)` out of a `Drop` type, `(xs[0], 1)` out of an array —
        // and also lost the move itself, so the element stayed usable
        // afterwards. Record and struct literals already consumed their fields;
        // these two were the outliers.
        if let TypedExpr::Tuple(items, ..) | TypedExpr::Array(items, ..) = expr {
            for item in items {
                self.consume_expr_with_cause(item, current_module, state, cause);
            }
            return;
        }
        // Same reasoning as the Tuple/Array case just above: coercing to `dyn
        // Aspect` (RFC-0008 §6) takes ownership of the concrete value into the
        // fat pointer's storage, so it must consume `inner`, not just observe
        // it — `place_from_expr` doesn't see through `DynCoerce` (it isn't
        // itself a place), so without this a non-`Copy` source would stay
        // usable after being erased into a `dyn Aspect`.
        if let TypedExpr::DynCoerce { inner, .. } = expr {
            self.consume_expr_with_cause(inner, current_module, state, cause);
            return;
        }
        self.observe_expr(expr, current_module, state);
    }

    /// Check what an assignment *reads*, which is everything under the final
    /// step but not the target itself.
    ///
    /// Writing to a place does not read it — that is how a moved binding is
    /// made valid again (`let moved = s; s = "again";`), and RFC-0071 allows it.
    /// This previously reported the target as a use, so a moved binding could
    /// never be reassigned; the pattern is idiomatic in a loop body, where the
    /// fixed point now makes it the first thing anyone hits.
    ///
    /// What must still hold is that the write can be *reached*: `p.f = v`
    /// requires a valid `p`, and `*p = v` a valid `p`, both handled by the
    /// per-variant recursion below.
    fn observe_assignment_target(
        &mut self,
        typed_place: &TypedPlace,
        current_module: &[String],
        state: &mut FlowState,
    ) {
        match typed_place {
            TypedPlace::Ident(_, _, _) => {}
            TypedPlace::Deref { object, .. } => self.observe_expr(object, current_module, state),
            TypedPlace::Field { object, .. } | TypedPlace::Tuple { object, .. } => {
                self.observe_projection_base_typed_place(object, current_module, state);
            }
            TypedPlace::Index { object, index, .. } => {
                self.observe_projection_base_typed_place(object, current_module, state);
                self.observe_expr(index, current_module, state);
            }
        }
    }

    fn observe_projection_base_expr(
        &mut self,
        expr: &TypedExpr,
        current_module: &[String],
        state: &mut FlowState,
    ) {
        if let Some(place) = place_from_expr(expr) {
            if self.record_descendant_use_if_moved(&place, expr.span(), state) {
                return;
            }
            match expr {
                TypedExpr::FieldAccess { object, .. } | TypedExpr::TupleAccess { object, .. } => {
                    self.observe_projection_base_expr(object, current_module, state);
                }
                TypedExpr::Index { object, index, .. } => {
                    self.observe_projection_base_expr(object, current_module, state);
                    self.observe_expr(index, current_module, state);
                }
                _ => {}
            }
            return;
        }
        self.observe_expr(expr, current_module, state);
    }

    fn observe_projection_base_typed_place(
        &mut self,
        typed_place: &TypedPlace,
        current_module: &[String],
        state: &mut FlowState,
    ) {
        if let Some(place) = from_typed_place(typed_place) {
            if self.record_descendant_use_if_moved(&place, typed_place_span(typed_place), state) {
                return;
            }
        }
        match typed_place {
            TypedPlace::Ident(_, _, _) => {}
            TypedPlace::Deref { object, .. } => self.observe_expr(object, current_module, state),
            TypedPlace::Field { object, .. } | TypedPlace::Tuple { object, .. } => {
                self.observe_projection_base_typed_place(object, current_module, state);
            }
            TypedPlace::Index { object, index, .. } => {
                self.observe_projection_base_typed_place(object, current_module, state);
                self.observe_expr(index, current_module, state);
            }
        }
    }

    fn consume_method_receiver(
        &mut self,
        receiver: &TypedExpr,
        method: &str,
        dispatch: &MethodDispatch,
        current_module: &[String],
        state: &mut FlowState,
    ) {
        let receiver_kind =
            self.method_receiver_kind(receiver.ty(), method, current_module, dispatch);
        match receiver_kind {
            Some(ReceiverKind::Value) => {
                // Mirrors `illegal_move_kind`'s own `is_copy` gate (the other
                // unconditional-ban mechanism `report_move_out_of_reference`
                // reuses): a reference to a `Copy` pointee can be read back by
                // value freely (RFC-0067a SS3a), so the gate is checked on the
                // *pointee* type (`peel_type_references`), not the reference's
                // own type, which is always `Copy` regardless of what it
                // points to and would otherwise defeat this check entirely.
                if Self::receiver_place_is_behind_a_reference(receiver)
                    && !self.is_copy(current_module, peel_type_references(receiver.ty()))
                {
                    self.report_move_out_of_reference(receiver, current_module, state);
                    return;
                }
                self.consume_expr_with_cause(
                    receiver,
                    current_module,
                    state,
                    MoveCause::ByValueReceiver,
                );
            }
            Some(ReceiverKind::Ref | ReceiverKind::RefMut) | None => {
                self.observe_expr(receiver, current_module, state);
            }
        }
    }

    /// Whether a by-value `self` method's receiver names a place reached
    /// through *any* reference — shared or mutable, and regardless of whether
    /// the deref is implicit (`r.eat()`, where `r: &B`) or written out
    /// (`(*r).eat()`). Both are the same operation: dispatch always resolves
    /// to the same by-value method, and either spelling would move `B` out of
    /// memory this scope does not own.
    ///
    /// Two independent signals, because a reference can appear at either end
    /// of the receiver expression: the receiver's own *type* is still a
    /// reference when the deref has not happened yet (`r`, `pair.0`), or the
    /// receiver's *place* already carries a `Deref` projection when it has
    /// (`*r`, `(*pair.0)`). Checking only one leaves the other spelling as an
    /// unguarded sibling — the exact shape #347's review found in the `&var`
    /// case, so both are checked together here rather than added on demand.
    fn receiver_place_is_behind_a_reference(receiver: &TypedExpr) -> bool {
        if matches!(receiver.ty(), Type::Reference(_) | Type::MutReference(_)) {
            return true;
        }
        place_from_expr(receiver).is_some_and(|place| {
            place
                .projections()
                .iter()
                .any(|projection| matches!(projection, Projection::Deref))
        })
    }

    /// A by-value `self` method cannot be called through a reference: there is
    /// no way to give up a value that lives in memory this scope only
    /// borrows. Rejected outright rather than recorded as a move — this is not
    /// about *prior* move history, so under `--move-check` the value is never
    /// legally observed even once, the same as `illegal_move_kind`'s other
    /// unconditional bans (an array element, a partial move of a `Drop`
    /// type).
    ///
    /// The receiver is still observed first, so a non-identifier receiver
    /// (`pair.0.eat()`) still checks its base object (`pair`) for a prior
    /// move — the same side effect `consume_expr_with_cause`'s own
    /// `FieldAccess`/`TupleAccess` arm produces for an ordinary consumption,
    /// reused here via `observe_expr` rather than re-implemented.
    fn report_move_out_of_reference(
        &mut self,
        receiver: &TypedExpr,
        current_module: &[String],
        state: &mut FlowState,
    ) {
        self.observe_expr(receiver, current_module, state);
        // Name the value actually being moved, not the reference. `r.eat()`
        // reports `(*r)`; `place_from_expr` already added the `Deref` itself
        // for an explicit `(*r).eat()`, so only the remaining *implicit*
        // layers need appending here — `deref_layers` counts them from the
        // receiver's own (already-partially-dereffed) type, so an auto-deref
        // chain more than one layer deep (`rr: &&B`) is still named in full
        // rather than left one layer short.
        //
        // A receiver with **no** nameable place at all — the result of a
        // call, an `if`, a `match`, or a cast, none of which is a place — is
        // still exactly as much a reference as a named one: the borrow is a
        // property of the *type*, not of whether anything binds it. An
        // earlier version of this function returned here without reporting
        // anything, silently accepting `get_ref(&b).eat()` — found by
        // adversarial review of this same commit.
        let moved_place = match place_from_expr(receiver) {
            Some(place) => {
                let layers = deref_layers(receiver.ty());
                (0..layers).fold(place, |p, _| p.with_projection(Projection::Deref))
            }
            None => Place::new("<temporary>".to_string()),
        };
        self.report_illegal_move(
            &moved_place,
            receiver.span().clone(),
            type_bucket(receiver.ty()),
            MoveViolationKind::MoveOutOfReference,
        );
    }

    fn apply_pattern_moves(
        &mut self,
        pattern: &TypedPattern,
        scrutinee: &TypedExpr,
        current_module: &[String],
        state: &mut FlowState,
    ) {
        if let Some(place) = place_from_expr(scrutinee) {
            // The *root's* type, not the scrutinee's. `illegal_move_kind` walks
            // the projection chain from the root looking for a `Drop` ancestor,
            // so handing it `h.name`'s type for the place `h.name` starts the
            // walk one level too deep and never sees `Handle`. The array-element
            // rule is purely syntactic on projections and so survived that,
            // which is why only the `Drop` half was reachable through a pattern.
            let root_ty = root_place_ty_from_expr(scrutinee).unwrap_or_else(|| scrutinee.ty());
            self.apply_pattern_place_move(
                pattern,
                &place,
                root_ty,
                scrutinee.span(),
                current_module,
                state,
            );
        } else {
            Self::observe_pattern_bindings(pattern, state);
        }
    }

    fn apply_pattern_place_move(
        &mut self,
        pattern: &TypedPattern,
        place: &Place,
        root_ty: &Type,
        use_span: &Span,
        current_module: &[String],
        state: &mut FlowState,
    ) {
        match pattern {
            TypedPattern::Wildcard(_) | TypedPattern::Literal(_, _) => {}
            TypedPattern::Binding(name, _, _) => {
                self.consume_place(
                    place,
                    root_ty,
                    use_span,
                    current_module,
                    state,
                    MoveCause::Other,
                );
                state.bind(name);
            }
            TypedPattern::Tuple(items, _) => {
                for (index, item) in items.iter().enumerate() {
                    let child = place.clone().with_projection(Projection::TupleIndex(index));
                    self.apply_pattern_place_move(
                        item,
                        &child,
                        root_ty,
                        use_span,
                        current_module,
                        state,
                    );
                }
            }
            TypedPattern::Record { fields, .. } => {
                for (field, _local) in fields {
                    let child = place
                        .clone()
                        .with_projection(Projection::field(field.clone()));
                    self.consume_place(
                        &child,
                        root_ty,
                        use_span,
                        current_module,
                        state,
                        MoveCause::Other,
                    );
                    state.bind(field);
                }
            }
            TypedPattern::Struct { fields, .. } => {
                for (field, id, _local) in fields {
                    let child = place
                        .clone()
                        .with_projection(Projection::field_with_id(field.clone(), *id));
                    self.consume_place(
                        &child,
                        root_ty,
                        use_span,
                        current_module,
                        state,
                        MoveCause::Other,
                    );
                    state.bind(field);
                }
            }
            TypedPattern::EnumVariant { fields, .. } => {
                if !fields.is_empty() {
                    self.consume_place(
                        place,
                        root_ty,
                        use_span,
                        current_module,
                        state,
                        MoveCause::Other,
                    );
                    for (field, _id, _local) in fields {
                        state.bind(field);
                    }
                }
            }
            TypedPattern::Array { elems, rest, .. } => {
                for item in elems {
                    let child = place.clone().with_projection(Projection::OpaqueIndex);
                    self.apply_pattern_place_move(
                        item,
                        &child,
                        root_ty,
                        use_span,
                        current_module,
                        state,
                    );
                }
                if let Some((rest, _)) = rest {
                    state.bind(rest);
                }
            }
        }
    }

    fn observe_pattern_bindings(pattern: &TypedPattern, state: &mut FlowState) {
        match pattern {
            TypedPattern::Binding(name, _, _) => state.bind(name),
            TypedPattern::Tuple(items, _) => {
                for item in items {
                    Self::observe_pattern_bindings(item, state);
                }
            }
            TypedPattern::Record { fields, .. } => {
                for (field, _local) in fields {
                    state.bind(field);
                }
            }
            TypedPattern::EnumVariant { fields, .. } | TypedPattern::Struct { fields, .. } => {
                for (field, _id, _local) in fields {
                    state.bind(field);
                }
            }
            TypedPattern::Array { elems, rest, .. } => {
                for item in elems {
                    Self::observe_pattern_bindings(item, state);
                }
                if let Some((rest, _)) = rest {
                    state.bind(rest);
                }
            }
            TypedPattern::Wildcard(_) | TypedPattern::Literal(_, _) => {}
        }
    }

    fn capture_closure<'names>(
        &mut self,
        body: &TypedBlock,
        params: impl Iterator<Item = &'names str>,
        span: &Span,
        state: &mut FlowState,
    ) {
        let mut locals: HashSet<String> = params.map(ToOwned::to_owned).collect();
        let captures = collect_free_roots_from_typed_block(body, &locals);
        for capture in captures {
            let CapturedRoot { name, ty } = capture;
            locals.insert(name.clone());
            let capture_place = Place::new(name.clone());
            let Some(capture_ty) = ty.or_else(|| state.binding_type(&name).cloned()) else {
                continue;
            };
            self.consume_place(
                &capture_place,
                &capture_ty,
                span,
                &[],
                state,
                MoveCause::Other,
            );
        }
    }

    fn consume_place(
        &mut self,
        place: &Place,
        root_ty: &Type,
        use_span: &Span,
        current_module: &[String],
        state: &mut FlowState,
        cause: MoveCause,
    ) {
        let place_ty = self
            .type_of_place(root_ty, place, current_module)
            .unwrap_or_else(|| root_ty.clone());
        if state.is_borrowed_array_element(place) && !self.is_copy(current_module, &place_ty) {
            self.report_illegal_move(
                place,
                use_span.clone(),
                type_bucket(&place_ty),
                MoveViolationKind::BorrowedArrayElementMove,
            );
            return;
        }
        if let Some(kind) = self.illegal_move_kind(place, root_ty, &place_ty, current_module) {
            self.report_illegal_move(place, use_span.clone(), type_bucket(&place_ty), kind);
            return;
        }
        // For a bare whole-value use, `place_ty` here is the type construction
        // stamped on the use expression — a `Type::Residual` / narrower `Record`
        // when the binding narrowed. Pass it so a legal use of a narrowed value
        // is not flagged as a partial-move violation (metel-core#950).
        let narrowed = place.projections().is_empty().then_some(&place_ty);
        self.check_place_use_before_move(place, use_span, state, narrowed);
        self.record_move_if_needed(place, &place_ty, use_span, current_module, state, cause);
    }

    fn check_place_use_before_move(
        &mut self,
        place: &Place,
        use_span: &Span,
        state: &FlowState,
        narrowed_whole_ty: Option<&Type>,
    ) {
        self.record_whole_use_if_moved(place, use_span, state, narrowed_whole_ty);
    }

    fn record_move_if_needed(
        &self,
        place: &Place,
        ty: &Type,
        use_span: &Span,
        current_module: &[String],
        state: &mut FlowState,
        cause: MoveCause,
    ) {
        if self.is_copy(current_module, ty) {
            return;
        }
        state.record_move(place.clone(), use_span.clone(), cause, type_bucket(ty));
    }

    fn record_descendant_use_if_moved(
        &mut self,
        place: &Place,
        use_span: &Span,
        state: &FlowState,
    ) -> bool {
        if let Some(record) = state.moved_record_for_descendant_use(place) {
            self.report.violations.push(MoveViolation {
                binding: place.root().to_string(),
                use_place: place.clone(),
                moved_place: record.place.clone(),
                kind: Self::violation_kind(place, record),
                moved_by_value_receiver: record.cause == MoveCause::ByValueReceiver,
                moved_type: record.moved_type.clone(),
                moved_in_previous_iteration: record.from_previous_iteration,
                use_span: use_span.clone(),
                moved_span: record.moved_span.clone(),
            });
            return true;
        }
        false
    }

    fn record_whole_use_if_moved(
        &mut self,
        place: &Place,
        use_span: &Span,
        state: &FlowState,
        narrowed_whole_ty: Option<&Type>,
    ) {
        // RFC-0137 / RFC-0117 (metel-core#950): a whole-value use of a binding
        // whose *type* has narrowed to a residual / narrower record is legal —
        // narrowing removed exactly the moved fields, so no still-live use
        // touches a moved one. Construction stamps that narrowed type on the use
        // expression; trust it when every field it still names is un-moved.
        if let Some(ty) = narrowed_whole_ty {
            if whole_use_of_narrowed_value_is_intact(state, place.root(), ty) {
                return;
            }
        }
        if let Some(record) = state.moved_record_for_whole_use(place) {
            self.report.violations.push(MoveViolation {
                binding: place.root().to_string(),
                use_place: place.clone(),
                moved_place: record.place.clone(),
                kind: Self::violation_kind(place, record),
                moved_by_value_receiver: record.cause == MoveCause::ByValueReceiver,
                moved_type: record.moved_type.clone(),
                moved_in_previous_iteration: record.from_previous_iteration,
                use_span: use_span.clone(),
                moved_span: record.moved_span.clone(),
            });
        }
    }

    fn record_skipped_generic_body(&mut self, span: &Span, reason: impl Into<String>) {
        if is_embedded_std_span(span) {
            self.report.skipped_generic_bodies_embedded_std += 1;
        } else {
            self.report.skipped_generic_bodies_user += 1;
            self.report
                .unchecked_generic_bodies
                .push(UncheckedGenericBody {
                    span: span.clone(),
                    reason: reason.into(),
                });
        }
    }

    fn is_copy(&self, current_module: &[String], ty: &Type) -> bool {
        matches!(
            peel_type_references(ty),
            Type::Fun(_, _, _, crate::types::UseMultiplicity::Copy, _)
        ) || self.type_satisfies_aspect(current_module, ty, "Copy")
    }

    fn is_drop(&self, current_module: &[String], ty: &Type) -> bool {
        self.type_satisfies_aspect(current_module, ty, "Drop")
    }

    fn type_satisfies_aspect(
        &self,
        current_module: &[String],
        ty: &Type,
        aspect_name: &str,
    ) -> bool {
        let Some(generic_env) = self.generic_envs.last() else {
            return self
                .registry
                .type_satisfies_aspect(current_module, ty, aspect_name);
        };
        if let Type::Named(name, args) = peel_type_references(ty) {
            if args.is_empty()
                && generic_env
                    .symbolic_aspects
                    .get(name)
                    .is_some_and(|aspects| aspects.contains(aspect_name))
            {
                return true;
            }
        }
        let infer_ty = type_to_infer_under_generic_env(ty, &generic_env.placeholders);
        self.registry.infer_type_satisfies_aspect(
            current_module,
            &infer_ty,
            aspect_name,
            &generic_env.assumptions,
        )
    }

    fn illegal_move_kind(
        &self,
        place: &Place,
        root_ty: &Type,
        place_ty: &Type,
        current_module: &[String],
    ) -> Option<MoveViolationKind> {
        if self.is_copy(current_module, place_ty) {
            return None;
        }
        if place
            .projections()
            .iter()
            .any(|projection| matches!(projection, Projection::OpaqueIndex))
        {
            return Some(MoveViolationKind::ArrayElementMove);
        }

        // #648: a reference only ever grants access to what it points at, never
        // ownership (RFC-0071 SS7.1) — banned the moment a projection step reads
        // *through* one, regardless of whether the crossing is explicit (`*r`,
        // a `Deref` projection) or implicit (auto-deref through a reference-typed
        // field or tuple element, which carries no `Deref` projection at all).
        // `prefix_ty` is checked *before* projecting through it, mirroring the
        // `is_drop` check below exactly, so this fires at the first step that
        // actually crosses a reference rather than at the place's root or its
        // final leaf type. The leaf is already known non-`Copy` by the early
        // return above, so no further `Copy` check is needed here — reading a
        // `Copy` value back out through a reference is exactly what `Copy`
        // permits (RFC-0067a SS3a).
        let mut prefix_ty = root_ty.clone();
        for projection in place.projections() {
            if matches!(prefix_ty, Type::Reference(_) | Type::MutReference(_)) {
                return Some(MoveViolationKind::MoveOutOfReference);
            }
            if self.is_drop(current_module, &prefix_ty) {
                return Some(MoveViolationKind::PartialMoveOfDropType);
            }
            prefix_ty = self.project_type(&prefix_ty, projection, current_module)?;
        }
        None
    }

    fn type_of_place(
        &self,
        root_ty: &Type,
        place: &Place,
        current_module: &[String],
    ) -> Option<Type> {
        let mut ty = root_ty.clone();
        for projection in place.projections() {
            ty = self.project_type(&ty, projection, current_module)?;
        }
        Some(ty)
    }

    fn project_type(
        &self,
        base_ty: &Type,
        projection: &Projection,
        current_module: &[String],
    ) -> Option<Type> {
        let peeled = peel_type_references(base_ty);
        match projection {
            Projection::TupleIndex(index) => match peeled {
                Type::Tuple(items) => items.get(*index).cloned(),
                _ => None,
            },
            Projection::OpaqueIndex => match peeled {
                Type::Array(item) | Type::SizedArray(item, _) => Some((**item).clone()),
                _ => None,
            },
            // `peel_type_references` has already stripped the reference, so the
            // peeled type *is* the pointee.
            Projection::Deref => Some(peeled.clone()),
            Projection::Field { name: field, id } => match peeled {
                Type::Record(fields) => fields
                    .iter()
                    .find(|(name, _)| name == field)
                    .map(|(_, ty)| ty.clone()),
                Type::Named(name, args) => {
                    let (type_id, _resolved_name, fields) = self
                        .registry
                        .projection_struct_fields(current_module, name)?;
                    // Prefer the interned `FieldId` (ADR-0054 / #1068); the
                    // declared name is the documented fallback for a place with
                    // no resolved id (an assignment target, an RFC-0137
                    // narrowing-synthesised projection) or an unstamped registry
                    // (move-check run with no identity context).
                    let field_entry = id
                        .as_ref()
                        .and_then(|fid| fields.iter().find(|entry| entry.id.as_ref() == Some(fid)))
                        .or_else(|| fields.iter().find(|entry| entry.name == *field))?;
                    let raw_ty = field_entry.ty.clone();
                    let infer_ty = if let Some(type_params) =
                        self.registry.struct_type_params_by_id(type_id)
                    {
                        let mut remap = Substitution::new();
                        for (&param, arg) in type_params.iter().zip(args.iter()) {
                            remap.bind(param, type_to_infer(arg));
                        }
                        remap.apply(&raw_ty)
                    } else {
                        raw_ty
                    };
                    infer_to_type(&infer_ty)
                }
                _ => None,
            },
        }
    }

    fn report_illegal_move(
        &mut self,
        place: &Place,
        use_span: Span,
        moved_type: String,
        kind: MoveViolationKind,
    ) {
        self.report.violations.push(MoveViolation {
            binding: place.root().to_string(),
            use_place: place.clone(),
            moved_place: place.clone(),
            kind,
            moved_by_value_receiver: false,
            moved_type,
            moved_in_previous_iteration: false,
            use_span,
            moved_span: dummy_span_from_place(place),
        });
    }

    fn violation_kind(place: &Place, record: &MoveRecord) -> MoveViolationKind {
        if record.moved_type == "&var T" && record.cause != MoveCause::ByValueReceiver {
            return MoveViolationKind::MovedMutReferenceWithoutReborrow;
        }
        if place.projections().is_empty() && !record.place.projections().is_empty() {
            return MoveViolationKind::PartialMoveUsedAsWhole;
        }
        MoveViolationKind::UseAfterMove
    }

    fn method_receiver_kind(
        &self,
        receiver_ty: &Type,
        method: &str,
        current_module: &[String],
        _dispatch: &MethodDispatch,
    ) -> Option<ReceiverKind> {
        if let Some((_, method_def, _)) = self.symbolic_aspect_method(receiver_ty, method) {
            return method_def
                .params
                .first()
                .and_then(|param| param.receiver.clone());
        }
        match peel_type_references(receiver_ty) {
            Type::Array(_) => self.registry.array_method_receiver_kind(method).cloned(),
            Type::Named(name, _) => self
                .registry
                .method_receiver_kind(current_module, name, method)
                .cloned(),
            other => primitive_type_name(other).and_then(|name| {
                self.registry
                    .method_receiver_kind(current_module, &name, method)
                    .cloned()
            }),
        }
    }

    fn method_param_types(
        &self,
        receiver_ty: &Type,
        method: &str,
        current_module: &[String],
        _dispatch: &MethodDispatch,
    ) -> Option<Vec<Type>> {
        if let Some((aspect, method_def, placeholder)) =
            self.symbolic_aspect_method(receiver_ty, method)
        {
            return crate::typechecker::symbolic_aspect_method_type(
                self.registry,
                &aspect,
                &method_def,
                &placeholder,
            )
            .as_ref()
            .and_then(infer_method_arg_types);
        }
        match peel_type_references(receiver_ty) {
            Type::Array(_) => self
                .registry
                .array_method_type(method)
                .and_then(infer_method_arg_types),
            Type::Named(name, _) => self
                .registry
                .method_type(current_module, name, method)
                .and_then(infer_method_arg_types),
            other => primitive_type_name(other).and_then(|name| {
                self.registry
                    .method_type(current_module, &name, method)
                    .and_then(infer_method_arg_types)
            }),
        }
    }

    // metel-core#989: the symbolic-aspect helpers below still look aspects up by bare
    // short name. `--move-check` is opt-in, and these reconstruct a generic parameter's
    // proven aspect bounds — a narrow path. On the rare same-short-name-across-modules
    // collision the registry's bare accessor now returns `None` (a missed symbolic
    // resolution) rather than the wrong aspect's methods; threading `current_module`
    // through here is deferred.
    fn symbolic_aspect_method(
        &self,
        receiver_ty: &Type,
        method: &str,
    ) -> Option<(String, crate::ast::AspectMethod, String)> {
        let Type::Named(placeholder, args) = peel_type_references(receiver_ty) else {
            return None;
        };
        if !args.is_empty() {
            return None;
        }
        let generic_env = self.generic_envs.last()?;
        let aspects = generic_env.symbolic_aspects.get(placeholder)?;
        let mut matches = aspects.iter().filter_map(|aspect| {
            self.registry
                .aspect_method_defs(aspect)?
                .iter()
                .find(|method_def| method_def.name == method)
                .cloned()
                .map(|method_def| (aspect.clone(), method_def, placeholder.clone()))
        });
        let result = matches.next()?;
        if matches.next().is_some() {
            return None;
        }
        Some(result)
    }
}

fn function_param_types(ty: &Type) -> Option<&[Type]> {
    match ty {
        Type::Fun(params, ..) => Some(params),
        _ => None,
    }
}

fn is_embedded_std_span(span: &Span) -> bool {
    span.filename.starts_with("<embedded std::")
}

fn generic_placeholder_name(var: TypeVar) -> String {
    format!("__metel_move_check_generic_{}", var.0)
}

fn scheme_with_source_generics(scheme: &TypeScheme, generics: &[GenericParam]) -> TypeScheme {
    let mut repaired = scheme.clone();
    let existing = repaired.quantified_vars.len();
    repaired.bounds.resize_with(existing, Vec::new);
    repaired.neg_bounds.resize_with(existing, Vec::new);
    repaired.record_kinds.resize(existing, false);
    repaired.assoc_projections.resize(existing, None);
    repaired
        .assoc_eq_constraints
        .resize_with(existing, Vec::new);
    repaired.opaque_returns.resize(existing, None);
    let mut replacements = HashMap::new();
    let mut gen = TypeVarGenerator::with_counter(4_000_000);
    for generic in generics {
        if repaired.param_names.contains(&generic.name) {
            continue;
        }
        let var = gen.fresh();
        replacements.insert(generic.name.clone(), InferType::Var(var));
        repaired.quantified_vars.push(var);
        repaired.param_names.push(generic.name.clone());
        repaired.bounds.push(
            generic
                .bounds
                .iter()
                .filter(|bound| bound.polarity == Polarity::Positive)
                .filter_map(GenericBound::from_ast)
                .collect(),
        );
        repaired.neg_bounds.push(
            generic
                .bounds
                .iter()
                .filter(|bound| bound.polarity == Polarity::Negative)
                .filter_map(GenericBound::from_ast)
                .collect(),
        );
        repaired.record_kinds.push(generic.is_record);
        repaired.assoc_projections.push(None);
        repaired.assoc_eq_constraints.push(Vec::new());
        repaired.opaque_returns.push(None);
    }
    repaired.ty = substitute_named_generics(&repaired.ty, &replacements);
    repaired
}

fn type_ctx_with_symbolic_aspect_methods(
    type_ctx: &TypeCtx,
    generic_env: &GenericMoveEnv,
) -> TypeCtx {
    let mut enriched = type_ctx.clone();
    let mut method_gen = TypeVarGenerator::with_counter(2_000_000);
    for (placeholder, aspects) in &generic_env.symbolic_aspects {
        enriched
            .registry
            .register_symbolic_named_aspects(placeholder.clone(), aspects.clone());
        let mut methods: HashMap<String, Vec<(String, crate::ast::AspectMethod)>> = HashMap::new();
        for aspect in aspects {
            let Some(method_defs) = enriched.registry.aspect_method_defs(aspect) else {
                continue;
            };
            for method in method_defs {
                methods
                    .entry(method.name.clone())
                    .or_default()
                    .push((aspect.clone(), method.clone()));
            }
        }
        for candidates in methods.into_values() {
            let [(aspect, method)] = candidates.as_slice() else {
                continue;
            };
            let Some(method_scheme) = crate::typechecker::symbolic_aspect_method_scheme(
                &enriched.registry,
                aspect,
                method,
                placeholder,
                &mut method_gen,
            ) else {
                continue;
            };
            // metel-core#1124: `placeholder` names a generic parameter, not a
            // real declaration -- the name resolver never assigns it a
            // `SymbolId`, so mint/reuse a local placeholder one to register
            // these methods under (the method tables are `SymbolId`-keyed).
            let owner = enriched.registry.local_placeholder_id(placeholder);
            enriched.registry.register_method_scheme(
                owner,
                method.name.clone(),
                method_scheme.clone(),
                Vec::new(),
            );
            enriched.registry.register_method_scheme_variant(
                owner,
                method.name.clone(),
                method_scheme,
                Vec::new(),
                Some(aspect.clone()),
                method.span.clone(),
            );
            if let Some(receiver) = method
                .params
                .first()
                .and_then(|param| param.receiver.clone())
            {
                enriched
                    .registry
                    .register_method_receiver(owner, method.name.clone(), receiver);
            }
        }
    }
    enriched
}

fn symbolic_aspect_assumptions(
    registry: &TypeDefinitionRegistry,
    placeholders: &HashMap<String, TypeVar>,
    assumptions: &AspectAssumptions,
) -> HashMap<String, HashSet<String>> {
    let mut symbolic_aspects: HashMap<String, HashSet<String>> = placeholders
        .iter()
        .filter_map(|(placeholder, var)| {
            assumptions
                .get(var)
                .cloned()
                .map(|aspects| (placeholder.clone(), aspects))
        })
        .collect();
    let mut pending: Vec<String> = symbolic_aspects.keys().cloned().collect();
    let mut next = 0;

    while let Some(symbolic_name) = pending.get(next).cloned() {
        next += 1;
        let aspects = symbolic_aspects
            .get(&symbolic_name)
            .cloned()
            .unwrap_or_default();
        for aspect in aspects {
            let Some(assoc_decls) = registry.aspect_assoc_type_decls(&aspect) else {
                continue;
            };
            for assoc_decl in assoc_decls {
                let assoc_aspects: HashSet<String> = assoc_decl
                    .bounds
                    .iter()
                    .filter(|bound| bound.polarity == Polarity::Positive)
                    .filter_map(GenericBound::from_ast)
                    .filter_map(|bound| bound.aspect_name().map(ToOwned::to_owned))
                    .collect();
                if assoc_aspects.is_empty() {
                    continue;
                }
                let projection = format!("{symbolic_name}::{}", assoc_decl.name);
                let entry = symbolic_aspects.entry(projection.clone()).or_default();
                let previous_len = entry.len();
                entry.extend(assoc_aspects);
                if entry.len() != previous_len {
                    pending.push(projection);
                }
            }
        }
    }

    symbolic_aspects
}

fn symbolic_method_ambiguity_reason(
    error: &MetelError,
    generic_env: &GenericMoveEnv,
    registry: &TypeDefinitionRegistry,
) -> Option<String> {
    let MetelError::Internal { message, .. } = error else {
        return None;
    };
    for (symbolic_name, aspects) in &generic_env.symbolic_aspects {
        let prefix = "no method `";
        let suffix = format!("` on `{symbolic_name}`");
        let Some(method) = message
            .strip_prefix(prefix)
            .and_then(|rest| rest.strip_suffix(&suffix))
        else {
            continue;
        };
        let mut candidates: Vec<String> = aspects
            .iter()
            .filter(|aspect| {
                registry
                    .aspect_method_defs(aspect)
                    .is_some_and(|methods| methods.iter().any(|candidate| candidate.name == method))
            })
            .cloned()
            .collect();
        if candidates.len() < 2 {
            continue;
        }
        candidates.sort();
        return Some(format!(
            "ambiguous aspect method `{method}` on symbolic type `{symbolic_name}`; candidates: {}",
            candidates.join(", ")
        ));
    }
    None
}

/// The declared parameter types of a method, excluding the receiver.
///
/// Returns `None` if any parameter cannot be resolved, rather than omitting it (#337).
/// The result is consumed positionally by `observe_call_args` (`params.get(index)` against
/// `args.iter().enumerate()`), so dropping one parameter would judge every later argument
/// against the wrong type — and that judgement is borrow-vs-move. A short list is worse
/// than no list: with `None`, `observe_call_args` recognises no reborrows and consumes
/// every argument, which can only over-report moves, never miss one. A shifted list can do
/// either.
fn infer_method_arg_types(fun_ty: &crate::typeinference::InferType) -> Option<Vec<Type>> {
    match fun_ty {
        crate::typeinference::InferType::Fun(params, ..) => params
            .iter()
            .skip(1)
            .map(infer_to_type)
            .collect::<Option<Vec<_>>>(),
        _ => None,
    }
}

fn substitute_named_generics(
    ty: &InferType,
    named_samples: &HashMap<String, InferType>,
) -> InferType {
    match ty {
        InferType::Named(name, args) if args.is_empty() => named_samples
            .get(name)
            .cloned()
            .unwrap_or_else(|| ty.clone()),
        InferType::Named(name, args) => InferType::Named(
            name.clone(),
            args.iter()
                .map(|arg| substitute_named_generics(arg, named_samples))
                .collect(),
        ),
        InferType::Fun(params, ret, call_mult, use_mult, call_mutation) => InferType::Fun(
            params
                .iter()
                .map(|param| substitute_named_generics(param, named_samples))
                .collect(),
            Box::new(substitute_named_generics(ret, named_samples)),
            *call_mult,
            *use_mult,
            *call_mutation,
        ),
        InferType::Tuple(items) => InferType::Tuple(
            items
                .iter()
                .map(|item| substitute_named_generics(item, named_samples))
                .collect(),
        ),
        InferType::Record(fields) => InferType::Record(
            fields
                .iter()
                .map(|(name, field_ty)| {
                    (
                        name.clone(),
                        substitute_named_generics(field_ty, named_samples),
                    )
                })
                .collect(),
        ),
        InferType::Array(item) => {
            InferType::Array(Box::new(substitute_named_generics(item, named_samples)))
        }
        InferType::SizedArray(item, len) => InferType::SizedArray(
            Box::new(substitute_named_generics(item, named_samples)),
            *len,
        ),
        InferType::Reference(inner) => {
            InferType::Reference(Box::new(substitute_named_generics(inner, named_samples)))
        }
        InferType::MutReference(inner) => {
            InferType::MutReference(Box::new(substitute_named_generics(inner, named_samples)))
        }
        InferType::Residual { brand, fields } => InferType::Residual {
            brand: brand.clone(),
            fields: fields
                .iter()
                .map(|(name, field_ty)| {
                    (
                        name.clone(),
                        substitute_named_generics(field_ty, named_samples),
                    )
                })
                .collect(),
        },
        InferType::Dyn { aspect, type_args } => InferType::Dyn {
            aspect: aspect.clone(),
            type_args: type_args
                .iter()
                .map(|arg| substitute_named_generics(arg, named_samples))
                .collect(),
        },
        InferType::Concrete(_) | InferType::Var(_) | InferType::Never => ty.clone(),
    }
}

fn type_to_infer_under_generic_env(
    ty: &Type,
    placeholders: &HashMap<String, TypeVar>,
) -> InferType {
    match ty {
        Type::Boolean
        | Type::Str
        | Type::Char
        | Type::Unit
        | Type::Never
        | Type::I8
        | Type::I16
        | Type::I32
        | Type::I64
        | Type::U8
        | Type::U16
        | Type::U32
        | Type::U64
        | Type::F32
        | Type::F64 => type_to_infer(ty),
        Type::Tuple(items) => InferType::Tuple(
            items
                .iter()
                .map(|item| type_to_infer_under_generic_env(item, placeholders))
                .collect(),
        ),
        Type::Record(fields) => InferType::Record(
            fields
                .iter()
                .map(|(name, field_ty)| {
                    (
                        name.clone(),
                        type_to_infer_under_generic_env(field_ty, placeholders),
                    )
                })
                .collect(),
        ),
        Type::Array(inner) => InferType::Array(Box::new(type_to_infer_under_generic_env(
            inner,
            placeholders,
        ))),
        Type::SizedArray(inner, len) => InferType::SizedArray(
            Box::new(type_to_infer_under_generic_env(inner, placeholders)),
            *len,
        ),
        Type::Reference(inner) => InferType::Reference(Box::new(type_to_infer_under_generic_env(
            inner,
            placeholders,
        ))),
        Type::MutReference(inner) => InferType::MutReference(Box::new(
            type_to_infer_under_generic_env(inner, placeholders),
        )),
        Type::Fun(params, ret, call_mult, use_mult, call_mutation) => InferType::Fun(
            params
                .iter()
                .map(|param| type_to_infer_under_generic_env(param, placeholders))
                .collect(),
            Box::new(type_to_infer_under_generic_env(ret, placeholders)),
            *call_mult,
            *use_mult,
            *call_mutation,
        ),
        Type::Named(name, args) => {
            if args.is_empty() {
                if let Some(var) = placeholders.get(name) {
                    return InferType::Var(*var);
                }
            }
            InferType::Named(
                name.clone(),
                args.iter()
                    .map(|arg| type_to_infer_under_generic_env(arg, placeholders))
                    .collect(),
            )
        }
        Type::Residual { brand, fields } => InferType::Residual {
            brand: brand.clone(),
            fields: fields
                .iter()
                .map(|(name, field_ty)| {
                    (
                        name.clone(),
                        type_to_infer_under_generic_env(field_ty, placeholders),
                    )
                })
                .collect(),
        },
        Type::Dyn { aspect, type_args } => InferType::Dyn {
            aspect: aspect.clone(),
            type_args: type_args
                .iter()
                .map(|arg| type_to_infer_under_generic_env(arg, placeholders))
                .collect(),
        },
    }
}

/// Convert an `InferType` to a `Type`, or `None` if any part of it is still an unresolved
/// inference variable.
///
/// **All-or-nothing by construction (#337).** Every compound arm collects into
/// `Option<Vec<_>>` rather than filtering, so a failure anywhere inside propagates out as
/// `None`. Filtering would silently change arity — a tuple `(T, i64)` with an unresolved
/// `T` would become the 1-tuple `(i64)`, a record would lose a field, and a `fun`'s
/// parameter list would shift. That last one is not cosmetic: `observe_call_args` pairs a
/// parameter list with arguments *positionally*, and the only thing it decides from a
/// parameter type is borrow-vs-move, so a shifted list silently converts a reborrow into a
/// move or vice versa.
///
/// The two callers handle `None` differently, and neither is harmed by it:
///
/// - `generic_sample_args` propagates it, and the generic-body path records a skip with a
///   reason — this module's convention for "could not analyse".
/// - `infer_method_arg_types` propagates it to `observe_call_args`, which records *no*
///   diagnostic and simply proceeds without reborrow information, consuming each argument.
///   That is more conservative than a shifted list, not less.
fn infer_to_type(ty: &crate::typeinference::InferType) -> Option<Type> {
    use crate::typeinference::InferType;
    match ty {
        InferType::Concrete(inner) => Some(inner.clone()),
        InferType::Never => Some(Type::Never),
        InferType::Tuple(items) => Some(Type::Tuple(
            items
                .iter()
                .map(infer_to_type)
                .collect::<Option<Vec<_>>>()?,
        )),
        InferType::Record(fields) => Some(Type::Record(
            fields
                .iter()
                .map(|(name, ty)| infer_to_type(ty).map(|ty| (name.clone(), ty)))
                .collect::<Option<Vec<_>>>()?,
        )),
        InferType::Array(inner) => infer_to_type(inner).map(|inner| Type::Array(Box::new(inner))),
        InferType::SizedArray(inner, len) => {
            infer_to_type(inner).map(|inner| Type::SizedArray(Box::new(inner), *len))
        }
        InferType::Reference(inner) => {
            infer_to_type(inner).map(|inner| Type::Reference(Box::new(inner)))
        }
        InferType::MutReference(inner) => {
            infer_to_type(inner).map(|inner| Type::MutReference(Box::new(inner)))
        }
        InferType::Fun(params, ret, call_mult, use_mult, call_mutation) => Some(Type::Fun(
            params
                .iter()
                .map(infer_to_type)
                .collect::<Option<Vec<_>>>()?,
            Box::new(infer_to_type(ret)?),
            *call_mult,
            *use_mult,
            *call_mutation,
        )),
        InferType::Named(name, args) => Some(Type::Named(
            name.clone(),
            args.iter().map(infer_to_type).collect::<Option<Vec<_>>>()?,
        )),
        InferType::Residual { brand, fields } => Some(Type::Residual {
            brand: brand.clone(),
            fields: fields
                .iter()
                .map(|(name, ty)| infer_to_type(ty).map(|ty| (name.clone(), ty)))
                .collect::<Option<Vec<_>>>()?,
        }),
        InferType::Dyn { aspect, type_args } => Some(Type::Dyn {
            aspect: aspect.clone(),
            type_args: type_args
                .iter()
                .map(infer_to_type)
                .collect::<Option<Vec<_>>>()?,
        }),
        InferType::Var(_) => None,
    }
}

fn is_reborrow(expr: &TypedExpr, param_ty: &Type) -> bool {
    matches!(expr.ty(), Type::MutReference(_)) && matches!(param_ty, Type::MutReference(_))
}

fn peel_type_references(ty: &Type) -> &Type {
    match ty {
        Type::Reference(inner) | Type::MutReference(inner) => peel_type_references(inner),
        _ => ty,
    }
}

/// Mirrors `typechecker::inference::primitive_type_from_name` (`pub(super)`, not
/// reachable from this module) — a `self` receiver's target name needs the same
/// primitive-name resolution an ordinary parameter's type annotation would get, so
/// `extend i64 { fun ...(&self) ... }`'s `self` is correctly typed `&i64`
/// (`Type::I64`) rather than the wrong `Type::Named("i64", [])`, which would dodge
/// `is_copy`'s primitive recognition and produce a false positive.
fn primitive_type_from_name(name: &str) -> Option<Type> {
    let ty = match name {
        "String" => Type::Str,
        "boolean" => Type::Boolean,
        "Char" => Type::Char,
        "i8" => Type::I8,
        "i16" => Type::I16,
        "i32" => Type::I32,
        "i64" => Type::I64,
        "u8" => Type::U8,
        "u16" => Type::U16,
        "u32" => Type::U32,
        "u64" => Type::U64,
        "f32" => Type::F32,
        "f64" => Type::F64,
        _ => return None,
    };
    Some(ty)
}

/// How many layers of `&`/`&var` wrap `ty` — the number of implicit derefs an
/// auto-deref chain still has left to do to reach the non-reference type
/// underneath. Companion to `peel_type_references`, which strips them but
/// throws the count away; `report_move_out_of_reference` needs the count to
/// name the full chain (`(*(*rr))` for `rr: &&B`), not just its first layer.
fn deref_layers(ty: &Type) -> usize {
    match ty {
        Type::Reference(inner) | Type::MutReference(inner) => 1 + deref_layers(inner),
        _ => 0,
    }
}

fn primitive_type_name(ty: &Type) -> Option<String> {
    match ty {
        Type::I8 => Some("i8".to_string()),
        Type::I16 => Some("i16".to_string()),
        Type::I32 => Some("i32".to_string()),
        Type::I64 => Some("i64".to_string()),
        Type::U8 => Some("u8".to_string()),
        Type::U16 => Some("u16".to_string()),
        Type::U32 => Some("u32".to_string()),
        Type::U64 => Some("u64".to_string()),
        Type::F32 => Some("f32".to_string()),
        Type::F64 => Some("f64".to_string()),
        Type::Boolean => Some("boolean".to_string()),
        Type::Char => Some("Char".to_string()),
        Type::Str => Some("String".to_string()),
        _ => None,
    }
}

fn collect_free_roots_from_typed_block(
    block: &TypedBlock,
    initial_locals: &HashSet<String>,
) -> Vec<CapturedRoot> {
    let mut collector = FreeRootCollector {
        scope_stack: vec![initial_locals.clone()],
        captures: Vec::new(),
        seen: HashSet::new(),
    };
    collector.block(block);
    collector.captures
}

#[derive(Debug, Clone)]
struct CapturedRoot {
    name: String,
    ty: Option<Type>,
}

struct FreeRootCollector {
    scope_stack: Vec<HashSet<String>>,
    captures: Vec<CapturedRoot>,
    seen: HashSet<String>,
}

impl FreeRootCollector {
    fn block(&mut self, block: &TypedBlock) {
        self.scope_stack.push(HashSet::new());
        for decl in &block.stmts {
            self.decl(decl);
        }
        if let Some(tail) = &block.tail {
            self.expr(tail);
        }
        self.scope_stack.pop();
    }

    fn decl(&mut self, decl: &TypedDecl) {
        match decl {
            TypedDecl::Let(let_decl) => {
                self.expr(&let_decl.value);
                self.bind(&let_decl.name);
            }
            TypedDecl::Mut(mut_decl) => {
                self.expr(&mut_decl.value);
                self.bind(&mut_decl.name);
            }
            TypedDecl::Fun(fun) => {
                self.bind(&fun.name);
            }
            TypedDecl::Stmt(stmt) => self.stmt(stmt),
            TypedDecl::Impl(_)
            | TypedDecl::Struct(_)
            | TypedDecl::Enum(_)
            | TypedDecl::Aspect(_) => {}
        }
    }

    fn stmt(&mut self, stmt: &TypedStmt) {
        match stmt {
            TypedStmt::Expr(expr) => self.expr(expr),
            TypedStmt::While(while_stmt) => {
                self.expr(&while_stmt.condition);
                self.block(&while_stmt.body);
            }
            TypedStmt::For(for_stmt) => {
                self.scope_stack.push(HashSet::new());
                if let Some(init) = &for_stmt.init {
                    match init {
                        TypedForInit::Let(let_decl) => {
                            self.expr(&let_decl.value);
                            self.bind(&let_decl.name);
                        }
                        TypedForInit::Mut(mut_decl) => {
                            self.expr(&mut_decl.value);
                            self.bind(&mut_decl.name);
                        }
                        TypedForInit::Expr(expr) => self.expr(expr),
                    }
                }
                if let Some(condition) = &for_stmt.condition {
                    self.expr(condition);
                }
                if let Some(step) = &for_stmt.step {
                    self.expr(step);
                }
                self.block(&for_stmt.body);
                self.scope_stack.pop();
            }
            TypedStmt::ForIn(for_in) => {
                self.expr(&for_in.iterable);
                self.scope_stack.push(HashSet::new());
                self.bind(&for_in.binding);
                self.block(&for_in.body);
                self.scope_stack.pop();
            }
        }
    }

    fn expr(&mut self, expr: &TypedExpr) {
        match expr {
            TypedExpr::Ident(name, _, ty, _) => self.capture_if_free(name, ty),
            TypedExpr::Tuple(items, ..) | TypedExpr::Array(items, ..) => {
                for item in items {
                    self.expr(item);
                }
            }
            TypedExpr::RecordLiteral { fields, .. } | TypedExpr::StructLiteral { fields, .. } => {
                for (_, value) in fields {
                    self.expr(value);
                }
            }
            TypedExpr::RepeatArray(value, ..)
            | TypedExpr::UnaryOp(_, value, ..)
            | TypedExpr::Cast { expr: value, .. }
            | TypedExpr::SingletonCoerce { inner: value, .. }
            | TypedExpr::DynCoerce { inner: value, .. }
            | TypedExpr::RefTemp { init: value, .. } => self.expr(value),
            TypedExpr::BinOp(left, _, right, ..) => {
                self.expr(left);
                self.expr(right);
            }
            TypedExpr::Assign { target, value, .. } => {
                self.place(target);
                self.expr(value);
            }
            TypedExpr::Call { callee, args, .. } => {
                self.expr(callee);
                for arg in args {
                    self.expr(arg);
                }
            }
            TypedExpr::MethodCall { receiver, args, .. } => {
                self.expr(receiver);
                for arg in args {
                    self.expr(arg);
                }
            }
            TypedExpr::FieldAccess { object, .. } | TypedExpr::TupleAccess { object, .. } => {
                self.expr(object);
            }
            TypedExpr::Index { object, index, .. } => {
                self.expr(object);
                self.expr(index);
            }
            TypedExpr::Match(m) => {
                self.expr(&m.scrutinee);
                for arm in &m.arms {
                    self.scope_stack.push(HashSet::new());
                    bind_pattern_names(
                        &arm.pattern,
                        self.scope_stack.last_mut().expect("scope exists"),
                    );
                    if let Some(guard) = &arm.guard {
                        self.expr(guard);
                    }
                    self.block(&arm.body);
                    self.scope_stack.pop();
                }
            }
            TypedExpr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                self.expr(condition);
                self.block(then_branch);
                if let Some(else_branch) = else_branch {
                    self.block(else_branch);
                }
            }
            TypedExpr::Loop { body, .. } => self.block(body),
            TypedExpr::Closure { params, body, .. } => {
                self.scope_stack.push(HashSet::new());
                for param in params {
                    self.bind(&param.name);
                }
                self.block(body);
                self.scope_stack.pop();
            }
            TypedExpr::GenericClosure { params, .. } => {
                self.scope_stack.push(HashSet::new());
                for param in params {
                    self.bind(&param.name);
                }
                self.scope_stack.pop();
            }
            TypedExpr::Return(ret) => {
                if let Some(value) = &ret.value {
                    self.expr(value);
                }
            }
            TypedExpr::Break(brk) => {
                if let Some(value) = &brk.value {
                    self.expr(value);
                }
            }
            TypedExpr::Literal(..) | TypedExpr::Path { .. } | TypedExpr::Continue(_) => {}
        }
    }

    fn place(&mut self, place: &TypedPlace) {
        match place {
            TypedPlace::Ident(name, _, _) => self.capture_free_name(name),
            TypedPlace::Deref { object, .. } => self.expr(object),
            TypedPlace::Field { object, .. } | TypedPlace::Tuple { object, .. } => {
                self.place(object);
            }
            TypedPlace::Index { object, index, .. } => {
                self.place(object);
                self.expr(index);
            }
        }
    }

    fn bind(&mut self, name: &str) {
        self.scope_stack
            .last_mut()
            .expect("scope exists")
            .insert(name.to_string());
    }

    fn capture_if_free(&mut self, name: &str, ty: &Type) {
        if self
            .scope_stack
            .iter()
            .rev()
            .any(|scope| scope.contains(name))
        {
            return;
        }
        if self.seen.insert(name.to_string()) {
            self.captures.push(CapturedRoot {
                name: name.to_string(),
                ty: Some(ty.clone()),
            });
        }
    }

    fn capture_free_name(&mut self, name: &str) {
        if self
            .scope_stack
            .iter()
            .rev()
            .any(|scope| scope.contains(name))
        {
            return;
        }
        if self.seen.insert(name.to_string()) {
            self.captures.push(CapturedRoot {
                name: name.to_string(),
                ty: None,
            });
        }
    }
}

fn violation_message(violation: &MoveViolation) -> String {
    match violation.kind {
        MoveViolationKind::UseAfterMove => format!(
            "use of moved value `{}`: `{}` was {}",
            violation.binding,
            format_place(&violation.moved_place),
            moved_at_clause(violation)
        ),
        MoveViolationKind::PartialMoveUsedAsWhole => format!(
            "use of partially moved value `{}`: field or element `{}` was {}",
            violation.binding,
            format_place(&violation.moved_place),
            moved_at_clause(violation)
        ),
        // No trailing location for the outright-banned rules: the offending
        // expression *is* the diagnostic's own span, so citing it again only
        // repeats the location the reader is already looking at.
        MoveViolationKind::PartialMoveOfDropType => format!(
            "cannot partially move value `{}`: `{}` belongs to a `Drop` type",
            violation.binding,
            format_place(&violation.use_place),
        ),
        MoveViolationKind::ArrayElementMove => format!(
            "cannot move from `{}`: array element moves are not allowed",
            format_place(&violation.use_place),
        ),
        MoveViolationKind::BorrowedArrayElementMove => format!(
            "cannot move `{}`: it is borrowed from a `T[]` view",
            format_place(&violation.use_place),
        ),
        MoveViolationKind::MovedMutReferenceWithoutReborrow => format!(
            "use of moved `&var` binding `{}`: `{}` was moved by a non-reborrow use at {}",
            violation.binding,
            violation.binding,
            format_span(&violation.moved_span)
        ),
        MoveViolationKind::MoveOutOfReference => format!(
            "cannot move `{}` out of a reference: a reference only grants access to the \
             value it points at, never ownership of it",
            format_place(&violation.use_place),
        ),
    }
}

/// Where the move happened, phrased from where the reader is standing.
///
/// A loop-carried move is usually its own use — the same expression, one
/// iteration earlier — so naming the location without naming the iteration
/// would point the reader back at the line they are already looking at.
fn moved_at_clause(violation: &MoveViolation) -> String {
    let same_site = violation.use_span == violation.moved_span;
    match (violation.moved_in_previous_iteration, same_site) {
        (true, true) => "moved here on an earlier iteration".to_string(),
        (true, false) => format!(
            "moved at {} on an earlier iteration",
            format_span(&violation.moved_span)
        ),
        (false, _) => format!("moved at {}", format_span(&violation.moved_span)),
    }
}

fn format_place(place: &Place) -> String {
    place.to_string()
}

fn format_span(span: &Span) -> String {
    format!("{}:{}:{}", span.filename, span.line, span.col)
}

fn bind_pattern_names(pattern: &TypedPattern, into: &mut HashSet<String>) {
    match pattern {
        TypedPattern::Binding(name, _, _) => {
            into.insert(name.clone());
        }
        TypedPattern::Tuple(items, _) => {
            for item in items {
                bind_pattern_names(item, into);
            }
        }
        TypedPattern::EnumVariant { fields, .. } | TypedPattern::Struct { fields, .. } => {
            for (field, _id, _local) in fields {
                into.insert(field.clone());
            }
        }
        TypedPattern::Record { fields, .. } => {
            for (field, _local) in fields {
                into.insert(field.clone());
            }
        }
        TypedPattern::Array { elems, rest, .. } => {
            for item in elems {
                bind_pattern_names(item, into);
            }
            if let Some((rest, _)) = rest {
                into.insert(rest.clone());
            }
        }
        TypedPattern::Wildcard(_) | TypedPattern::Literal(_, _) => {}
    }
}

fn root_place_ty_from_expr(expr: &TypedExpr) -> Option<&Type> {
    match expr {
        TypedExpr::Ident(_, _, ty, _) => Some(ty),
        TypedExpr::FieldAccess { object, .. }
        | TypedExpr::TupleAccess { object, .. }
        | TypedExpr::Index { object, .. } => root_place_ty_from_expr(object),
        _ => None,
    }
}

fn dummy_span_from_place(place: &Place) -> Span {
    Span {
        start: 0,
        end: 0,
        filename: format!("<place:{}>", place.root()),
        line: 0,
        col: 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{coherence, module_loader, name_resolver, path_normalizer, typechecker};
    use std::io::Write;
    use std::sync::atomic::{AtomicU64, Ordering};

    fn move_violations_for_source(source: &str) -> Vec<MoveViolation> {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("metel_move_check_{}_{n}.mtl", std::process::id()));
        {
            let mut file = std::fs::File::create(&path).expect("create temp fixture");
            file.write_all(source.as_bytes())
                .expect("write temp fixture");
        }
        let violations = (|| {
            let graph = module_loader::load_root(&path).expect("load temp fixture");
            let names = name_resolver::resolve(&graph).expect("resolve temp fixture");
            let normalized =
                path_normalizer::normalize(graph, &names).expect("normalize temp fixture");
            coherence::check(&normalized, &names).expect("coherence temp fixture");
            let typed =
                typechecker::check_graph(&normalized, &names, &typechecker::CorePrelude::default())
                    .expect("typecheck temp fixture");
            collect_graph_violations(&typed)
                .violations
                .into_iter()
                .filter(|violation| violation.use_span.filename == path.to_string_lossy())
                .collect()
        })();
        let _ = std::fs::remove_file(&path);
        violations
    }

    /// RFC-0137 slice 2: some shapes that `move_check` used to be the only thing
    /// to reject are now caught earlier, by move-triggered row narrowing, as a
    /// plain typecheck error. Assert the frontend rejects `source` with a message
    /// containing `needle`.
    fn assert_typecheck_error_contains(source: &str, needle: &str) {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("metel_narrow_err_{}_{n}.mtl", std::process::id()));
        std::fs::write(&path, source).expect("write temp fixture");
        let result = (|| {
            let graph = module_loader::load_root(&path)?;
            let names = name_resolver::resolve(&graph)?;
            let normalized = path_normalizer::normalize(graph, &names)?;
            coherence::check(&normalized, &names)?;
            typechecker::check_graph(&normalized, &names, &typechecker::CorePrelude::default())
                .map(|_| ())
        })();
        let _ = std::fs::remove_file(&path);
        let err = result.expect_err("expected a typecheck error, got a clean typecheck");
        let msg = err.to_string();
        assert!(
            msg.contains(needle),
            "expected typecheck error to contain {needle:?}, got: {msg}"
        );
    }

    fn assert_has_violation(source: &str, binding: &str) -> Vec<MoveViolation> {
        let violations = move_violations_for_source(source);
        assert!(
            violations
                .iter()
                .any(|violation| violation.binding == binding),
            "expected a move violation for `{binding}`, got {violations:#?}"
        );
        violations
    }

    fn assert_no_violations(source: &str) {
        let violations = move_violations_for_source(source);
        assert!(
            violations.is_empty(),
            "unexpected violations: {violations:#?}"
        );
    }

    fn move_warnings_for_source(source: &str) -> Vec<String> {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "metel_move_check_warning_{}_{n}.mtl",
            std::process::id()
        ));
        {
            let mut file = std::fs::File::create(&path).expect("create temp fixture");
            file.write_all(source.as_bytes())
                .expect("write temp fixture");
        }
        let warnings = (|| {
            let graph = module_loader::load_root(&path).expect("load temp fixture");
            let names = name_resolver::resolve(&graph).expect("resolve temp fixture");
            let normalized =
                path_normalizer::normalize(graph, &names).expect("normalize temp fixture");
            coherence::check(&normalized, &names).expect("coherence temp fixture");
            let typed =
                typechecker::check_graph(&normalized, &names, &typechecker::CorePrelude::default())
                    .expect("typecheck temp fixture");
            check_graph(&typed).expect("move-check temp fixture")
        })();
        let _ = std::fs::remove_file(&path);
        warnings
    }

    #[test]
    fn unchecked_generic_body_is_reported_to_compiler_callers() {
        let warnings = move_warnings_for_source(
            r#"
aspect FirstMarker {
    fun inspect(&self);
}

aspect SecondMarker {
    fun inspect(&self);
}

aspect Container {
    type Item: FirstMarker + SecondMarker;
    fun get(self) -> Item;
}

fun inspect<T: Container>(value: T) {
    let item := value.get();
    item.inspect();
}

fun main() { }
"#,
        );
        assert!(
            warnings.iter().any(|warning| {
                warning.contains("ambiguous aspect method `inspect`")
                    && warning.contains("FirstMarker, SecondMarker")
            }),
            "expected the reconstruction failure reason, got {warnings:#?}"
        );
    }

    #[test]
    fn bounded_generic_mut_receiver_and_argument_are_reborrowed() {
        let warnings = move_warnings_for_source(
            r#"
aspect Blend {
    fun blend(&var self, other: &var Self);
}

fun blend_twice<T: Blend>(value: T, other: T) {
    var value := value;
    var other := other;
    value.blend(&var other);
    value.blend(&var other);
}

fun main() { }
"#,
        );
        assert!(
            warnings.is_empty(),
            "bounded generic method body was not fully checked: {warnings:#?}"
        );
    }

    #[test]
    fn bounded_generic_method_generic_copy_bound_is_checked() {
        let warnings = move_warnings_for_source(
            r#"
aspect GenericSink {
    fun take<U: Copy>(&self, other: U);
}

fun take_copy<T: GenericSink, U: Copy>(value: T, other: U) -> U {
    value.take(other);
    other
}

fun main() { }
"#,
        );
        assert!(
            warnings.is_empty(),
            "bounded method-generic body was not fully checked: {warnings:#?}"
        );
    }

    #[test]
    fn unmet_method_generic_bound_is_reported_unchecked() {
        let warnings = move_warnings_for_source(
            r#"
aspect GenericSink {
    fun take<U: Copy>(&self, other: U);
}

fun take_unbounded<T: GenericSink, U>(value: T, other: U) {
    value.take(other);
}

fun main() { }
"#,
        );
        assert!(
            warnings
                .iter()
                .any(|warning| warning.contains("does not implement `Copy`")),
            "expected the reconstruction failure reason, got {warnings:#?}"
        );
    }

    #[test]
    fn assignment_move_then_use_is_reported() {
        assert_has_violation(
            r#"
fun main() {
    let a := "hello";
    let b := a;
    let c := a;
}
"#,
            "a",
        );
    }

    #[test]
    fn argument_move_then_use_is_reported() {
        assert_has_violation(
            r#"
fun take(s: String) { }

fun main() {
    let s := "hello";
    take(s);
    let again := s;
}
"#,
            "s",
        );
    }

    #[test]
    fn return_move_then_use_is_reported() {
        assert_has_violation(
            r#"
fun forward(s: String) -> String {
    return s;
}

fun main() {
    let s := "hello";
    let kept := forward(s);
    let again := s;
}
"#,
            "s",
        );
    }

    #[test]
    fn copy_type_can_be_used_twice() {
        assert_no_violations(
            r#"
fun main() {
    let n := 41;
    let a := n;
    let b := n;
}
"#,
        );
        assert_no_violations(
            r#"
fun main() {
    let n := 5;
    let f := || -> i64 { return n; };
    assert(n == 5);
}
"#,
        );
    }

    #[test]
    fn using_moved_field_again_is_a_typecheck_error() {
        // RFC-0137 slice 2 (metel-core#858): the first `pair.left` narrows `pair`
        // to `Pair.{ right }`, so the second projection of `left` is rejected at
        // typecheck, before `--move-check` ever runs.
        assert_typecheck_error_contains(
            r#"
struct Pair {
    left: String,
    right: i64,
}

fun main() {
    let pair := Pair { left = "a", right = 1 };
    let moved: String := pair.left;
    let again: String := pair.left;
}
"#,
            "left",
        );
    }

    #[test]
    fn sibling_field_stays_accessible_after_partial_move() {
        assert_no_violations(
            r#"
struct Pair {
    left: String,
    right: i64,
}

fun main() {
    let pair := Pair { left = "a", right = 1 };
    let moved: String := pair.left;
    let still_live: i64 := pair.right;
}
"#,
        );
    }

    #[test]
    fn whole_value_use_after_partial_move_is_a_typecheck_error() {
        // RFC-0137 slice 2 (metel-core#858): `pair` narrows to `Pair.{ right }`
        // after `pair.left` moves, so passing it where the whole `Pair` is
        // required is a plain typecheck error, not only a `--move-check` finding.
        assert_typecheck_error_contains(
            r#"
struct Pair {
    left: String,
    right: i64,
}

fun take(pair: Pair) -> i64 {
    pair.right
}

fun main() {
    let pair := Pair { left = "a", right = 1 };
    let moved: String := pair.left;
    let value: i64 := take(pair);
}
"#,
            "partially-moved `Pair`",
        );
    }

    #[test]
    fn partial_move_of_drop_type_is_reported() {
        assert_has_violation(
            r#"
struct Handle {
    name: String,
    fd: i64,
}

extend Handle: Drop {
    fun drop(&var self) { }
}

fun main() {
    let handle := Handle { name = "x", fd = 1 };
    let name := handle.name;
}
"#,
            "handle",
        );
    }

    #[test]
    fn partial_move_of_drop_type_in_match_binding_is_reported() {
        assert_has_violation(
            r#"
struct Handle {
    name: String,
    fd: i64,
}

extend Handle: Drop {
    fun drop(&var self) { }
}

fun main() {
    let handle := Handle { name = "x", fd = 1 };
    let n := match (handle.name) {
        name => name.len(),
    };
}
"#,
            "handle",
        );
    }

    /// A record pattern moves at field granularity, like a struct field access:
    /// the moved field is gone, and the record may no longer be used as a whole.
    ///
    /// The `Drop` variant of this test is deliberately absent rather than
    /// overlooked. An anonymous record can never implement `Drop` (RFC-0116 §3,
    /// enforced in `coherence`: "anonymous records cannot implement `Drop`"), so
    /// a record pattern partially moving a `Drop` value is unrepresentable. An
    /// earlier revision tried to write it by destructuring a *nominal* struct
    /// with a record pattern, which the typechecker rejects outright — the test
    /// was failing on its own fixture, not on the checker.
    #[test]
    fn record_pattern_moves_at_field_granularity() {
        assert_has_violation(
            r#"
fun take(r: { n: i64, name: String }) -> i64 {
    return r.n;
}

fun main() {
    let r := { name = "x", n = 1 };
    let moved := match (r) {
        { name, n } => name,
    };
    let again := take(r);
}
"#,
            "r",
        );
    }

    #[test]
    fn tuple_pattern_partial_move_of_drop_prefix_is_reported() {
        assert_has_violation(
            r#"
struct Wrapper {
    pair: (String, i64),
}

extend Wrapper: Drop {
    fun drop(&var self) { }
}

fun main() {
    let wrapper := Wrapper { pair = ("x", 1) };
    let n := match (wrapper.pair) {
        (name, _) => name.len(),
    };
}
"#,
            "wrapper",
        );
    }

    #[test]
    fn enum_payload_pattern_partial_move_of_drop_prefix_is_reported() {
        assert_has_violation(
            r#"
enum MaybeText {
    Empty,
    Full { text: String },
}

struct Wrapper {
    payload: MaybeText,
}

extend Wrapper: Drop {
    fun drop(&var self) { }
}

fun main() {
    let wrapper := Wrapper {
        payload = MaybeText::Full { text = "x" },
    };
    let n := match (wrapper.payload) {
        MaybeText::Full { text } => text.len(),
        MaybeText::Empty => 0,
    };
}
"#,
            "wrapper",
        );
    }

    #[test]
    fn nested_direct_partial_move_of_drop_prefix_is_reported() {
        assert_has_violation(
            r#"
struct Wrapper {
    pair: (String, i64),
}

extend Wrapper: Drop {
    fun drop(&var self) { }
}

fun main() {
    let wrapper := Wrapper { pair = ("x", 1) };
    let name := wrapper.pair.0;
}
"#,
            "wrapper",
        );
    }

    #[test]
    fn tuple_element_partial_move_then_reuse_is_reported() {
        assert_has_violation(
            r#"
fun main() {
    let pair := ("x", 1);
    let left := pair.0;
    let again := pair.0;
}
"#,
            "pair",
        );
    }

    #[test]
    fn enum_payload_move_consumes_whole_value() {
        assert_has_violation(
            r#"
enum MaybeText {
    Empty,
    Full { text: String },
}

fun main() {
    let value := MaybeText::Full { text = "x" };
    let n := match (value) {
        MaybeText::Full { text } => text.len(),
        MaybeText::Empty => 0,
    };
    let again := value;
}
"#,
            "value",
        );
    }

    #[test]
    fn array_element_move_is_reported() {
        assert_has_violation(
            r#"
fun main() {
    let xs := ["x"];
    let first := xs[0];
}
"#,
            "xs",
        );
    }

    #[test]
    fn array_element_move_in_match_binding_is_reported() {
        assert_has_violation(
            r#"
fun main() {
    let xs := ["x"];
    let n := match (xs[0]) {
        s => s.len(),
    };
}
"#,
            "xs",
        );
    }

    #[test]
    fn array_pattern_binding_array_element_is_reported() {
        assert_has_violation(
            r#"
fun main() {
    let xs: [String; 1] := ["x"];
    let n := match (xs) {
        [s] => s.len(),
    };
}
"#,
            "xs",
        );
    }

    #[test]
    fn closure_capture_then_use_is_reported() {
        let violations = assert_has_violation(
            r#"
fun main() {
    let s := "hello";
    let f := [s] once || -> String { s };
    let again := s;
}
"#,
            "s",
        );
        assert_eq!(violations[0].moved_type, "String");
    }

    #[test]
    fn move_in_one_if_arm_persists_after_join() {
        assert_has_violation(
            r#"
fun main() {
    let s := "hello";
    if (true) {
        let moved := s;
    } else {
        let keep := 0;
    }
    let again := s;
}
"#,
            "s",
        );
    }

    #[test]
    fn move_in_loop_body_persists_after_loop() {
        assert_has_violation(
            r#"
fun main() {
    let s := "hello";
    loop {
        let moved := s;
        break;
    }
    let again := s;
}
"#,
            "s",
        );
    }

    #[test]
    fn mut_ref_argument_reborrows_cleanly() {
        assert_no_violations(
            r#"
struct Counter { value: i64 }

fun bump(r: &var Counter) { }

fun main() {
    var c := Counter { value = 0 };
    let r := &var c;
    bump(r);
    bump(r);
}
"#,
        );
    }

    #[test]
    fn plain_binding_of_mut_ref_then_use_is_reported() {
        assert_has_violation(
            r#"
struct Counter { value: i64 }

fun bump(r: &var Counter) { }

fun main() {
    var c := Counter { value = 0 };
    let r := &var c;
    let q := r;
    bump(r);
}
"#,
            "r",
        );
    }

    #[test]
    fn move_site_is_not_reported_as_its_own_use() {
        let violations = move_violations_for_source(
            r#"
struct Pair {
    left: String,
    right: i64,
}

fun main() {
    let pair := Pair { left = "a", right = 1 };
    let moved := pair.left;
}
"#,
        );
        assert!(
            violations.is_empty(),
            "the move site must not accuse itself: {violations:#?}"
        );
    }

    #[test]
    fn moving_projection_does_not_report_base_as_only_use() {
        let violations = move_violations_for_source(
            r#"
struct Pair {
    left: String,
    right: i64,
}

fun main() {
    let pair := Pair { left = "a", right = 1 };
    let moved := pair.left;
    let sibling := pair.right;
}
"#,
        );
        assert!(
            violations.is_empty(),
            "moving `pair.left` must not report `pair` as used-after-move: {violations:#?}"
        );
    }

    /// A tuple literal takes ownership of its elements. Regression for a false
    /// negative where they were only *observed*: the element stayed usable
    /// afterwards, and every rule `consume_place` enforces was skipped.
    #[test]
    fn tuple_literal_consumes_its_elements() {
        assert_has_violation(
            r#"
struct Owned {
    s: String,
}

fun main() {
    let a := Owned { s = "x" };
    let t := (a, 1);
    let n := a.s.len();
}
"#,
            "a",
        );
    }

    #[test]
    fn tuple_literal_cannot_partially_move_a_drop_type() {
        assert_has_violation(
            r#"
struct Handle {
    name: String,
    fd: i64,
}

extend Handle: Drop {
    fun drop(&var self) { }
}

fun main() {
    let h := Handle { name = "x", fd = 1 };
    let t := (h.name, 1);
}
"#,
            "h",
        );
    }

    #[test]
    fn array_literal_cannot_move_an_array_element() {
        assert_has_violation(
            r#"
fun main() {
    let xs := ["a"];
    let ys := [xs[0]];
}
"#,
            "xs",
        );
    }

    #[test]
    fn borrowed_array_for_in_cannot_move_a_noncopy_element() {
        assert_has_violation(
            r#"
fun first<T>(items: T[]) -> T {
    for (item in items) {
        return item;
    }
    panic("empty")
}

fun main() { }
"#,
            "item",
        );
    }

    #[test]
    fn borrowed_array_for_in_allows_copy_elements() {
        assert_no_violations(
            r#"
fun first<T: Copy>(items: T[]) -> T {
    for (item in items) {
        return item;
    }
    panic("empty")
}

fun main() {
    let values: i64[] := [1, 2, 3];
    assert(first(values) == 1);
}
"#,
        );
    }

    #[test]
    fn function_values_are_copy() {
        assert_no_violations(
            r#"
fun increment(value: i64) -> i64 { value + 1 }

fun apply(f: |i64| -> i64) -> i64 { f(1) }

fun main() {
    let f := increment;
    assert(apply(f) == 2);
    assert(apply(f) == 2);
}
"#,
        );
    }

    // --- #337: type conversion must preserve arity or fail outright ---------------------
    //
    // These exercise the conversion helpers directly. The misalignment they guard against
    // needs an unresolved `InferType::Var` to survive into a parameter list, which the
    // reconstruction path does not currently produce from source -- it abandons a body
    // wholesale instead. So there is no `.mtl` fixture that would fail without the fix;
    // asserting on the helpers is what actually pins the invariant.

    use crate::typeinference::{InferType, TypeVar};

    fn var() -> InferType {
        InferType::Var(TypeVar(0))
    }

    fn concrete() -> InferType {
        InferType::Concrete(Type::I64)
    }

    #[test]
    fn tuple_with_an_unresolved_element_converts_to_none_not_a_shorter_tuple() {
        let ty = InferType::Tuple(vec![var(), concrete()]);
        assert_eq!(infer_to_type(&ty), None);
    }

    #[test]
    fn record_with_an_unresolved_field_converts_to_none_not_a_smaller_record() {
        let ty = InferType::Record(vec![
            ("a".to_string(), var()),
            ("b".to_string(), concrete()),
        ]);
        assert_eq!(infer_to_type(&ty), None);
    }

    #[test]
    fn fun_with_an_unresolved_param_converts_to_none_not_a_shorter_signature() {
        let ty = InferType::fun(vec![var(), concrete()], concrete());
        assert_eq!(infer_to_type(&ty), None);
    }

    #[test]
    fn named_with_an_unresolved_argument_converts_to_none_not_fewer_arguments() {
        let ty = InferType::Named("Holder".to_string(), vec![var(), concrete()]);
        assert_eq!(infer_to_type(&ty), None);
    }

    #[test]
    fn fully_resolved_compounds_still_convert_and_keep_their_arity() {
        let tuple = InferType::Tuple(vec![concrete(), concrete(), concrete()]);
        assert_eq!(
            infer_to_type(&tuple),
            Some(Type::Tuple(vec![Type::I64, Type::I64, Type::I64]))
        );

        let fun = InferType::fun(vec![concrete(), concrete()], concrete());
        assert_eq!(
            infer_to_type(&fun),
            Some(Type::Fun(
                vec![Type::I64, Type::I64],
                Box::new(Type::I64),
                crate::types::CallMultiplicity::Many,
                crate::types::UseMultiplicity::Copy,
                crate::types::CallMutation::Reading,
            ))
        );
    }

    #[test]
    fn method_arg_types_are_none_when_a_parameter_is_unresolved() {
        // Receiver plus three parameters, the middle one unresolved. A filtered list would
        // be `[i64, i64]`, and `observe_call_args` -- which indexes positionally -- would
        // then judge the third argument against the second parameter's type. That decides
        // borrow-vs-move, so the shift silently turns a reborrow into a move or back.
        let fun_ty = InferType::fun(vec![concrete(), concrete(), var(), concrete()], concrete());
        assert_eq!(infer_method_arg_types(&fun_ty), None);
    }

    #[test]
    fn method_arg_types_skip_the_receiver_and_keep_the_rest_in_order() {
        let fun_ty = InferType::fun(
            vec![
                InferType::Concrete(Type::Boolean),
                InferType::Concrete(Type::I64),
                InferType::Concrete(Type::MutReference(Box::new(Type::I64))),
            ],
            concrete(),
        );
        assert_eq!(
            infer_method_arg_types(&fun_ty),
            Some(vec![Type::I64, Type::MutReference(Box::new(Type::I64))])
        );
    }

    // ── Loop-carried moves (#291) ────────────────────────────────────────────
    //
    // A loop body is walked more than once while its entry state grows. These
    // pin the two things that are easy to get wrong about that: what reaches the
    // next iteration, and that walking twice does not report twice.

    #[test]
    fn a_loop_carried_move_is_reported_once_not_once_per_pass() {
        let violations = assert_has_violation(
            r#"
fun main() {
    let s := "hello";
    var i := 0;
    loop {
        i += 1;
        let moved := s;
        if (i == 2) { break; }
    }
}
"#,
            "s",
        );
        assert_eq!(
            violations.len(),
            1,
            "the body is walked once per widening pass; only the last may report"
        );
        assert!(violations[0].moved_in_previous_iteration);
    }

    #[test]
    fn nested_loops_report_a_carried_move_once_each_not_once_per_outer_pass() {
        let violations = assert_has_violation(
            r#"
fun main() {
    let s := "hello";
    var i := 0;
    while (i < 3) {
        i += 1;
        var j := 0;
        while (j < 2) {
            j += 1;
            let moved := s;
        }
    }
}
"#,
            "s",
        );
        assert_eq!(violations.len(), 1, "got {violations:#?}");
    }

    #[test]
    fn a_move_reached_only_by_breaking_out_does_not_reach_the_next_iteration() {
        assert_no_violations(
            r#"
fun main() {
    let s := "hello";
    var i := 0;
    loop {
        i += 1;
        if (i == 2) {
            let moved := s;
            break;
        }
    }
}
"#,
        );
    }

    #[test]
    fn a_move_reached_only_by_returning_does_not_reach_the_next_iteration() {
        assert_no_violations(
            r#"
fun main() {
    let s := "hello";
    var i := 0;
    loop {
        i += 1;
        if (i == 2) {
            let moved := s;
            return;
        }
    }
}
"#,
        );
    }

    #[test]
    fn a_move_before_continue_reaches_the_next_iteration() {
        let violations = assert_has_violation(
            r#"
fun main() {
    let s := "hello";
    var i := 0;
    loop {
        i += 1;
        let moved := s;
        if (i < 3) { continue; }
        break;
    }
}
"#,
            "s",
        );
        assert!(violations[0].moved_in_previous_iteration);
    }

    #[test]
    fn a_move_that_breaks_out_is_still_visible_after_the_loop() {
        assert_has_violation(
            r#"
fun main() {
    let s := "hello";
    var i := 0;
    loop {
        i += 1;
        if (i == 2) {
            let moved := s;
            break;
        }
    }
    let again := s;
}
"#,
            "s",
        );
    }

    #[test]
    fn a_binding_declared_inside_the_body_is_fresh_each_iteration() {
        assert_no_violations(
            r#"
fun main() {
    var i := 0;
    while (i < 3) {
        i += 1;
        let local := "fresh";
        let moved := local;
    }
}
"#,
        );
    }

    #[test]
    fn a_move_on_a_returning_branch_does_not_reach_the_code_after_the_if() {
        // The `return` leaves the function, so the move never happened on the
        // path that reaches `again`.
        assert_no_violations(
            r#"
fun main() {
    let s := "hello";
    if (true) {
        let moved := s;
        return;
    }
    let again := s;
}
"#,
        );
    }

    #[test]
    fn a_move_on_a_branch_that_falls_through_still_reaches_the_code_after_the_if() {
        assert_has_violation(
            r#"
fun main() {
    let s := "hello";
    if (true) {
        let moved := s;
    }
    let again := s;
}
"#,
            "s",
        );
    }

    // ── Writing to a moved place reinitializes it ────────────────────────────
    //
    // A write does not read its target. These matter most inside a loop, where
    // move-then-replace is the idiomatic body, but the rule is not loop-specific.

    #[test]
    fn reassigning_a_moved_binding_makes_it_valid_again() {
        assert_no_violations(
            r#"
fun main() {
    var s := "hello";
    let moved := s;
    s := "again";
    let ok := s;
}
"#,
        );
    }

    #[test]
    fn reassigning_a_moved_binding_inside_a_loop_is_not_loop_carried() {
        assert_no_violations(
            r#"
fun main() {
    var s := "hello";
    var i := 0;
    loop {
        i += 1;
        let moved := s;
        s := "again";
        if (i == 3) { break; }
    }
}
"#,
        );
    }

    #[test]
    fn reassigning_a_moved_field_makes_the_whole_value_usable_again() {
        assert_no_violations(
            r#"
struct Pair { left: String, right: String }

fun main() {
    var p := Pair { left = "a", right = "b" };
    let taken := p.left;
    p.left := "c";
    let whole := p;
}
"#,
        );
    }

    #[test]
    fn assigning_a_field_does_not_revive_a_wholly_moved_value() {
        // The write needs a base it can reach, and `p` is gone.
        assert_has_violation(
            r#"
struct Pair { left: String, right: String }

fun main() {
    var p := Pair { left = "a", right = "b" };
    let whole := p;
    p.left := "c";
}
"#,
            "p",
        );
    }

    #[test]
    fn assigning_one_field_leaves_a_sibling_field_moved() {
        // RFC-0137 (metel-core#858/#950): reassigning `left` does not clear the
        // `right` move, so `p` stays narrowed to `Pair.{ left }`. Binding it at
        // its narrowed type (`let whole := p;`) is fine; using it where the whole
        // `Pair` is required is the error — caught at type-check time now.
        assert_typecheck_error_contains(
            r#"
struct Pair { left: String, right: String }

fun take_whole(p: Pair) -> i64 { 0 }

fun main() {
    var p := Pair { left = "a", right = "b" };
    let taken := p.right;
    p.left := "c";
    let n := take_whole(p);
}
"#,
            "partially-moved `Pair`",
        );
    }

    #[test]
    fn a_loop_with_no_reachable_break_diverges() {
        // The inner `loop` always returns, so the outer loop's back edge is
        // never taken and its body's move happens at most once.
        assert_no_violations(
            r#"
fun main() {
    let s := "hello";
    var i := 0;
    while (i < 3) {
        i += 1;
        let moved := s;
        loop { return; }
    }
}
"#,
        );
    }

    #[test]
    fn an_inner_loop_that_can_break_leaves_the_outer_back_edge_live() {
        assert_has_violation(
            r#"
fun main() {
    let s := "hello";
    var i := 0;
    while (i < 3) {
        i += 1;
        let moved := s;
        loop { break; }
    }
}
"#,
            "s",
        );
    }

    // ── Shadowing (#343) ─────────────────────────────────────────────────────
    //
    // Binding a name clears its moved state, which is right for the new binding
    // and must not destroy the one it shadows. The delicate part is that a
    // `break` or `continue` records its state *before* the shadow's scope is
    // popped, so the recorded state has to be unwound first.

    #[test]
    fn a_shadow_does_not_launder_a_loop_carried_move() {
        assert_has_violation(
            r#"
fun main() {
    let s := "original";
    var i := 0;
    loop {
        i += 1;
        let moved := s;
        let s := "replacement";
        if (i == 2) { break; }
    }
}
"#,
            "s",
        );
    }

    #[test]
    fn a_shadow_does_not_launder_a_move_carried_out_through_break() {
        assert_has_violation(
            r#"
fun main() {
    let s := "original";
    loop {
        let moved := s;
        let s := "replacement";
        break;
    }
    let again := s;
}
"#,
            "s",
        );
    }

    #[test]
    fn a_move_of_a_shadow_does_not_escape_its_scope_through_break() {
        // The inverse error: unwinding must not carry the *shadow's* move out
        // and pin it on the outer binding, which was never moved.
        assert_no_violations(
            r#"
fun main() {
    let s := "original";
    var i := 0;
    loop {
        i += 1;
        let s := "shadow";
        let moved := s;
        if (i == 2) { break; }
    }
    let outer := s;
}
"#,
        );
    }

    #[test]
    fn rebinding_the_same_name_twice_in_one_scope_restores_the_outermost() {
        // `pop_scope` unwinds in reverse; forwards would leave the second
        // shadow's empty state instead of what the scope was entered with.
        assert_has_violation(
            r#"
fun main() {
    let s := "original";
    var i := 0;
    loop {
        i += 1;
        let moved := s;
        let s := "first";
        let s := "second";
        if (i == 2) { break; }
    }
}
"#,
            "s",
        );
    }

    #[test]
    fn a_repeated_move_through_a_dereference_is_a_violation() {
        let violations = assert_has_violation(
            r#"
fun eat(s: String) -> i64 { 1 }

fun main() {
    let s := "hello";
    let p := &s;
    let first := eat(*p);
    let second := eat(*p);
}
"#,
            "p",
        );
        assert_eq!(format_place(&violations[0].moved_place), "(*p)");
    }

    // ── By-value receivers through a reference (#348) ───────────────────────
    //
    // `&T` and `&var T` are both `Copy` at the reference-place level, so
    // consuming the receiver *place* records nothing — the checker has to
    // recognise a by-value `self` method reached through a reference and
    // reject it directly, not by tracking a move of the place that never
    // happens. Rejected at the first call, not the second.

    #[test]
    fn a_by_value_method_through_a_shared_reference_is_rejected_at_the_first_call() {
        let violations = assert_has_violation(
            r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }

fun main() {
    let b := B { v = "owned" };
    let r := &b;
    let first := r.eat();
}
"#,
            "r",
        );
        assert_eq!(violations.len(), 1);
        assert_eq!(format_place(&violations[0].moved_place), "(*r)");
    }

    #[test]
    fn a_by_value_method_through_an_explicit_deref_is_rejected_identically() {
        // Auto-deref (`r.eat()`) and an explicit `*` (`(*r).eat()`) dispatch to
        // the same method and must be rejected the same way — checking only
        // the receiver's static type would miss this spelling, since the
        // deref has already happened by the time `self.ty()` is read.
        let violations = assert_has_violation(
            r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }

fun main() {
    let b := B { v = "owned" };
    let r := &b;
    let first := (*r).eat();
}
"#,
            "r",
        );
        assert_eq!(format_place(&violations[0].moved_place), "(*r)");
    }

    #[test]
    fn a_by_value_method_through_a_mut_reference_is_rejected_at_the_first_call() {
        // `&var T` is not `Copy`, so before this fix the second call was
        // rejected as reuse of the moved *reference* — the wrong reason. The
        // first call must be rejected now, for the actual reason.
        let violations = assert_has_violation(
            r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }

fun main() {
    var b := B { v = "owned" };
    let r := &var b;
    let first := r.eat();
}
"#,
            "r",
        );
        assert_eq!(violations[0].kind, MoveViolationKind::MoveOutOfReference);
    }

    #[test]
    fn a_by_value_method_through_a_generic_bound_reference_is_rejected() {
        // Concrete and generic dispatch resolve through the same
        // `consume_method_receiver`, so there is no second copy of this rule
        // that could disagree with the concrete case above.
        assert_has_violation(
            r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }

fun twice<T: Consume>(x: &T) -> String {
    let a := x.eat();
    return x.eat();
}

fun main() {
    let b := B { v = "owned" };
    let result := twice(&b);
}
"#,
            "x",
        );
    }

    #[test]
    fn a_by_value_method_through_a_non_ident_receiver_is_rejected() {
        // The receiver is `pair.0`, not an identifier — the same shape #347
        // found unguarded for `&var self`. The check is keyed on the
        // receiver's type and place, not on `Expr::Ident`.
        let violations = assert_has_violation(
            r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }

fun consume_sneak<T: Consume>(pair: (&T, i64)) -> String {
    return pair.0.eat();
}

fun main() {
    let b := B { v = "owned" };
    let result := consume_sneak((&b, 1));
}
"#,
            "pair",
        );
        assert_eq!(format_place(&violations[0].moved_place), "(*pair.0)");
    }

    #[test]
    fn an_owned_by_value_receiver_is_still_an_ordinary_move() {
        // The rule is about a reference in the way, not about by-value
        // receivers in general.
        assert_has_violation(
            r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }

fun main() {
    let b := B { v = "owned" };
    let out := b.eat();
    let again := b.v;
}
"#,
            "b",
        );
    }

    #[test]
    fn ref_and_mut_ref_methods_through_a_reference_are_unaffected() {
        assert_no_violations(
            r#"
aspect Show { fun show(&self) -> String; }
aspect Bump { fun bump(&var self); }
struct B { v: String }
extend B: Show { fun show(&self) -> String { return self.v.clone(); } }
struct C { v: i64 }
extend C: Bump { fun bump(&var self) { self.v := self.v + 1; } }

fun main() {
    let b := B { v = "x" };
    let r := &b;
    let a := r.show();
    let c := r.show();

    var cc := C { v = 0 };
    let rc := &var cc;
    rc.bump();
    rc.bump();
}
"#,
        );
    }

    #[test]
    fn a_by_value_method_through_a_reference_is_allowed_when_the_pointee_is_copy() {
        // `illegal_move_kind` (the pre-existing "outright ban" mechanism this
        // check reuses via `report_illegal_move`) already gates every one of
        // its bans on `is_copy` first — a Copy value can always be read back
        // out. `receiver_place_is_behind_a_reference` must not skip that same
        // gate, or a Copy struct's by-value method becomes uncallable through
        // a reference at all, which RFC-0067a SS3a explicitly allows ("only
        // copied, and only when the referent's type actually permits
        // copying"). Called twice through the same reference to confirm
        // nothing is consumed either.
        assert_no_violations(
            r#"
struct Pair { a: i64, b: i64 }
extend Pair: Copy;
extend Pair { fun sum(self) -> i64 { self.a + self.b } }

fun main() {
    let p := Pair { a = 1, b = 2 };
    let r := &p;
    let first := r.sum();
    let second := r.sum();
}
"#,
        );
    }

    #[test]
    fn a_by_value_method_on_a_non_place_reference_receiver_is_rejected() {
        // A call result, `if`, `match`, or cast has no nameable `Place` at
        // all, so `receiver_place_is_behind_a_reference`'s second signal
        // (a `Deref` projection) can never fire for it — only the first
        // signal (the receiver's own static type) can. An earlier version of
        // `report_move_out_of_reference` returned early when `place_from_expr`
        // gave `None`, silently accepting this; found by adversarial review.
        let violations = assert_has_violation(
            r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }

fun get_ref(x: &B) -> &B { return x; }

fun main() {
    let b := B { v = "owned" };
    let out := get_ref(&b).eat();
}
"#,
            "<temporary>",
        );
        assert_eq!(violations.len(), 1);
    }

    #[test]
    fn a_by_value_method_through_a_double_reference_names_every_layer() {
        // `deref_layers` must count every implicit layer from the receiver's
        // own type, not just append one `Deref` unconditionally — otherwise
        // `rr: &&B` reports `(*rr)` (still a reference, not the `B` actually
        // moved) instead of `(*(*rr))`. Found by adversarial review.
        let violations = assert_has_violation(
            r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }

fun main() {
    let b := B { v = "owned" };
    let r := &b;
    let rr := &r;
    let out := rr.eat();
}
"#,
            "rr",
        );
        assert_eq!(violations.len(), 1);
        assert_eq!(format_place(&violations[0].moved_place), "(*(*rr))");
    }

    // ── Moving a value out of a reference at non-receiver positions (#648) ──
    //
    // #602 (above) only ever intercepted a by-value method *receiver*. Every
    // other position a value can be moved from — a `let` initializer, a
    // by-value argument, a plain field read — funnels through the ordinary
    // `consume_place` -> `illegal_move_kind` path instead, which never
    // consulted whether a projection stepped through a reference. These
    // exercise that path directly.

    #[test]
    fn move_out_of_self_field_in_a_ref_self_method_is_rejected() {
        // The motivating repro for #648: `self` in a `&self` method is a
        // reference like any other, but nothing checked it before this fix.
        let violations = assert_has_violation(
            r#"
struct Name { value: String }
struct Item { name: Name, count: i64 }
extend Item {
    fun peek(&self) -> String {
        let v := self.name.value;
        v
    }
}
fun main() {
    let item := Item { name = Name { value = "n" }, count = 1 };
    let _ := item.peek();
}
"#,
            "self",
        );
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].kind, MoveViolationKind::MoveOutOfReference);
        assert_eq!(format_place(&violations[0].moved_place), "self.name.value");
    }

    #[test]
    fn move_out_of_a_field_read_through_a_plain_reference_parameter_is_rejected() {
        // Same rule, no `self` involved — an ordinary `&T` parameter.
        let violations = assert_has_violation(
            r#"
struct Name { value: String }
struct Item { name: Name, count: i64 }
fun peek(item: &Item) -> String {
    let v := item.name.value;
    v
}
fun main() {
    let item := Item { name = Name { value = "n" }, count = 1 };
    let _ := peek(&item);
}
"#,
            "item",
        );
        assert_eq!(violations.len(), 1);
        assert_eq!(format_place(&violations[0].moved_place), "item.name.value");
    }

    #[test]
    fn general_assignment_out_of_an_explicit_deref_is_rejected() {
        // RFC-0071 SS7.1's own named example: `let x: B = *r;`.
        assert_has_violation(
            r#"
struct B { v: String }
fun main() {
    let b := B { v = "x" };
    let r := &b;
    let x: B := *r;
}
"#,
            "r",
        );
    }

    #[test]
    fn by_value_argument_passing_out_of_an_explicit_deref_is_rejected() {
        // RFC-0071 SS7.1's other named example: `f(*r)`.
        assert_has_violation(
            r#"
struct B { v: String }
fun takes(b: B) -> String { b.v }
fun main() {
    let b := B { v = "x" };
    let r := &b;
    let n := takes(*r);
}
"#,
            "r",
        );
    }

    #[test]
    fn by_value_argument_passing_a_field_read_through_a_reference_is_rejected() {
        // The field-read form of the same argument-position gap: `f(r.field)`,
        // no explicit `*` anywhere.
        assert_has_violation(
            r#"
struct Name { value: String }
struct Item { name: Name }
fun takes(v: String) -> i64 { v.len() }
fun main() {
    let item := Item { name = Name { value = "x" } };
    let r := &item;
    let n := takes(r.name.value);
}
"#,
            "r",
        );
    }

    #[test]
    fn copy_field_read_through_a_reference_is_still_allowed() {
        // The `Copy` gate must survive the new check exactly as it does for
        // #602's receiver case: a `Copy` value can always be read back out.
        assert_no_violations(
            r#"
struct Item { count: i64, name: String }
fun peek(item: &Item) -> i64 {
    let v := item.count;
    v
}
fun main() {
    let item := Item { count = 5, name = "n" };
    let _ := peek(&item);
}
"#,
        );
    }

    #[test]
    fn by_value_method_through_an_interior_reference_field_is_rejected() {
        // A different manifestation of the same gap, reached through
        // `consume_method_receiver`'s own fallback: #602's
        // `receiver_place_is_behind_a_reference` only inspects the
        // *immediate* receiver's own type/place, so it misses a receiver
        // reached via auto-deref through an *interior* reference-typed field
        // (`outer.inner.payload`, where `inner: &Middle`). That fallback
        // still routes through `consume_expr_with_cause` -> `illegal_move_kind`
        // when its own check misses, so this fix closes it as a side effect —
        // this test proves it rather than leaving it as an assumption.
        assert_has_violation(
            r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }
struct Middle { payload: B }
struct Outer { inner: &Middle }
fun main() {
    let b := B { v = "owned" };
    let middle := Middle { payload = b };
    let outer := Outer { inner = &middle };
    let taken := outer.inner.payload.eat();
}
"#,
            "outer",
        );
    }

    #[test]
    fn ref_self_method_that_only_reads_is_still_unaffected() {
        // Reading a Copy field, or calling a &self/&var self method, through
        // self must remain completely unaffected by the corrected self type.
        assert_no_violations(
            r#"
struct Item { count: i64, name: String }
extend Item {
    fun show(&self) -> String {
        return "${self.count}: ${self.name}";
    }
}
fun main() {
    let item := Item { count = 1, name = "n" };
    println(item.show());
}
"#,
        );
    }
}

fn typed_place_span(place: &TypedPlace) -> &Span {
    match place {
        TypedPlace::Ident(_, _, span)
        | TypedPlace::Deref { span, .. }
        | TypedPlace::Field { span, .. }
        | TypedPlace::Tuple { span, .. }
        | TypedPlace::Index { span, .. } => span,
    }
}
