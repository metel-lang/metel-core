//! A parse-driven walk that assigns structural identities to the lexical
//! bindings and value references inside a module's function bodies.
//!
//! This is the #1048 slice: it produces the *local* half of a [`ResolutionMap`]
//! — every binding gets a [`LocalId`], every use gets a [`RefId`] and a
//! [`Resolution`] — using only lexical scoping, which needs nothing from the
//! name resolver. A use that binds lexically resolves to [`BindingId::Local`];
//! anything else is left [`UnresolvedCause::NotInScope`] for #1049 to reclassify
//! as a global, a visibility error, or a genuine unbound name once the
//! resolver's module scopes are wired in.
//!
//! Coverage here is deliberately partial (free functions, their nested blocks,
//! nested functions, closures, `let` / `mut`, loop bindings, match-arm
//! patterns). Impl methods, `let` destructuring, captures, and the full pattern
//! grammar are #1049.
//!
//! [`LocalId`]: super::LocalId
//! [`RefId`]: super::RefId

use std::collections::HashMap;

use crate::ast::{
    AssignTarget, Block, CaptureSpec, Decl, Expr, ForInit, MatchArm, Pattern, Span, Stmt,
};
use crate::name_resolver::ResolvedNames;

use super::lexical_path::{LexicalPath, LexicalSeg};
use super::position::{PositionHit, PositionIndex};
use super::{
    structural_hash, BindingId, DefinitionInfo, DefinitionKind, LocalId, NameInterner, RefId,
    Resolution, ResolutionMap, UnresolvedCause, UnresolvedRef,
};

/// The identity artefacts produced for one module: the durable identity-keyed
/// [`ResolutionMap`] and the volatile position lookup rebuilt alongside it.
#[derive(Debug, Clone, Default)]
pub struct Allocation {
    /// Identity-keyed resolved facts. Durable.
    pub resolution: ResolutionMap,
    /// Byte-offset → identity. Rebuilt per snapshot; never a semantic input.
    pub positions: PositionIndex,
}

/// Assign structural identities to every binding and value reference in
/// `decls`, the top-level declarations of the module at `module_path`.
///
/// `names` is consumed read-only, only to map an owning function's spelling to
/// its [`SymbolId`]; no resolution decision is taken from it here.
#[must_use]
pub fn allocate_module(
    module_path: &[String],
    decls: &[Decl],
    names: &ResolvedNames,
    interner: &mut NameInterner,
) -> Allocation {
    let mut out = ResolutionMap::default();
    let mut positions = Vec::new();
    let mut collision = CollisionGuard::default();

    for decl in decls {
        let Decl::Fun(fun) = decl else { continue };
        let key = (module_path.to_vec(), fun.name.clone());
        let Some(&sym) = names.symbols.get(&key) else {
            // A declared free function with no interned symbol should not
            // happen; skip rather than fabricate an owner.
            continue;
        };
        let mut walker = Walker {
            owner: BindingId::Global(sym),
            interner,
            out: &mut out,
            positions: &mut positions,
            collision: &mut collision,
            scopes: vec![Scope::default()],
            path: LexicalPath::root(),
            block_counter: vec![0],
            closure_counter: vec![0],
            use_counter: HashMap::new(),
        };
        for (i, param) in fun.params.iter().enumerate() {
            walker.bind(
                &param.name,
                &param.span,
                DefinitionKind::Param,
                LexicalSeg::Param(u32::try_from(i).unwrap_or(u32::MAX)),
            );
        }
        walker.walk_block(&fun.body);
    }

    Allocation {
        resolution: out,
        positions: PositionIndex::from_entries(positions),
    }
}

/// One lexical scope: spelling → the binding it currently denotes.
#[derive(Default)]
struct Scope {
    names: HashMap<String, LocalId>,
}

struct Walker<'a> {
    owner: BindingId,
    interner: &'a mut NameInterner,
    out: &'a mut ResolutionMap,
    positions: &'a mut Vec<(Span, PositionHit)>,
    collision: &'a mut CollisionGuard,
    scopes: Vec<Scope>,
    /// The structural path to the *current* scope, relative to `owner`.
    path: LexicalPath,
    /// Per-nesting-level counter of blocks entered, so [`LexicalSeg::Block`] is
    /// an ordinal among blocks rather than among all statements.
    block_counter: Vec<u32>,
    closure_counter: Vec<u32>,
    /// `(scope path, name)` → uses seen, for [`LexicalSeg::Use`] disambiguation.
    use_counter: HashMap<(Vec<LexicalSeg>, String), u32>,
}

impl Walker<'_> {
    // ── scope plumbing ──────────────────────────────────────────────────────

    fn enter(&mut self, seg: LexicalSeg) {
        self.path.push(seg);
        self.scopes.push(Scope::default());
        self.block_counter.push(0);
        self.closure_counter.push(0);
    }

    fn leave(&mut self) {
        self.path.pop();
        self.scopes.pop();
        self.block_counter.pop();
        self.closure_counter.pop();
    }

    fn bind(&mut self, name: &str, span: &Span, kind: DefinitionKind, seg: LexicalSeg) {
        let name_id = self.interner.name(name);
        let key_path = self.path.child(seg);
        let raw = structural_hash(self.owner, &key_path);
        let id = LocalId(raw);
        self.collision.check_local(id, self.owner, &key_path);
        self.out.definitions.insert(
            BindingId::Local(id),
            DefinitionInfo {
                kind,
                name: name_id,
                span: span.clone(),
            },
        );
        self.positions
            .push((span.clone(), PositionHit::Definition(BindingId::Local(id))));
        if let Some(scope) = self.scopes.last_mut() {
            scope.names.insert(name.to_string(), id);
        }
    }

    fn lookup(&self, name: &str) -> Option<LocalId> {
        self.scopes
            .iter()
            .rev()
            .find_map(|s| s.names.get(name).copied())
    }

    fn record_use(&mut self, name: &str, span: &Span) {
        let name_id = self.interner.name(name);
        let counter_key = (self.path.0.clone(), name.to_string());
        let occ = self.use_counter.entry(counter_key).or_insert(0);
        let occurrence = *occ;
        *occ += 1;

        let key_path = self.path.child(LexicalSeg::Use {
            name: name.to_string(),
            occurrence,
        });
        let raw = structural_hash(self.owner, &key_path);
        let rid = RefId(raw);
        self.collision.check_ref(rid, self.owner, &key_path);

        let resolution = match self.lookup(name) {
            Some(local) => Resolution::Resolved(BindingId::Local(local)),
            None => Resolution::Unresolved(UnresolvedRef {
                spelling: name_id,
                // #1049 reclassifies: Global | VisibilityDenied | (real) NotInScope.
                cause: UnresolvedCause::NotInScope,
            }),
        };
        self.out.references.insert(rid, resolution);
        self.positions
            .push((span.clone(), PositionHit::Reference(rid)));
    }

    // ── AST walk ────────────────────────────────────────────────────────────

    fn walk_block(&mut self, block: &Block) {
        let n = self.next_block();
        self.enter(LexicalSeg::Block(n));
        for decl in &block.stmts {
            self.walk_decl(decl);
        }
        if let Some(tail) = &block.tail {
            self.walk_expr(tail);
        }
        self.leave();
    }

    fn walk_decl(&mut self, decl: &Decl) {
        match decl {
            Decl::Let(d) => {
                self.walk_expr(&d.value);
                self.bind(
                    &d.name,
                    &d.span,
                    DefinitionKind::Let,
                    LexicalSeg::Let(d.name.clone()),
                );
            }
            Decl::Mut(d) => {
                self.walk_expr(&d.value);
                self.bind(
                    &d.name,
                    &d.span,
                    DefinitionKind::Mut,
                    LexicalSeg::Mut(d.name.clone()),
                );
            }
            Decl::Fun(f) => {
                // A nested function: record it as a binding, then walk its body
                // under a NestedFn step with its own fresh parameter scope.
                self.bind(
                    &f.name,
                    &f.span,
                    DefinitionKind::NestedFn,
                    LexicalSeg::NestedFn(f.name.clone()),
                );
                self.enter(LexicalSeg::NestedFn(f.name.clone()));
                for (i, param) in f.params.iter().enumerate() {
                    self.bind(
                        &param.name,
                        &param.span,
                        DefinitionKind::Param,
                        LexicalSeg::Param(u32::try_from(i).unwrap_or(u32::MAX)),
                    );
                }
                self.walk_block(&f.body);
                self.leave();
            }
            Decl::Stmt(stmt) => self.walk_stmt(stmt),
            // Types, impls, aspects, aliases inside a body are out of scope for
            // #1048's value-binding walk.
            Decl::Struct(_)
            | Decl::Enum(_)
            | Decl::Impl(_)
            | Decl::Aspect(_)
            | Decl::TypeAlias(_) => {}
        }
    }

    fn walk_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Expr(e) => self.walk_expr(e),
            Stmt::While(w) => {
                self.walk_expr(&w.condition);
                self.walk_block(&w.body);
            }
            Stmt::For(f) => {
                let n = self.next_block();
                self.enter(LexicalSeg::Block(n));
                // clippy-allow: ForInit::Let(LetDecl) and ForInit::Mut(MutDecl)
                // wrap distinct types, so the two arms cannot be merged into one
                // or-pattern even though their bodies read the same fields.
                #[allow(clippy::match_same_arms)]
                match &f.init {
                    Some(ForInit::Let(d)) => {
                        self.walk_expr(&d.value);
                        self.bind(
                            &d.name,
                            &d.span,
                            DefinitionKind::LoopBinding,
                            LexicalSeg::LoopBinding(d.name.clone()),
                        );
                    }
                    Some(ForInit::Mut(d)) => {
                        self.walk_expr(&d.value);
                        self.bind(
                            &d.name,
                            &d.span,
                            DefinitionKind::LoopBinding,
                            LexicalSeg::LoopBinding(d.name.clone()),
                        );
                    }
                    Some(ForInit::Expr(e)) => self.walk_expr(e),
                    None => {}
                }
                if let Some(c) = &f.condition {
                    self.walk_expr(c);
                }
                if let Some(s) = &f.step {
                    self.walk_expr(s);
                }
                self.walk_block(&f.body);
                self.leave();
            }
            Stmt::ForIn(f) => {
                self.walk_expr(&f.iterable);
                let n = self.next_block();
                self.enter(LexicalSeg::Block(n));
                self.bind(
                    &f.binding,
                    &f.span,
                    DefinitionKind::LoopBinding,
                    LexicalSeg::LoopBinding(f.binding.clone()),
                );
                self.walk_block(&f.body);
                self.leave();
            }
        }
    }

    fn walk_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Ident(name, span) => self.record_use(name, span),
            // No value references to record:
            // - `Path` / `ResolvedPath`: module-qualified, identity comes from
            //   path normalization and is threaded onto the typed IR by #1050;
            // - `Literal`, `Continue`, `RecordProjection`: no operand names.
            Expr::Path(_, _)
            | Expr::ResolvedPath { .. }
            | Expr::Literal(_, _)
            | Expr::Continue(_)
            | Expr::RecordProjection { .. } => {}
            Expr::Tuple(xs, _) | Expr::Array(xs, _) => {
                for x in xs {
                    self.walk_expr(x);
                }
            }
            Expr::RepeatArray(x, _, _)
            | Expr::UnaryOp(_, x, _)
            | Expr::FieldAccess { object: x, .. }
            | Expr::TupleAccess { object: x, .. }
            | Expr::Cast { expr: x, .. }
            | Expr::Ascribe { expr: x, .. }
            | Expr::PropagateError { expr: x, .. } => self.walk_expr(x),
            Expr::RecordLiteral { fields, .. } | Expr::StructLiteral { fields, .. } => {
                for (_, v) in fields {
                    self.walk_expr(v);
                }
            }
            Expr::BinOp(a, _, b, _) => {
                self.walk_expr(a);
                self.walk_expr(b);
            }
            Expr::Assign { target, value, .. } => {
                self.walk_assign_target(target);
                self.walk_expr(value);
            }
            Expr::Call {
                callee: head, args, ..
            }
            | Expr::MethodCall {
                receiver: head,
                args,
                ..
            } => {
                self.walk_expr(head);
                for a in args {
                    self.walk_expr(a);
                }
            }
            Expr::Index { object, index, .. } => {
                self.walk_expr(object);
                self.walk_expr(index);
            }
            Expr::Closure {
                captures,
                params,
                body,
                ..
            } => self.walk_closure(captures, params, body),
            Expr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                self.walk_expr(condition);
                self.walk_block(then_branch);
                if let Some(b) = else_branch {
                    self.walk_block(b);
                }
            }
            Expr::Match(m) => {
                self.walk_expr(&m.scrutinee);
                for arm in &m.arms {
                    self.walk_match_arm(arm);
                }
            }
            Expr::Loop { body, .. } => self.walk_block(body),
            Expr::Return(r) => self.walk_opt(r.value.as_deref()),
            Expr::Break(b) => self.walk_opt(b.value.as_deref()),
        }
    }

    fn walk_opt(&mut self, expr: Option<&Expr>) {
        if let Some(expr) = expr {
            self.walk_expr(expr);
        }
    }

    fn walk_closure(
        &mut self,
        captures: &[CaptureSpec],
        params: &[crate::ast::Param],
        body: &Block,
    ) {
        // Captures name bindings in the *enclosing* scope: record them as uses
        // before descending into the closure body.
        for cap in captures {
            let (name, span) = capture_name(cap);
            self.record_use(name, span);
        }
        let n = self.closure_counter.last().copied().unwrap_or(0);
        if let Some(c) = self.closure_counter.last_mut() {
            *c += 1;
        }
        self.enter(LexicalSeg::Closure(n));
        for (i, p) in params.iter().enumerate() {
            self.bind(
                &p.name,
                &p.span,
                DefinitionKind::ClosureParam,
                LexicalSeg::ClosureParam(u32::try_from(i).unwrap_or(u32::MAX)),
            );
        }
        self.walk_block(body);
        self.leave();
    }

    fn walk_assign_target(&mut self, target: &AssignTarget) {
        match target {
            AssignTarget::Ident(name, span) => self.record_use(name, span),
            AssignTarget::FieldAccess { object, .. }
            | AssignTarget::TupleAccess { object, .. }
            | AssignTarget::Deref { object, .. } => self.walk_expr(object),
            AssignTarget::Index { object, index, .. } => {
                self.walk_expr(object);
                self.walk_expr(index);
            }
        }
    }

    fn walk_match_arm(&mut self, arm: &MatchArm) {
        let n = self.next_block();
        self.enter(LexicalSeg::Block(n));
        self.bind_pattern(&arm.pattern);
        if let Some(guard) = &arm.guard {
            self.walk_expr(guard);
        }
        self.walk_block(&arm.body);
        self.leave();
    }

    fn bind_pattern(&mut self, pat: &Pattern) {
        match pat {
            Pattern::Binding(name, span) => {
                self.bind(
                    name,
                    span,
                    DefinitionKind::PatternBinding,
                    LexicalSeg::PatternField(name.clone()),
                );
            }
            Pattern::Tuple(elems, _) => {
                for (i, e) in elems.iter().enumerate() {
                    self.path.push(LexicalSeg::PatternElem(
                        u32::try_from(i).unwrap_or(u32::MAX),
                    ));
                    self.bind_pattern(e);
                    self.path.pop();
                }
            }
            Pattern::Struct { fields, .. } | Pattern::Record { fields, .. } => {
                for f in fields {
                    self.bind(
                        f,
                        &Span::new(0, 0, "<pattern>"),
                        DefinitionKind::PatternBinding,
                        LexicalSeg::PatternField(f.clone()),
                    );
                }
            }
            Pattern::Array { elems, rest, .. } => {
                for (i, e) in elems.iter().enumerate() {
                    self.path.push(LexicalSeg::PatternElem(
                        u32::try_from(i).unwrap_or(u32::MAX),
                    ));
                    self.bind_pattern(e);
                    self.path.pop();
                }
                if let Some(name) = rest {
                    self.bind(
                        name,
                        &Span::new(0, 0, "<pattern>"),
                        DefinitionKind::PatternBinding,
                        LexicalSeg::PatternField(name.clone()),
                    );
                }
            }
            Pattern::Wildcard(_) | Pattern::Literal(_, _) | Pattern::EnumVariant { .. } => {}
        }
    }

    fn next_block(&mut self) -> u32 {
        let n = self.block_counter.last().copied().unwrap_or(0);
        if let Some(c) = self.block_counter.last_mut() {
            *c += 1;
        }
        n
    }
}

/// The captured binding's spelling and span, regardless of capture mode
/// (`[x]`, `[&x]`, `[&var x]`, `[x.clone()]` — RFC-0050).
fn capture_name(cap: &CaptureSpec) -> (&str, &Span) {
    match cap {
        CaptureSpec::Owned { name, span }
        | CaptureSpec::SharedRef { name, span }
        | CaptureSpec::MutRef { name, span }
        | CaptureSpec::Clone { name, span } => (name, span),
    }
}

/// Reverse table that turns a genuine structural-hash collision into a loud
/// panic instead of a silently merged identity. Collisions on a 64-bit
/// [`DefaultHasher`] over one module's keys are astronomically unlikely; this
/// exists so that "unlikely" is enforced, not assumed.
#[derive(Default)]
struct CollisionGuard {
    locals: HashMap<u64, (BindingId, LexicalPath)>,
    refs: HashMap<u64, (BindingId, LexicalPath)>,
}

impl CollisionGuard {
    fn check_local(&mut self, id: LocalId, owner: BindingId, path: &LexicalPath) {
        if let Some(prev) = self.locals.get(&id.0) {
            assert!(
                prev == &(owner, path.clone()),
                "LocalId structural-hash collision: {prev:?} vs {:?}",
                (owner, path)
            );
        } else {
            self.locals.insert(id.0, (owner, path.clone()));
        }
    }

    fn check_ref(&mut self, id: RefId, owner: BindingId, path: &LexicalPath) {
        if let Some(prev) = self.refs.get(&id.0) {
            assert!(
                prev == &(owner, path.clone()),
                "RefId structural-hash collision: {prev:?} vs {:?}",
                (owner, path)
            );
        } else {
            self.refs.insert(id.0, (owner, path.clone()));
        }
    }
}
