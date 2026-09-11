//! Reference resolution pass (METEL-187 / ADR-0041, step 1).
//!
//! The name resolver interns every *declaration* to a [`SymbolId`]. This pass walks
//! every *reference* (expression `Ident` sites) and classifies it as either:
//!
//! - [`Res::Def`] — a reference to a top-level declaration (a function, `let`/`mut`,
//!   imported item, or glob-visible name), carrying that declaration's stable
//!   [`SymbolId`]; or
//! - [`Res::Local`] — a reference to a true local: a function parameter, a block-local
//!   `let`/`mut`, a closure parameter, a `for`/`for-in` binding, or a match-pattern
//!   binding. Locals stay name-keyed in the lexical environment.
//!
//! Only `Def` references are recorded, in a side table keyed by the reference's
//! [`Span`]; an absent span means `Local` (or unresolved — the typechecker reports
//! genuinely undefined names). The table is consumed later to dispatch top-level
//! callables by `SymbolId` instead of by environment name lookup.
//!
//! This pass runs *inside* [`crate::name_resolver::resolve`], before path
//! normalization. Multi-segment `Expr::Path` references are therefore left untouched
//! here: the path normalizer rewrites them to `Expr::ResolvedPath` carrying their own
//! `symbol_id`, so construction reads their identity directly from the node. Only bare
//! single-segment `Expr::Ident` references need this side table.

use std::collections::{HashMap, HashSet};

use crate::ast::{
    AssignTarget, Block, Decl, Expr, ForInit, FunDecl, MatchArm, Pattern, Span, Stmt,
};
use crate::name_resolver::{resolve_name_provided_by_module, GlobTier, ModuleScope};
use crate::symbols::SymbolId;

/// The classification of a single reference site. See module docs.
///
/// The collected table stores only `Def` references (by span); `Local` is implicit in
/// a span's absence. The explicit `Local` variant documents the ADR-0041 design and is
/// reserved for a future move to carrying `Res` directly on AST nodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub enum Res {
    /// A reference to a top-level declaration with this stable identity.
    Def(SymbolId),
    /// A reference to a true local (parameter, local binding, …); stays name-keyed.
    Local,
}

/// Side table of resolved `Def` references, keyed by the reference site's span.
/// A reference whose span is absent is a `Res::Local` (or genuinely undefined).
pub type ReferenceTable = HashMap<Span, SymbolId>;

/// Inputs the resolver needs about each module, gathered by the name resolver.
pub(crate) struct ResolveInputs<'a> {
    /// Per-module import scope (explicit imports + glob tiers).
    pub scopes: &'a HashMap<Vec<String>, ModuleScope>,
    /// Public names per module — used to resolve glob-imported references.
    pub pub_surface: &'a HashMap<Vec<String>, HashSet<String>>,
    /// All top-level declared names per module — used to resolve same-module references.
    pub declared_names: &'a HashMap<Vec<String>, HashSet<String>>,
    /// Canonical `(module, name)` → `SymbolId` table.
    pub symbols: &'a HashMap<(Vec<String>, String), SymbolId>,
    /// Names declared via more than one `fn` in the same module (overload sets).
    /// `symbols`'s entry for such a name is a leftover single-declaration artifact of
    /// the initial interning pass, not a stable identity for the name as a whole — an
    /// overloaded name's real identity is resolved per call site by argument types
    /// (`typechecker::overload`), not by this reference table. `resolve_name` must not
    /// treat these as an ordinary same-module declaration (ADR-0042).
    pub overloaded_names: &'a HashMap<Vec<String>, HashSet<String>>,
}

/// Walk every module's declarations and collect the `Def` reference table.
pub(crate) fn collect_references(
    modules: &[(Vec<String>, &[Decl])],
    inputs: &ResolveInputs,
) -> ReferenceTable {
    let mut table = ReferenceTable::new();
    for (module_path, decls) in modules {
        let mut walker = Walker {
            module_path,
            inputs,
            locals: Vec::new(),
            table: &mut table,
        };
        for decl in *decls {
            walker.resolve_decl(decl);
        }
    }
    table
}

struct Walker<'a, 'b> {
    module_path: &'a [String],
    inputs: &'a ResolveInputs<'a>,
    /// Lexical stack of true-local names, innermost last.
    locals: Vec<HashSet<String>>,
    table: &'b mut ReferenceTable,
}

impl Walker<'_, '_> {
    fn push_scope(&mut self) {
        self.locals.push(HashSet::new());
    }
    fn pop_scope(&mut self) {
        self.locals.pop();
    }
    fn bind_local(&mut self, name: &str) {
        if let Some(scope) = self.locals.last_mut() {
            scope.insert(name.to_string());
        }
    }
    fn is_local(&self, name: &str) -> bool {
        self.locals.iter().any(|s| s.contains(name))
    }

    /// Resolve a bare name reference to a top-level `SymbolId`, if any.
    ///
    /// Precedence: a local shadows everything (handled by the caller); otherwise a
    /// declaration in the current module wins, then an explicit import, then a
    /// glob-visible name (user globs before `std::core`).
    fn resolve_name(&self, name: &str) -> Option<SymbolId> {
        // Same-module top-level declaration — but not an overloaded one (ADR-0042):
        // there's no single unambiguous declaration to point at until argument types
        // are known, so this falls through to imports/globs below instead, the same
        // as a name this module doesn't declare at all.
        let is_overloaded = self
            .inputs
            .overloaded_names
            .get(self.module_path)
            .is_some_and(|names| names.contains(name));
        if !is_overloaded
            && self
                .inputs
                .declared_names
                .get(self.module_path)
                .is_some_and(|names| names.contains(name))
        {
            if let Some(id) = self
                .inputs
                .symbols
                .get(&(self.module_path.to_vec(), name.to_string()))
            {
                return Some(*id);
            }
        }

        let scope = self.inputs.scopes.get(self.module_path)?;

        // Explicit import binding.
        if let Some(binding) = scope.explicit.get(name) {
            return Some(binding.symbol_id);
        }

        // Glob imports — user globs win over the std auto-glob (ADR-0026 tiers),
        // regardless of push order, so resolve a `User`-tier hit eagerly and only
        // fall back to a `Std`-tier hit if no user glob provides the name.
        let mut std_hit = None;
        for (tier, glob_module) in &scope.globs {
            let provides = self
                .inputs
                .pub_surface
                .get(glob_module)
                .is_some_and(|names| names.contains(name));
            if !provides {
                continue;
            }
            if let Some(id) = resolve_name_provided_by_module(
                glob_module,
                name,
                self.inputs.symbols,
                self.inputs.scopes,
            ) {
                match tier {
                    GlobTier::User => return Some(id),
                    GlobTier::Std => std_hit = std_hit.or(Some(id)),
                }
            }
        }
        std_hit
    }

    fn record_ref(&mut self, name: &str, span: &Span) {
        if self.is_local(name) {
            return;
        }
        if let Some(id) = self.resolve_name(name) {
            self.table.insert(span.clone(), id);
        }
    }

    // ── Declarations ──────────────────────────────────────────────────────────

    fn resolve_decl(&mut self, decl: &Decl) {
        match decl {
            Decl::Let(ld) => self.resolve_expr(&ld.value),
            Decl::Mut(md) => self.resolve_expr(&md.value),
            Decl::Fun(fd) => self.resolve_fun(fd),
            Decl::Impl(ib) => {
                for method in &ib.methods {
                    self.resolve_fun(method);
                }
            }
            Decl::Aspect(ad) => {
                for method in &ad.methods {
                    if let Some(body) = &method.default_body {
                        self.push_scope();
                        for p in &method.params {
                            self.bind_local(&p.name);
                        }
                        self.resolve_block(body);
                        self.pop_scope();
                    }
                }
            }
            Decl::Struct(_) | Decl::Enum(_) => {}
            Decl::TypeAlias(_) => {
                unreachable!("RFC-0160 type aliases are expanded before reference resolution")
            }
            Decl::Stmt(s) => self.resolve_stmt(s),
        }
    }

    fn resolve_fun(&mut self, fun: &FunDecl) {
        self.push_scope();
        for p in &fun.params {
            self.bind_local(&p.name);
        }
        self.resolve_block(&fun.body);
        self.pop_scope();
    }

    // ── Blocks / statements ─────────────────────────────────────────────────────

    fn resolve_block(&mut self, block: &Block) {
        self.push_scope();
        for decl in &block.stmts {
            // A local `let`/`mut` is resolved with the names visible *before* it,
            // then its own name shadows for the rest of the block. Nested `fun`
            // declarations bind their name as a local too.
            match decl {
                Decl::Let(ld) => {
                    self.resolve_expr(&ld.value);
                    self.bind_local(&ld.name);
                }
                Decl::Mut(md) => {
                    self.resolve_expr(&md.value);
                    self.bind_local(&md.name);
                }
                Decl::Fun(fd) => {
                    self.bind_local(&fd.name);
                    self.resolve_fun(fd);
                }
                other => self.resolve_decl(other),
            }
        }
        if let Some(tail) = &block.tail {
            self.resolve_expr(tail);
        }
        self.pop_scope();
    }

    fn resolve_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Expr(e) => self.resolve_expr(e),
            Stmt::While(w) => {
                self.resolve_expr(&w.condition);
                self.resolve_block(&w.body);
            }
            Stmt::For(f) => {
                self.push_scope();
                if let Some(init) = &f.init {
                    match init {
                        ForInit::Expr(e) => self.resolve_expr(e),
                        ForInit::Let(ld) => {
                            self.resolve_expr(&ld.value);
                            self.bind_local(&ld.name);
                        }
                        ForInit::Mut(md) => {
                            self.resolve_expr(&md.value);
                            self.bind_local(&md.name);
                        }
                    }
                }
                if let Some(cond) = &f.condition {
                    self.resolve_expr(cond);
                }
                if let Some(step) = &f.step {
                    self.resolve_expr(step);
                }
                self.resolve_block(&f.body);
                self.pop_scope();
            }
            Stmt::ForIn(fi) => {
                self.resolve_expr(&fi.iterable);
                self.push_scope();
                self.bind_local(&fi.binding);
                self.resolve_block(&fi.body);
                self.pop_scope();
            }
        }
    }

    // ── Expressions ───────────────────────────────────────────────────────────

    fn resolve_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Ident(name, span) => self.record_ref(name, span),
            // Multi-segment paths are handled by the path normalizer (they become
            // `ResolvedPath` carrying their own `symbol_id`); leave them here.
            // `ResolvedPath` does not exist yet at this stage but is matched for safety.
            Expr::Path(..)
            | Expr::ResolvedPath { .. }
            | Expr::Literal(_, _)
            | Expr::RecordProjection { .. }
            | Expr::Continue(_) => {}
            Expr::Tuple(elems, _) | Expr::Array(elems, _) => {
                for e in elems {
                    self.resolve_expr(e);
                }
            }
            Expr::RepeatArray(elem, _, _) => self.resolve_expr(elem),
            Expr::BinOp(lhs, _, rhs, _) => {
                self.resolve_expr(lhs);
                self.resolve_expr(rhs);
            }
            Expr::UnaryOp(_, operand, _) => self.resolve_expr(operand),
            Expr::Cast { expr, .. }
            | Expr::Ascribe { expr, .. }
            | Expr::PropagateError { expr, .. } => self.resolve_expr(expr),
            Expr::Assign { target, value, .. } => {
                self.resolve_assign_target(target);
                self.resolve_expr(value);
            }
            Expr::Call { callee, args, .. } => {
                self.resolve_expr(callee);
                for a in args {
                    self.resolve_expr(a);
                }
            }
            Expr::MethodCall { receiver, args, .. } => {
                self.resolve_expr(receiver);
                for a in args {
                    self.resolve_expr(a);
                }
            }
            Expr::FieldAccess { object, .. } | Expr::TupleAccess { object, .. } => {
                self.resolve_expr(object);
            }
            Expr::Index { object, index, .. } => {
                self.resolve_expr(object);
                self.resolve_expr(index);
            }
            Expr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                self.resolve_expr(condition);
                self.resolve_block(then_branch);
                if let Some(eb) = else_branch {
                    self.resolve_block(eb);
                }
            }
            Expr::Loop { body, .. } => self.resolve_block(body),
            Expr::Closure { params, body, .. } => {
                self.push_scope();
                for p in params {
                    self.bind_local(&p.name);
                }
                self.resolve_block(body);
                self.pop_scope();
            }
            Expr::Match(m) => {
                self.resolve_expr(&m.scrutinee);
                for arm in &m.arms {
                    self.resolve_arm(arm);
                }
            }
            Expr::StructLiteral { fields, .. } | Expr::RecordLiteral { fields, .. } => {
                for (_, v) in fields {
                    self.resolve_expr(v);
                }
            }
            Expr::Return(r) => {
                if let Some(v) = &r.value {
                    self.resolve_expr(v);
                }
            }
            Expr::Break(b) => {
                if let Some(v) = &b.value {
                    self.resolve_expr(v);
                }
            }
        }
    }

    fn resolve_assign_target(&mut self, target: &AssignTarget) {
        match target {
            // A bare assignment target names a place. `record_ref` skips it if it
            // is a local; a top-level `var` target is a reference to a global
            // declaration and needs its `SymbolId` for the resolution freeze
            // (ADR-0054 / metel-core#1052).
            AssignTarget::Ident(name, span) => self.record_ref(name, span),
            AssignTarget::FieldAccess { object, .. }
            | AssignTarget::TupleAccess { object, .. }
            | AssignTarget::Deref { object, .. } => {
                self.resolve_expr(object);
            }
            AssignTarget::Index { object, index, .. } => {
                self.resolve_expr(object);
                self.resolve_expr(index);
            } // RFC-0110: `*p = v` — the operand is an ordinary value expression.
        }
    }

    fn resolve_arm(&mut self, arm: &MatchArm) {
        self.push_scope();
        bind_pattern(&arm.pattern, &mut |name| self.bind_local(name));
        if let Some(guard) = &arm.guard {
            self.resolve_expr(guard);
        }
        self.resolve_block(&arm.body);
        self.pop_scope();
    }
}

/// Invoke `bind` for every binding name introduced by a pattern.
fn bind_pattern(pattern: &Pattern, bind: &mut dyn FnMut(&str)) {
    match pattern {
        Pattern::Wildcard(_) | Pattern::Literal(_, _) => {}
        Pattern::Binding(name, _) => bind(name),
        Pattern::EnumVariant { fields, .. }
        | Pattern::Struct { fields, .. }
        | Pattern::Record { fields, .. } => {
            for f in fields {
                bind(f);
            }
        }
        Pattern::Tuple(elems, _) => {
            for p in elems {
                bind_pattern(p, bind);
            }
        }
        Pattern::Array { elems, rest, .. } => {
            for p in elems {
                bind_pattern(p, bind);
            }
            if let Some((rest, _)) = rest {
                bind(rest);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::module_loader::{LoadedModule, ModuleGraph};
    use crate::name_resolver::resolve;
    use std::collections::HashMap;
    use std::path::PathBuf;

    /// Build a single-module graph (module path `[]`) from one source string.
    fn single_module_graph(source: &str) -> ModuleGraph {
        let program = crate::parser::parse(source, "test.mtl").expect("parse");
        ModuleGraph {
            root: PathBuf::from("test.mtl"),
            modules: vec![LoadedModule {
                module_path: vec![],
                file_path: PathBuf::from("test.mtl"),
                program,
            }],
            path_aliases: HashMap::new(),
        }
    }

    #[test]
    fn resolves_top_level_call_to_its_symbol_id() {
        let graph = single_module_graph(
            "fun helper() -> i64 { 1 }\n\
             fun main() { let x := 1; helper(); }",
        );
        let names = resolve(&graph).unwrap();
        let helper_id = names.symbols[&(vec![], "helper".to_string())];
        // Exactly one bare-Ident reference resolves to a Def: the `helper` call site.
        // The `let x` binding and the `x`/literal sites are locals or non-references.
        let resolved: Vec<_> = names.references.values().copied().collect();
        assert_eq!(
            resolved,
            vec![helper_id],
            "the only resolved reference should be the call to `helper`"
        );
    }

    #[test]
    fn local_binding_shadows_top_level_declaration() {
        let graph = single_module_graph(
            "fun foo() -> i64 { 1 }\n\
             fun main() { let foo := 2; foo; }",
        );
        let names = resolve(&graph).unwrap();
        let foo_id = names.symbols[&(vec![], "foo".to_string())];
        assert!(
            !names.references.values().any(|&id| id == foo_id),
            "a local `foo` must shadow the top-level `foo`, so no reference resolves to it"
        );
    }

    #[test]
    fn overloaded_name_reference_does_not_resolve_to_a_stale_id() {
        // ADR-0042 regression: an overloaded name has no single unambiguous
        // declaration — `symbols[(module, "print")]` is a leftover artifact of the
        // initial interning pass (whichever overload happened to be interned last),
        // never a real identity anything registers a runtime value under. A bare
        // reference to it (here, used as a first-class value, not a call — call
        // sites go through the separate overload-selection path in
        // `typechecker::overload` entirely) must not resolve to that stale id.
        let graph = single_module_graph(
            "fun print(x: i64) {}\n\
             fun print(x: String) {}\n\
             fun main() { let f := print; }",
        );
        let names = resolve(&graph).unwrap();
        let stale_id = names.symbols[&(vec![], "print".to_string())];
        assert!(
            !names.references.values().any(|&id| id == stale_id),
            "a reference to an overloaded name must not resolve to the interning \
             pass's leftover single-declaration id"
        );
    }
}
