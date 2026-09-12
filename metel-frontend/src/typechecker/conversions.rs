use crate::ast::{Span, TypeExpr};
use crate::error::{MetelError, TypeErrorCode};
use crate::typeinference::{InferType, Substitution, TypeDefinitionRegistry, TypeVar};
use crate::types::Type;
use std::collections::HashMap;

/// Context for resolving associated-type projections (RFC-0082).
/// Passed through `type_expr_to_infer_in_context` so that `Projection` nodes
/// and bare-name sugar can be resolved against the registry.
pub(super) struct AssocResolveCtx<'a> {
    pub registry: &'a TypeDefinitionRegistry,
    pub current_module: &'a [String],
    /// Set when converting an ASPECT's own method signature (§1.2 bare-name sugar):
    /// the aspect currently being processed, so `Item` alone resolves as `Self::Item`.
    pub current_aspect: Option<&'a str>,
}

/// The stand-in produced when a record projection cannot be resolved to a real row.
///
/// This function is infallible (its callers are), so it cannot report *why* the
/// projection failed — and an earlier version smuggled the reason in here as the type's
/// *name*, which then rendered as "unknown type record projection target ... has no field
/// ..." or, worse, doubled up as "unknown type unknown type Missing". The name is now just
/// the projection's own spelling, so every message that interpolates a type name stays
/// grammatical.
///
/// The precise diagnosis is `projections::check`'s job: it runs once the registry is
/// complete and reports unknown types, unknown fields and non-struct targets directly.
/// This value only has to fail *somewhere* if that pass missed the position.
fn unresolved_record_projection_type(path: &[String], fields: &[String]) -> InferType {
    InferType::Named(
        format!("{}.{{ {} }}", path.join("::"), fields.join(", ")),
        vec![],
        crate::types::NominalId::NONE,
    )
}

fn resolve_record_projection_type(
    path: &[String],
    fields: &[String],
    self_ty_name: Option<&str>,
    assoc_ctx: Option<&AssocResolveCtx<'_>>,
) -> InferType {
    // #774: `Self` resolves to the enclosing impl's own target type everywhere else
    // a plain type name can appear (see the `TypeExpr::Named` arm below) -- a record
    // projection's own path never got the same treatment, so `Self.{ fd }` looked up
    // a struct literally named "Self" (never found) instead of the real target.
    let lookup_name = if path.len() == 1 && path[0] == "Self" {
        self_ty_name.map(str::to_string)
    } else {
        None
    };
    // Errors still show the source spelling (`Self.{ fd }`), not the resolved target
    // name -- resolving `Self` is this function's job, not a rewrite of what the
    // programmer wrote.
    let display_name = path.join("::");
    let Some(ctx) = assoc_ctx else {
        return unresolved_record_projection_type(path, fields);
    };
    let Some((struct_id, struct_name, raw_fields)) = ctx.registry.projection_struct_fields(
        ctx.current_module,
        lookup_name.as_deref().unwrap_or(&display_name),
    ) else {
        return unresolved_record_projection_type(path, fields);
    };

    let mut projected = Vec::with_capacity(fields.len());
    for field_name in fields {
        // Deliberately not `filter_map`: a label the struct does not have must not be
        // dropped, or `Handle.{ nope }` would silently become the empty record `{}`.
        let Some(entry) = raw_fields.iter().find(|entry| entry.name == *field_name) else {
            return unresolved_record_projection_type(path, fields);
        };
        projected.push((field_name.clone(), entry.ty.clone()));
    }
    // RFC-0137 (metel-core#857): a projection off a real struct is branded, not a bare
    // Record -- that's the entire point (Self.{ fd } must reject an unrelated anonymous
    // record literal of the same shape). A projection naming every field the struct
    // declares normalizes back to the plain Named type instead of constructing a
    // Residual (§3's own worked example: full-width projection is still just the
    // struct, not a distinct form) -- `Type::Residual`'s own invariant requires this.
    if projected.len() == raw_fields.len() {
        // metel-core#1137: `projection_struct_fields` already resolved this
        // exact `SymbolId` above -- carry it through instead of discarding it,
        // the same identity the inference-side twin of this function now also
        // preserves (see the comment above referencing this pairing).
        return InferType::Named(
            struct_name.to_string(),
            vec![],
            crate::types::NominalId::some(struct_id),
        );
    }
    // `Residual::fields` is always lexicographically sorted by label (mirrors
    // `Record`'s own invariant) so derived `PartialEq`/structural unification compare
    // correctly regardless of the source projection's written field order.
    projected.sort_by(|(a, _), (b, _)| a.cmp(b));
    InferType::Residual {
        brand: struct_name.to_string(),
        fields: projected,
    }
}

// Exhaustive match over every TypeExpr variant; splitting it up would scatter
// one coherent dispatch table across many small functions with no real gain
// in clarity.
#[allow(clippy::too_many_lines)]
fn type_expr_to_infer_in_context(
    te: &TypeExpr,
    generics: Option<&HashMap<String, TypeVar>>,
    self_ty_name: Option<&str>,
    assoc_ctx: Option<&AssocResolveCtx<'_>>,
) -> InferType {
    match te {
        TypeExpr::Named(name, args) => {
            // RFC-0082 §1.2 bare-name sugar: inside an aspect's method signature,
            // `Item` alone resolves as `Self::Item` when the aspect declares
            // an associated type named `Item`.
            if args.is_empty() {
                if let Some(ctx) = assoc_ctx {
                    if let Some(aspect) = ctx.current_aspect {
                        if let Some(decls) = ctx.registry.aspect_assoc_type_decls(aspect) {
                            if decls.iter().any(|d| d.name == *name) {
                                // Treat as Projection { base: Self, assoc_name: name }
                                let base = TypeExpr::Named("Self".to_string(), vec![]);
                                let proj = TypeExpr::Projection {
                                    base: Box::new(base),
                                    assoc_name: name.clone(),
                                    span: Span::new(0, 0, ""),
                                };
                                return type_expr_to_infer_in_context(
                                    &proj,
                                    generics,
                                    self_ty_name,
                                    assoc_ctx,
                                );
                            }
                        }
                    }
                }
                if let Some(generics) = generics {
                    if let Some(&tv) = generics.get(name.as_str()) {
                        return InferType::Var(tv);
                    }
                }
                if name == "Self" {
                    if let Some(target) = self_ty_name {
                        // #650: recurse as if the source had spelled the resolved
                        // target name directly, so a primitive target (`i64`,
                        // `String`, ...) falls through this same function's own
                        // dispatch table below into its real `InferType::Concrete`
                        // representation, instead of being wrapped in `Named(..)`
                        // here -- which the unifier has no bridge for (see
                        // `primitive_type_from_name`'s doc comment in
                        // `inference.rs`) and produced a confusing "cannot unify
                        // i64 with i64" the moment a primitive `extend` target's
                        // method returned `Self`. Safe from infinite recursion:
                        // `self_ty_name` is always the real target name, never the
                        // literal string "Self".
                        return type_expr_to_infer_in_context(
                            &TypeExpr::Named(target.to_string(), vec![]),
                            generics,
                            self_ty_name,
                            assoc_ctx,
                        );
                    }
                }
            }
            let arg_tys: Vec<_> = args
                .iter()
                .map(|a| type_expr_to_infer_in_context(a, generics, self_ty_name, assoc_ctx))
                .collect();
            match (name.as_str(), arg_tys.len()) {
                ("i64", 0) => InferType::int(),
                ("f64", 0) => InferType::float(),
                ("boolean", 0) => InferType::bool(),
                ("Char", 0) => InferType::Concrete(Type::Char),
                ("String", 0) => InferType::str(),
                ("Never", 0) => InferType::never(),
                ("i8", 0) => InferType::Concrete(Type::I8),
                ("i16", 0) => InferType::Concrete(Type::I16),
                ("i32", 0) => InferType::Concrete(Type::I32),
                ("u8", 0) => InferType::Concrete(Type::U8),
                ("u16", 0) => InferType::Concrete(Type::U16),
                ("u32", 0) => InferType::Concrete(Type::U32),
                ("u64", 0) => InferType::Concrete(Type::U64),
                ("f32", 0) => InferType::Concrete(Type::F32),
                ("Array", 1) => InferType::Array(Box::new(arg_tys.into_iter().next().unwrap())),
                _ => {
                    // A `root`/`self`/`super`-qualified name (#659) or a plain
                    // `as Alias`-imported name (#667) must canonicalize to the same
                    // spelling an equivalent value-position path would -- otherwise
                    // `let t: root::parser::Token = root::parser::Token{..}` (or,
                    // for #667, `let t: Tok = Token{..}` given `import ... as Tok;`)
                    // resolves the annotation but leaves it unifying with a
                    // differently-spelled `InferType::Named` for what's really the
                    // same type.
                    let canonical = assoc_ctx.and_then(|ctx| {
                        ctx.registry
                            .canonicalize_type_name(ctx.current_module, name)
                    });
                    let resolved_name = canonical.unwrap_or_else(|| name.clone());
                    // metel-core#1129: this is a type annotation written in
                    // source, resolved from its own module's scope -- exactly
                    // where identity resolution is reliable (unlike a value
                    // flowing into a *different* module's bound check later).
                    // Populating it here is what lets that later check find
                    // the real declaration instead of guessing by name.
                    let id = assoc_ctx
                        .and_then(|ctx| {
                            ctx.registry
                                .resolve_type_id(ctx.current_module, &resolved_name)
                        })
                        .map_or(crate::types::NominalId::NONE, crate::types::NominalId::some);
                    InferType::Named(resolved_name, arg_tys, id)
                }
            }
        }
        TypeExpr::Unit => InferType::unit(),
        TypeExpr::Tuple(ts) => InferType::Tuple(
            ts.iter()
                .map(|t| type_expr_to_infer_in_context(t, generics, self_ty_name, assoc_ctx))
                .collect(),
        ),
        TypeExpr::Record(fields) => InferType::Record(
            fields
                .iter()
                .map(|(name, ty)| {
                    (
                        name.clone(),
                        type_expr_to_infer_in_context(ty, generics, self_ty_name, assoc_ctx),
                    )
                })
                .collect(),
        ),
        TypeExpr::Array(t) => InferType::Array(Box::new(type_expr_to_infer_in_context(
            t,
            generics,
            self_ty_name,
            assoc_ctx,
        ))),
        TypeExpr::SizedArray(t, n) => InferType::SizedArray(
            Box::new(type_expr_to_infer_in_context(
                t,
                generics,
                self_ty_name,
                assoc_ctx,
            )),
            *n,
        ),
        TypeExpr::Reference(t) => InferType::Reference(Box::new(type_expr_to_infer_in_context(
            t,
            generics,
            self_ty_name,
            assoc_ctx,
        ))),
        TypeExpr::MutReference(t) => InferType::MutReference(Box::new(
            type_expr_to_infer_in_context(t, generics, self_ty_name, assoc_ctx),
        )),
        TypeExpr::Fun {
            params: ps,
            return_type: ret,
            call_multiplicity,
            call_mutation,
        } => InferType::Fun(
            ps.iter()
                .map(|p| type_expr_to_infer_in_context(p, generics, self_ty_name, assoc_ctx))
                .collect(),
            Box::new(ret.as_deref().map_or(InferType::unit(), |r| {
                type_expr_to_infer_in_context(r, generics, self_ty_name, assoc_ctx)
            })),
            *call_multiplicity,
            crate::types::UseMultiplicity::Move,
            *call_mutation,
        ),
        TypeExpr::ImplAspect { bound, .. } => {
            type_expr_to_infer_in_context(bound, generics, self_ty_name, assoc_ctx)
        }
        // RFC-0082 §3: `T::AssocType` projection.
        // Concrete case: base resolves to a known type (not a generic param).
        // Look up the aspect that declares this assoc name and resolve to the
        // concrete binding from the impl.
        TypeExpr::Projection {
            base, assoc_name, ..
        } => {
            // Resolve the base type.
            let base_ty =
                type_expr_to_infer_in_context(base.as_ref(), generics, self_ty_name, assoc_ctx);
            // If the base is a TypeVar (generic param), the concrete case
            // doesn't apply — fall back to a Named placeholder (abstract case
            // is handled by the caller in inference.rs with &mut InferContext).
            if matches!(&base_ty, InferType::Var(_)) {
                let base_name = match base.as_ref() {
                    TypeExpr::Named(n, _) => n.clone(),
                    _ => String::new(),
                };
                return InferType::Named(
                    format!("{base_name}::{assoc_name}"),
                    vec![],
                    crate::types::NominalId::NONE,
                );
            }
            // Extract the base type's name for registry lookup.
            let base_name = match &base_ty {
                InferType::Named(n, ..) | InferType::Concrete(Type::Named(n, ..)) => {
                    Some(n.as_str())
                }
                _ => None,
            };
            if let (Some(ctx), Some(bn)) = (assoc_ctx, base_name) {
                // If current_aspect is known (we're inside an aspect method or an
                // impl block's own conversion), resolve directly against it.
                if let Some(aspect) = ctx.current_aspect {
                    if let Some(ty) =
                        ctx.registry
                            .impl_assoc_type(ctx.current_module, bn, aspect, assoc_name)
                    {
                        return type_to_infer(ty);
                    }
                }
                // No known aspect and a concrete (non-generic, non-Self) base: a
                // projection like `SomeConcreteType::AssocName` used outside any
                // impl/aspect context. Not exercised by any RFC-0082 example (every
                // real case is either `T::AssocType` on a generic param -- handled
                // by the abstract-case special-casing in inference.rs before this
                // function is ever called -- or bare `Self::AssocType` sugar inside
                // an aspect/impl, where current_aspect is always Some). Falls
                // through to the defensive placeholder below rather than guessing
                // which aspect is meant.
            }
            // Fallback: return a Named placeholder (defensive — §2's completeness
            // check is the real guard).
            let base_name_str = match &base_ty {
                InferType::Named(n, ..) | InferType::Concrete(Type::Named(n, ..)) => n.clone(),
                _ => String::new(),
            };
            InferType::Named(
                format!("{base_name_str}::{assoc_name}"),
                vec![],
                crate::types::NominalId::NONE,
            )
        }
        TypeExpr::RecordProjection { path, fields, .. } => {
            resolve_record_projection_type(path, fields, self_ty_name, assoc_ctx)
        }
        // RFC-0008: `dyn Aspect` — an existential type, not lowered away the way
        // `ImplAspect` is. `bound` is always a `named_type` (parser guarantees this
        // via `dyn_type = { "dyn" ~ named_type }`), so its name is the principal
        // aspect and its args are the aspect's own type arguments.
        TypeExpr::DynAspect { bound, .. } => {
            let TypeExpr::Named(aspect, args) = bound.as_ref() else {
                unreachable!("dyn_type grammar only ever produces a named_type bound")
            };
            InferType::Dyn {
                aspect: aspect.clone(),
                type_args: args
                    .iter()
                    .map(|a| type_expr_to_infer_in_context(a, generics, self_ty_name, assoc_ctx))
                    .collect(),
            }
        }
    }
}

/// Like `type_expr_to_infer` but substitutes known generic parameter names with their
/// corresponding `InferType::Var`s.  Call this when inferring a generic function body
/// where `generics` maps each parameter name (e.g. `"T"`) to its fresh `TypeVar`.
pub(super) fn type_expr_to_infer_with_generics(
    te: &TypeExpr,
    generics: &HashMap<String, TypeVar>,
) -> InferType {
    type_expr_to_infer_in_context(te, Some(generics), None, None)
}

pub(super) fn type_expr_to_infer_with_generics_and_self(
    te: &TypeExpr,
    generics: &HashMap<String, TypeVar>,
    self_ty_name: &str,
) -> InferType {
    type_expr_to_infer_in_context(te, Some(generics), Some(self_ty_name), None)
}

/// Convert a source-level `TypeExpr` to an `InferType` for use during inference.
pub(super) fn type_expr_to_infer(te: &TypeExpr) -> InferType {
    type_expr_to_infer_in_context(te, None, None, None)
}

pub(super) fn type_expr_to_infer_with_self(te: &TypeExpr, self_ty_name: &str) -> InferType {
    type_expr_to_infer_in_context(te, None, Some(self_ty_name), None)
}

/// Convert a source-level `TypeExpr` to an `InferType` with associated-type
/// resolution context. Used when converting type annotations inside aspect
/// method signatures (§1.2 bare-name sugar) or concrete projection positions.
pub(super) fn type_expr_to_infer_with_assoc_ctx(
    te: &TypeExpr,
    generics: &HashMap<String, TypeVar>,
    self_ty_name: Option<&str>,
    assoc_ctx: &AssocResolveCtx<'_>,
) -> InferType {
    type_expr_to_infer_in_context(te, Some(generics), self_ty_name, Some(assoc_ctx))
}

/// Convert a fully-solved `InferType` to a concrete `Type`.
/// Returns E0002 if any type variable is still unresolved.
pub(super) fn infer_type_to_type(ty: &InferType, span: &Span) -> Result<Type, MetelError> {
    match ty {
        InferType::Concrete(t) => Ok(t.clone()),
        InferType::Never => Ok(Type::Never),
        InferType::Var(_) => Err(MetelError::type_error(
            TypeErrorCode::T0002,
            "cannot infer type; add a type annotation",
            span,
        )),
        InferType::Fun(params, ret, call_mult, use_mult, call_mutation) => {
            let p: Result<Vec<_>, _> = params.iter().map(|p| infer_type_to_type(p, span)).collect();
            Ok(Type::Fun(
                p?,
                Box::new(infer_type_to_type(ret, span)?),
                *call_mult,
                *use_mult,
                *call_mutation,
            ))
        }
        InferType::Tuple(ts) => {
            let t: Result<Vec<_>, _> = ts.iter().map(|t| infer_type_to_type(t, span)).collect();
            Ok(Type::Tuple(t?))
        }
        InferType::Record(fields) => Ok(Type::Record(
            fields
                .iter()
                .map(|(name, ty)| Ok((name.clone(), infer_type_to_type(ty, span)?)))
                .collect::<Result<Vec<_>, MetelError>>()?,
        )),
        InferType::Array(t) => Ok(Type::Array(Box::new(infer_type_to_type(t, span)?))),
        InferType::SizedArray(t, n) => {
            Ok(Type::SizedArray(Box::new(infer_type_to_type(t, span)?), *n))
        }
        InferType::Reference(t) => Ok(Type::Reference(Box::new(infer_type_to_type(t, span)?))),
        InferType::MutReference(t) => {
            Ok(Type::MutReference(Box::new(infer_type_to_type(t, span)?)))
        }
        InferType::Named(name, args, id) => {
            let a: Result<Vec<_>, _> = args.iter().map(|a| infer_type_to_type(a, span)).collect();
            let args = a?;
            Ok(Type::Named(name.clone(), args, id.clone()))
        }
        InferType::Residual { brand, fields } => Ok(Type::Residual {
            brand: brand.clone(),
            fields: fields
                .iter()
                .map(|(name, ty)| Ok((name.clone(), infer_type_to_type(ty, span)?)))
                .collect::<Result<Vec<_>, MetelError>>()?,
        }),
        InferType::Dyn { aspect, type_args } => Ok(Type::Dyn {
            aspect: aspect.clone(),
            type_args: type_args
                .iter()
                .map(|a| infer_type_to_type(a, span))
                .collect::<Result<Vec<_>, MetelError>>()?,
        }),
    }
}

pub(super) fn resolved_to_type(
    ty: &InferType,
    subst: &Substitution,
    span: &Span,
) -> Result<Type, MetelError> {
    infer_type_to_type(&subst.apply(ty), span)
}

// `type_to_infer` now lives in `typeinference` alongside `InferType` itself:
// it is the canonical embedding of a concrete `Type` into inference space, and
// the aspect-satisfaction query there needs it. Re-exported so the many call
// sites in this module's siblings keep their existing import.
pub(super) use crate::typeinference::type_to_infer;
