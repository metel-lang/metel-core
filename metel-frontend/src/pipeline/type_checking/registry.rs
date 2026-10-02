use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::conversions::{
    AssocResolveCtx, type_expr_to_infer, type_expr_to_infer_with_assoc_ctx,
    type_expr_to_infer_with_generics, type_expr_to_infer_with_self,
};
use crate::data::ast::{
    AspectDecl, AspectMethod, Decl, GenericParam, Polarity, Program, Span, StructKind, TypeExpr,
    WhereClause,
};
use crate::identity::symbols::SymbolId;
use crate::pipeline::name_resolution::name_resolver::ModuleScope;
use crate::pipeline::type_checking::type_engine::{
    EnumInfo, FieldEntry, GenericBound, InferContext, InferType, RowConstraint, RowConstraintField,
    TypeDefinitionRegistry, TypeScheme, TypeVar, TypeVarGenerator, VariantInfo,
};

/// Collect merged aspect-name bounds per type param from inline bounds + where clause.
/// Returns one Vec<String> per param (same order as `generics`), containing all
/// required aspect names for that param (deduped).
pub(super) fn collect_type_param_bounds(
    generics: &[GenericParam],
    where_clause: Option<&WhereClause>,
) -> Vec<Vec<GenericBound>> {
    generics
        .iter()
        .map(|gp| {
            // Negative bounds (`T: !Drop`) are dropped from this positive aspect-name
            // list for now — their satisfaction checking is issue #243's job.
            let mut names: Vec<GenericBound> = gp
                .bounds
                .iter()
                .filter(|b| b.polarity == Polarity::Positive)
                .filter_map(GenericBound::from_ast)
                .collect();
            if let Some(wc) = where_clause {
                for constraint in &wc.constraints {
                    if constraint.name != gp.name {
                        continue;
                    }
                    for b in constraint
                        .bounds
                        .iter()
                        .filter(|b| b.polarity == Polarity::Positive)
                    {
                        if let Some(n) = GenericBound::from_ast(b)
                            && !names.iter().any(|existing| matches!((existing, &n), (GenericBound::Aspect(a), GenericBound::Aspect(b)) if a == b)) {
                                names.push(n);
                            }
                    }
                }
            }
            names
        })
        .collect()
}

/// Collect **negative** aspect-name bounds per type param (RFC-0072, issue #243).
/// Mirrors `collect_type_param_bounds` but filters for `Polarity::Negative`.
pub(super) fn collect_negative_type_param_bounds(
    generics: &[GenericParam],
    where_clause: Option<&WhereClause>,
) -> Vec<Vec<GenericBound>> {
    generics
        .iter()
        .map(|gp| {
            let mut names: Vec<GenericBound> = gp
                .bounds
                .iter()
                .filter(|b| b.polarity == Polarity::Negative)
                .filter_map(GenericBound::from_ast)
                .collect();
            if let Some(wc) = where_clause {
                for constraint in &wc.constraints {
                    if constraint.name != gp.name {
                        continue;
                    }
                    for b in constraint
                        .bounds
                        .iter()
                        .filter(|b| b.polarity == Polarity::Negative)
                    {
                        if let Some(n) = GenericBound::from_ast(b)
                            && !names.iter().any(|existing| matches!((existing, &n), (GenericBound::Aspect(a), GenericBound::Aspect(b)) if a == b)) {
                                names.push(n);
                            }
                    }
                }
            }
            names
        })
        .collect()
}

pub(super) fn collect_type_param_record_kinds(
    generics: &[GenericParam],
    where_clause: Option<&WhereClause>,
) -> Vec<bool> {
    generics
        .iter()
        .map(|gp| {
            // RFC-0121: a `row` parameter's argument is a (closed) record type,
            // so it is record-kinded like `record T` -- which is also what lets
            // a record argument satisfy its row bound.
            gp.is_record
                || gp.is_row
                || where_clause
                    .and_then(|wc| wc.constraint_for(&gp.name))
                    .is_some_and(|constraint| constraint.is_record)
        })
        .collect()
}

/// Synthesize a `Vec<GenericParam>` from the struct's own canonical generic names
/// merged with the impl block's own `ib.generics`. This lets the bound-collection
/// helpers work uniformly for both inline (`impl<T: Bound>`) and where-clause
/// (`impl for Type<T> where T: Bound`) forms.
pub(super) fn synth_generics_for_impl(
    struct_generic_names: &[String],
    ib_generics: &[GenericParam],
) -> Vec<GenericParam> {
    struct_generic_names
        .iter()
        .map(|n| GenericParam {
            name: n.clone(),
            is_record: ib_generics
                .iter()
                .find(|g| &g.name == n)
                .is_some_and(|g| g.is_record),
            is_row: ib_generics
                .iter()
                .find(|g| &g.name == n)
                .is_some_and(|g| g.is_row),
            bounds: ib_generics
                .iter()
                .find(|g| &g.name == n)
                .map(|g| g.bounds.clone())
                .unwrap_or_default(),
        })
        .collect()
}

/// RFC-0121 item 5: an impl's own generics, with each row generic that the target
/// splices (`extend<row Q: { .. }> Session<..Q>`) renamed to the struct's own
/// parameter at that position, so `synth_generics_for_impl`'s by-name lookup finds
/// its bounds whatever the impl calls it. A rename that would collide with another
/// impl generic is skipped.
pub(super) fn impl_generics_with_row_aliases(
    ib: &crate::data::ast::ImplBlock,
    struct_generic_names: &[String],
) -> Vec<GenericParam> {
    let mut generics = ib.generics.clone();
    let TypeExpr::Named(_, args) = &ib.target_type else {
        return generics;
    };
    for (arg, struct_name) in args.iter().zip(struct_generic_names) {
        let TypeExpr::RowArg(tail) = arg else {
            continue;
        };
        let Some(written) = tail.var.as_deref() else {
            continue;
        };
        if written == struct_name || generics.iter().any(|g| &g.name == struct_name) {
            continue;
        }
        if let Some(g) = generics.iter_mut().find(|g| g.is_row && g.name == written) {
            g.name.clone_from(struct_name);
        }
    }
    generics
}

fn bare_target_generic_name(ib: &crate::data::ast::ImplBlock) -> Option<&str> {
    let TypeExpr::Named(name, args) = &ib.target_type else {
        return None;
    };
    if !args.is_empty() {
        return None;
    }
    ib.generics
        .iter()
        .find(|gp| gp.name == *name)
        .map(|gp| gp.name.as_str())
}

/// The row condition an `extend` on a record target imposes on its receiver
/// (RFC-0121 §3, `spec.types.generics.row-conditional-impls`): a closed record target
/// (`extend { x: f64, y: f64 }: A`) matches exactly that row, a row-tailed one
/// (`extend<row R: { x: f64, .. }> { ..R }: A`) every row carrying its named fields plus
/// whatever the tail variable's own bound, `where` bound or `where R = { .. }`
/// decomposition requires. `None` for any other target.
pub(crate) fn record_target_row(ib: &crate::data::ast::ImplBlock) -> Option<RowConstraint> {
    match &ib.target_type {
        TypeExpr::Record(fields) => Some(RowConstraint {
            fields: fields
                .iter()
                .map(|(label, ty)| RowConstraintField {
                    label: label.clone(),
                    ty: Some(ty.clone()),
                })
                .collect(),
            open: false,
        }),
        TypeExpr::OpenRecord(fields, tail) => {
            let mut row_fields: Vec<RowConstraintField> = fields
                .iter()
                .map(|(label, ty)| RowConstraintField {
                    label: label.clone(),
                    ty: Some(ty.clone()),
                })
                .collect();
            if let Some(var) = tail.var.as_deref() {
                let from_bounds = |bounds: &[crate::data::ast::Bound]| -> Vec<RowConstraintField> {
                    bounds
                        .iter()
                        .filter(|b| b.polarity == Polarity::Positive)
                        .filter_map(GenericBound::from_ast)
                        .filter_map(|b| match b {
                            GenericBound::Row(row) => Some(row.fields),
                            _ => None,
                        })
                        .flatten()
                        .collect()
                };
                for gp in ib.generics.iter().filter(|gp| gp.name == var) {
                    row_fields.extend(from_bounds(&gp.bounds));
                }
                if let Some(wc) = &ib.where_clause {
                    for constraint in wc.constraints.iter().filter(|c| c.name == var) {
                        row_fields.extend(from_bounds(&constraint.bounds));
                    }
                    if let Some(equation) = wc.row_equation_for(var) {
                        row_fields.extend(equation.fields.iter().map(|(label, ty)| {
                            RowConstraintField {
                                label: label.clone(),
                                ty: Some(ty.clone()),
                            }
                        }));
                    }
                }
            }
            Some(RowConstraint {
                fields: row_fields,
                open: true,
            })
        }
        _ => None,
    }
}

/// RFC-0123 `where all R: Aspect` on an `extend` whose target is `{ .., ..R }`: every
/// field of the receiver beyond the target's own named ones satisfies each aspect.
pub(crate) fn record_target_all_fields(ib: &crate::data::ast::ImplBlock) -> Vec<GenericBound> {
    let TypeExpr::OpenRecord(fields, tail) = &ib.target_type else {
        return vec![];
    };
    let (Some(var), Some(wc)) = (tail.var.as_deref(), &ib.where_clause) else {
        return vec![];
    };
    wc.field_wise
        .iter()
        .filter(|c| c.var == var)
        .map(|c| GenericBound::AllFields {
            aspects: c
                .bounds
                .iter()
                .filter(|b| b.polarity == Polarity::Positive)
                .filter_map(|b| b.aspect_name().map(str::to_string))
                .collect(),
            except: fields.iter().map(|(label, _)| label.clone()).collect(),
        })
        .collect()
}

pub(super) fn array_target_generic_name(ib: &crate::data::ast::ImplBlock) -> Option<&str> {
    let TypeExpr::Array(inner) = &ib.target_type else {
        return None;
    };
    let TypeExpr::Named(name, args) = inner.as_ref() else {
        return None;
    };
    if !args.is_empty() {
        return None;
    }
    ib.generics
        .iter()
        .find(|gp| gp.name == *name)
        .map(|gp| gp.name.as_str())
}

/// Derive the prelude schemes by parsing the embedded `std::core` source:
/// free `native` functions by name, plus static native methods on generic
/// structs as joined-key schemes (`List::new`) quantified over the struct's
/// type params (METEL-181). `stdlib/core.mtl` + the `NativeKey` enum are the
/// single source of truth — there is no hand-maintained scheme list to keep in
/// sync. Used by `CorePrelude::default()` so the single-program pipeline (which
/// performs no module loading) sees the same surface as the module graph path.
fn populate_schemes_from_embedded_core(
    map: &mut HashMap<String, TypeScheme>,
    type_var_gen: &mut TypeVarGenerator,
) {
    let program = crate::stdlib::core_program();
    for decl in &program.decls {
        match decl {
            Decl::Fun(fun) => {
                if fun.native.is_none() {
                    continue;
                }
                // Overloaded std::core natives (the assert pair) are dispatched
                // by SymbolId via the seeded overload table, never by name.
                if super::overload::core_overload_table().contains_key(&fun.name) {
                    continue;
                }
                let generic_map: HashMap<String, TypeVar> = fun
                    .generics
                    .iter()
                    .map(|g| (g.name.clone(), type_var_gen.fresh()))
                    .collect();
                let te = |t: &TypeExpr| -> InferType {
                    if generic_map.is_empty() {
                        type_expr_to_infer(t)
                    } else {
                        type_expr_to_infer_with_generics(t, &generic_map)
                    }
                };
                let params: Vec<InferType> = fun
                    .params
                    .iter()
                    .map(|p| {
                        p.type_ann.as_ref().map(te).expect(
                            "native declarations are fully annotated (enforced by native_fun_ty)",
                        )
                    })
                    .collect();
                let ret = fun.return_type.as_ref().map_or_else(InferType::unit, te);
                let fun_ty = InferType::fun(params, ret);
                let bounds = super::inference::collect_fun_type_var_bounds(fun, &generic_map);
                let neg_bounds =
                    super::inference::collect_negative_fun_type_var_bounds(fun, &generic_map);
                let scheme = crate::pipeline::type_checking::type_engine::generalize(
                    fun_ty,
                    &HashSet::default(),
                )
                .with_bounds(&bounds)
                .with_neg_bounds(&neg_bounds);
                map.insert(fun.name.clone(), scheme);
            }
            Decl::Impl(ib) => {
                // Static native methods on generic structs become joined-key
                // schemes ("List::new") quantified over the struct's params.
                let TypeExpr::Named(target_name, target_args) = &ib.target_type else {
                    continue;
                };
                let generic_map: HashMap<String, TypeVar> = target_args
                    .iter()
                    .filter_map(|te| match te {
                        TypeExpr::Named(n, args) if args.is_empty() => {
                            Some((n.clone(), type_var_gen.fresh()))
                        }
                        _ => None,
                    })
                    .collect();
                if generic_map.is_empty() {
                    continue;
                }
                for method in &ib.methods {
                    if method.native.is_none()
                        || method.params.first().is_some_and(|p| p.receiver.is_some())
                    {
                        continue;
                    }
                    let params: Vec<InferType> = method
                        .params
                        .iter()
                        .map(|p| {
                            p.type_ann
                                .as_ref()
                                .map(|ann| type_expr_to_infer_with_generics(ann, &generic_map))
                                .expect(
                                "native declarations are fully annotated (enforced by native_fun_ty)",
                            )
                        })
                        .collect();
                    let ret = method
                        .return_type
                        .as_ref()
                        .map_or_else(InferType::unit, |ann| {
                            type_expr_to_infer_with_generics(ann, &generic_map)
                        });
                    let fun_ty = InferType::fun(params, ret);
                    let scheme = crate::pipeline::type_checking::type_engine::generalize(
                        fun_ty,
                        &HashSet::default(),
                    );
                    map.insert(format!("{target_name}::{}", method.name), scheme);
                }
            }
            _ => {}
        }
    }
}

pub(super) fn type_expr_to_infer_for_registry(
    te: &TypeExpr,
    generics: &HashMap<String, TypeVar>,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
) -> InferType {
    let assoc_ctx = AssocResolveCtx {
        registry,
        current_module,
        current_aspect: None,
    };
    type_expr_to_infer_with_assoc_ctx(te, generics, None, &assoc_ctx)
}

fn register_builtin_aspect_impls(registry: &mut TypeDefinitionRegistry) {
    use crate::data::types::Type;
    use crate::identity::symbols::{SYM_TYPE_RANGE, SYM_TYPE_RANGE_INCLUSIVE};
    // Iterable impls for built-in sequence types. Runtime ranges are intrinsic,
    // so these stay hand-registered; the primitive Display impls and the
    // numeric From cross-product are declared in the embedded std::core source
    // and registered through the normal impl-decl pass (METEL-181). Target
    // registered directly by id — Range/RangeInclusive are fixed builtin type ids,
    // not names needing scope resolution (ADR-0042); the aspect half stays the
    // literal name "Iterable" (see `impl_aspect_env`'s doc for why).
    registry.register_aspect_impl_by_id(SYM_TYPE_RANGE, "Iterable", vec![Type::I64]);
    registry.register_aspect_impl_by_id(SYM_TYPE_RANGE_INCLUSIVE, "Iterable", vec![Type::I64]);
}

/// Build the `TypeDefinitionRegistry` from the program's declarations and built-in types.
/// Allocates `TypeVars` from `gen`; the caller must pass the same `gen` to
/// `InferContext::new` so that all `TypeVar` IDs are globally unique.
pub(super) fn build_registry(
    program: &Program,
    type_var_gen: &mut TypeVarGenerator,
    current_module_path: &[String],
    symbols: Option<&HashMap<(Vec<String>, String), SymbolId>>,
    scopes: Option<&HashMap<Vec<String>, ModuleScope>>,
) -> TypeDefinitionRegistry {
    let mut registry = TypeDefinitionRegistry::new();
    if let (Some(symbols), Some(scopes)) = (symbols, scopes) {
        // Cloned once per module here, not per lookup — `impl_aspect_env`'s
        // resolution needs its own `Rc` handle to share cheaply as this registry
        // gets merged across modules (`merge_from`), but `ResolvedNames` itself
        // doesn't carry these as `Rc`, so the one clone happens at the boundary.
        registry.set_symbol_resolution(Rc::new(symbols.clone()), Rc::new(scopes.clone()));
    }
    register_builtin_aspect_impls(&mut registry);

    // Builtin types and aspects (Perhaps, Result, List, Display, From,
    // Iterable) are declared in the embedded std::core source and registered
    // through the same machinery as user declarations (METEL-181). When the
    // module being checked IS std::core, its own decl pass below covers them;
    // deriving again here would double-register.
    let std_core_path = ["std".to_string(), "core".to_string()];
    if current_module_path != std_core_path {
        register_program_decls(
            &crate::stdlib::core_program().decls,
            &std_core_path,
            type_var_gen,
            &mut registry,
        );
    }

    register_program_decls(
        &program.decls,
        current_module_path,
        type_var_gen,
        &mut registry,
    );

    registry
}

/// Register a program's type-level declarations (structs, enums, aspects, impl
/// signatures) into the registry. Used both for the module being checked and
/// for the embedded `std::core` decls, which seed every module's registry.
// Exhaustive match over every AST/type-system variant; splitting it up would
// scatter one coherent dispatch table across many small functions with no
// real gain in clarity.
#[allow(clippy::too_many_lines)]
fn register_program_decls(
    decls: &[Decl],
    current_module_path: &[String],
    type_var_gen: &mut TypeVarGenerator,
    registry: &mut TypeDefinitionRegistry,
) {
    // Pass 1: register structs, enums, and aspects.
    for decl in decls {
        match decl {
            Decl::Struct(sd) if sd.generics.is_empty() => {
                // A struct with no declaring symbol is a broken resolution state;
                // skip it rather than fabricate an id (metel-core#1060).
                let Some(sym) = registry.resolve_type_id(current_module_path, &sd.name) else {
                    continue;
                };
                let empty_generics = HashMap::new();
                let fields: Vec<FieldEntry> = sd
                    .fields
                    .iter()
                    .map(|f| FieldEntry {
                        name: f.name.clone(),
                        ty: type_expr_to_infer_for_registry(
                            &f.type_ann,
                            &empty_generics,
                            registry,
                            current_module_path,
                        ),
                        span: f.span.clone(),
                        visibility: f.visibility.clone(),
                        id: None,
                    })
                    .collect();
                registry.register_struct_fields(
                    sym,
                    sd.name.clone(),
                    fields,
                    current_module_path.to_vec(),
                    sd.visibility.clone(),
                    sd.kind == StructKind::Record,
                );
            }
            Decl::Struct(sd) => {
                let Some(sym) = registry.resolve_type_id(current_module_path, &sd.name) else {
                    continue;
                };
                let mut gen_map: HashMap<String, TypeVar> = HashMap::new();
                let mut type_params = vec![];
                for gp in &sd.generics {
                    let tv = type_var_gen.fresh();
                    gen_map.insert(gp.name.clone(), tv);
                    type_params.push(tv);
                }
                let fields: Vec<FieldEntry> = sd
                    .fields
                    .iter()
                    .map(|f| FieldEntry {
                        name: f.name.clone(),
                        ty: type_expr_to_infer_for_registry(
                            &f.type_ann,
                            &gen_map,
                            registry,
                            current_module_path,
                        ),
                        span: f.span.clone(),
                        visibility: f.visibility.clone(),
                        id: None,
                    })
                    .collect();
                registry.register_struct_fields(
                    sym,
                    sd.name.clone(),
                    fields,
                    current_module_path.to_vec(),
                    sd.visibility.clone(),
                    sd.kind == StructKind::Record,
                );
                registry.register_struct_type_params(sym, type_params);
                registry.register_struct_generic_names(
                    sym,
                    sd.generics.iter().map(|g| g.name.clone()).collect(),
                );
                let row_kinds: Vec<bool> = sd.generics.iter().map(|g| g.is_row).collect();
                if row_kinds.iter().any(|flag| *flag) {
                    registry.register_type_param_row_kinds(sym, row_kinds);
                }
                let record_kinds =
                    collect_type_param_record_kinds(&sd.generics, sd.where_clause.as_ref());
                if record_kinds.iter().any(|flag| *flag) {
                    registry.register_type_param_record_kinds(sym, record_kinds);
                }
                let bounds = collect_type_param_bounds(&sd.generics, sd.where_clause.as_ref());
                if bounds.iter().any(|b| !b.is_empty()) {
                    registry.register_type_param_bounds(sym, bounds);
                }
                let neg_bounds =
                    collect_negative_type_param_bounds(&sd.generics, sd.where_clause.as_ref());
                if neg_bounds.iter().any(|b| !b.is_empty()) {
                    registry.register_neg_type_param_bounds(sym, neg_bounds);
                }
            }
            Decl::Enum(ed) => {
                let enum_sym = registry.resolve_type_id(current_module_path, &ed.name);
                let mut gen_map: HashMap<String, TypeVar> = HashMap::new();
                let mut type_params = vec![];
                for gp in &ed.generics {
                    let tv = type_var_gen.fresh();
                    gen_map.insert(gp.name.clone(), tv);
                    type_params.push(tv);
                }
                let variants = ed
                    .variants
                    .iter()
                    .map(|v| VariantInfo {
                        name: v.name.clone(),
                        fields: v
                            .fields
                            .iter()
                            .map(|f| FieldEntry {
                                name: f.name.clone(),
                                ty: type_expr_to_infer_with_generics(&f.type_ann, &gen_map),
                                span: f.span.clone(),
                                visibility: f.visibility.clone(),
                                id: None,
                            })
                            .collect(),
                        id: None,
                    })
                    .collect();
                if let Some(sym) = enum_sym {
                    registry.register_struct_generic_names(
                        sym,
                        ed.generics.iter().map(|g| g.name.clone()).collect(),
                    );
                }
                if let Some(sym) = enum_sym {
                    let row_kinds: Vec<bool> = ed.generics.iter().map(|g| g.is_row).collect();
                    if row_kinds.iter().any(|flag| *flag) {
                        registry.register_type_param_row_kinds(sym, row_kinds);
                    }
                }
                let record_kinds =
                    collect_type_param_record_kinds(&ed.generics, ed.where_clause.as_ref());
                let bounds = collect_type_param_bounds(&ed.generics, ed.where_clause.as_ref());
                if let Some(sym) = enum_sym {
                    registry.register_enum(
                        sym,
                        ed.name.clone(),
                        EnumInfo {
                            type_params,
                            variants,
                        },
                        current_module_path.to_vec(),
                    );
                    if record_kinds.iter().any(|flag| *flag) {
                        registry.register_type_param_record_kinds(sym, record_kinds);
                    }
                    if bounds.iter().any(|b| !b.is_empty()) {
                        registry.register_type_param_bounds(sym, bounds);
                    }
                    let neg_bounds =
                        collect_negative_type_param_bounds(&ed.generics, ed.where_clause.as_ref());
                    if neg_bounds.iter().any(|b| !b.is_empty()) {
                        registry.register_neg_type_param_bounds(sym, neg_bounds);
                    }
                }
            }
            Decl::Aspect(ad) => {
                register_aspect_decl(ad, current_module_path, registry);
            }
            _ => {}
        }
    }

    // Pass 2: register impl method signatures once all aspect definitions are known.
    // Methods on generic structs (where the target type has registered type params) are
    // skipped here — they contain T-typed params that need TypeVars, not Named("T",[]).
    // infer_impl_method in inference.rs registers them correctly as polymorphic schemes.
    for decl in decls {
        if let Decl::Impl(ib) = decl {
            let nominal_target_name = match &ib.target_type {
                TypeExpr::Named(name, _) => Some(name.clone()),
                _ => None,
            };
            let is_array_generic_target = array_target_generic_name(ib).is_some();
            if let Some(row) = record_target_row(ib) {
                register_record_target_impl(ib, &row, type_var_gen, registry);
                continue;
            }
            if nominal_target_name.is_none() && !is_array_generic_target {
                continue;
            }

            // #746: a method with its *own* generics (e.g. `fun describe<U:
            // Aspect>` inside `extend Foo { ... }`, where `Foo` itself has no
            // generics and neither does the impl block) needs the same
            // polymorphic-scheme treatment as an impl-level generic -- it also
            // has T-typed params that need TypeVars, not Named("U",[]).
            // Missing this case used to route such methods through
            // `register_impl_methods` (the concrete/fast path), which has no
            // way to represent the method's own generic parameter, so nothing
            // usable for call-time dispatch ever got registered for it.
            let has_method_own_generics = ib.methods.iter().any(|m| !m.generics.is_empty());
            let is_generic_target = is_array_generic_target
                || !ib.generics.is_empty()
                || has_method_own_generics
                || nominal_target_name.as_ref().is_some_and(|target_name| {
                    registry
                        .struct_generic_names_for(current_module_path, target_name.as_str())
                        .is_some_and(|names| !names.is_empty())
                });

            if is_array_generic_target {
                register_array_impl_method_schemes(ib, type_var_gen, registry);
            } else if let Some(target_name) = nominal_target_name.as_ref() {
                if is_generic_target {
                    register_generic_impl_method_schemes(
                        ib,
                        target_name,
                        current_module_path,
                        type_var_gen,
                        registry,
                    );
                } else {
                    register_impl_methods(
                        ib.methods.iter(),
                        target_name,
                        current_module_path,
                        type_var_gen,
                        registry,
                    );
                    if ib.polarity == Polarity::Positive {
                        register_default_aspect_methods(
                            ib,
                            target_name,
                            type_var_gen,
                            registry,
                            current_module_path,
                        );
                    }
                }
            }

            if ib.polarity == Polarity::Positive {
                if let Some(aspect_name) = &ib.aspect_name {
                    let type_args: Vec<crate::data::types::Type> = ib
                        .aspect_type_args
                        .iter()
                        .filter_map(|te| {
                            match type_expr_to_infer_for_registry(
                                te,
                                &HashMap::new(),
                                registry,
                                current_module_path,
                            ) {
                                InferType::Concrete(t) => Some(t),
                                InferType::Named(n, ..) => Some(crate::data::types::Type::Named(
                                    n,
                                    vec![],
                                    crate::data::types::NominalId::NONE,
                                )),
                                _ => None,
                            }
                        })
                        .collect();
                    if is_generic_target {
                        if bare_target_generic_name(ib).is_some() {
                            let pos_bounds =
                                collect_type_param_bounds(&ib.generics, ib.where_clause.as_ref());
                            let neg_bounds = collect_negative_type_param_bounds(
                                &ib.generics,
                                ib.where_clause.as_ref(),
                            );
                            registry.register_bare_impl_bounds(aspect_name, pos_bounds, neg_bounds);
                        } else if is_array_generic_target {
                            let pos_bounds =
                                collect_type_param_bounds(&ib.generics, ib.where_clause.as_ref());
                            let neg_bounds = collect_negative_type_param_bounds(
                                &ib.generics,
                                ib.where_clause.as_ref(),
                            );
                            registry.register_array_impl_bounds(
                                aspect_name,
                                pos_bounds,
                                neg_bounds,
                            );
                        } else if let Some(target_name) = nominal_target_name.as_ref() {
                            let generic_names = registry
                                .struct_generic_names_for(current_module_path, target_name.as_str())
                                .cloned()
                                .unwrap_or_default();
                            let synth = synth_generics_for_impl(
                                &generic_names,
                                &impl_generics_with_row_aliases(ib, &generic_names),
                            );
                            let pos_bounds =
                                collect_type_param_bounds(&synth, ib.where_clause.as_ref());
                            let neg_bounds = collect_negative_type_param_bounds(
                                &synth,
                                ib.where_clause.as_ref(),
                            );
                            if pos_bounds.iter().any(|b| !b.is_empty())
                                || neg_bounds.iter().any(|b| !b.is_empty())
                            {
                                registry.register_conditional_impl_bounds(
                                    current_module_path,
                                    target_name,
                                    aspect_name,
                                    pos_bounds,
                                    neg_bounds,
                                );
                            } else {
                                registry.register_aspect_impl(
                                    current_module_path,
                                    target_name,
                                    aspect_name,
                                    type_args,
                                );
                            }
                        }
                    } else if let Some(target_name) = nominal_target_name.as_ref() {
                        registry.register_aspect_impl(
                            current_module_path,
                            target_name,
                            aspect_name,
                            type_args,
                        );
                    }
                    if let Some(target_name) = nominal_target_name.as_ref()
                        && !is_generic_target
                        && !ib.assoc_type_defs.is_empty()
                    {
                        let mut bindings = HashMap::new();
                        for def in &ib.assoc_type_defs {
                            let infer_ty = super::conversions::type_expr_to_infer_with_self(
                                &def.ty,
                                target_name,
                            );
                            let dummy = Span::new(0, 0, "");
                            if let Ok(concrete_ty) =
                                super::conversions::infer_type_to_type(&infer_ty, &dummy)
                            {
                                bindings.insert(def.name.clone(), concrete_ty);
                            }
                        }
                        if !bindings.is_empty() {
                            registry.register_impl_assoc_types(
                                current_module_path,
                                target_name,
                                aspect_name,
                                bindings,
                            );
                        }
                    }
                }
            } else if ib.polarity == Polarity::Negative
                && let Some(aspect_name) = &ib.aspect_name
            {
                if !ib.generics.is_empty() {
                    if bare_target_generic_name(ib).is_some() {
                        let pos_bounds =
                            collect_type_param_bounds(&ib.generics, ib.where_clause.as_ref());
                        let neg_bounds = collect_negative_type_param_bounds(
                            &ib.generics,
                            ib.where_clause.as_ref(),
                        );
                        registry.register_neg_bare_impl_bounds(aspect_name, pos_bounds, neg_bounds);
                    } else if is_array_generic_target {
                        let pos_bounds =
                            collect_type_param_bounds(&ib.generics, ib.where_clause.as_ref());
                        let neg_bounds = collect_negative_type_param_bounds(
                            &ib.generics,
                            ib.where_clause.as_ref(),
                        );
                        registry.register_neg_array_impl_bounds(
                            aspect_name,
                            pos_bounds,
                            neg_bounds,
                        );
                    } else if let Some(target_name) = nominal_target_name.as_ref() {
                        let generic_names = registry
                            .struct_generic_names_for(current_module_path, target_name.as_str())
                            .cloned()
                            .unwrap_or_default();
                        let synth = synth_generics_for_impl(
                            &generic_names,
                            &impl_generics_with_row_aliases(ib, &generic_names),
                        );
                        let pos_bounds =
                            collect_type_param_bounds(&synth, ib.where_clause.as_ref());
                        let neg_bounds =
                            collect_negative_type_param_bounds(&synth, ib.where_clause.as_ref());
                        registry.register_neg_conditional_impl_bounds(
                            current_module_path,
                            target_name,
                            aspect_name,
                            pos_bounds,
                            neg_bounds,
                        );
                    }
                } else if let (Some(target_name), TypeExpr::Named(_, target_type_args)) =
                    (nominal_target_name.as_ref(), &ib.target_type)
                {
                    let concrete_target_args: Vec<crate::data::types::Type> = target_type_args
                        .iter()
                        .filter_map(|te| match type_expr_to_infer(te) {
                            InferType::Concrete(t) => Some(t),
                            InferType::Named(n, ..) => Some(crate::data::types::Type::Named(
                                n,
                                vec![],
                                crate::data::types::NominalId::NONE,
                            )),
                            _ => None,
                        })
                        .collect();
                    registry.register_neg_impl(
                        current_module_path,
                        target_name,
                        aspect_name,
                        concrete_target_args,
                    );
                }
            }
        }
    }
}

fn register_aspect_decl(
    ad: &AspectDecl,
    declaring_module: &[String],
    registry: &mut TypeDefinitionRegistry,
) {
    let method_names = ad.methods.iter().map(|m| m.name.clone()).collect();
    registry.register_aspect_decl(
        ad.name.clone(),
        declaring_module.to_vec(),
        method_names,
        ad.generics.clone(),
        ad.methods.clone(),
        ad.assoc_types.clone(),
    );
}

/// Register the annotated signatures of NATIVE methods in an impl block on a
/// generic struct (e.g. `impl List<T>` in `std::core`) as polymorphic schemes
/// over the struct's registered type params. Metel-bodied methods are handled
/// by `infer_impl_method` instead; static native methods (no receiver) are
/// exposed as joined-key prelude schemes (`List::new`), not method schemes.
/// Register polymorphic method schemes for instance methods on a generic struct
/// or enum, derived from their (fully required) parameter/return annotations.
///
/// This covers both native methods (which have no body to infer) and Metel-bodied
/// methods. Deriving the scheme from annotations is what lets the single-program
/// path (`check_with_ctx`, no module loading) resolve `std::core`'s bodied generic
/// methods like `Perhaps::map` / `List::filter` — there is no separate `std::core`
/// module check there to run `infer_impl_method`. In the graph path the inferred
/// scheme later overwrites this one for `std::core`'s own module; downstream modules
/// use this annotation-derived scheme directly. Static methods (no receiver) are
/// handled as joined-key schemes elsewhere and skipped here.
#[allow(clippy::too_many_lines)]
fn register_generic_impl_method_schemes(
    ib: &crate::data::ast::ImplBlock,
    target_name: &str,
    current_module_path: &[String],
    type_var_gen: &mut TypeVarGenerator,
    registry: &mut TypeDefinitionRegistry,
) {
    let target_id = registry.resolve_type_id(current_module_path, target_name);
    // Type params for the generic target — a struct or an enum. A non-generic
    // struct has no entry in `raw_struct_type_params` at all (registered only
    // for structs with `sd.generics` non-empty -- an optimization elsewhere,
    // not a "this isn't a struct" signal); fall back to `raw_struct_env`,
    // which every struct is unconditionally registered into regardless of its
    // own generics, before concluding `target_name` isn't a struct/enum at
    // all (#746 -- needed so a method with its own generics on an otherwise
    // non-generic target, e.g. `extend Foo { fun describe<U: Aspect>(...) }`,
    // still resolves here instead of bailing).
    let type_params: Vec<TypeVar> = if let Some(tps) = target_id
        .and_then(|id| registry.raw_struct_type_params().get(&id))
        .cloned()
    {
        tps
    } else if let Some(info) = registry.enum_info(current_module_path, target_name) {
        info.type_params.clone()
    } else if target_id.is_some_and(|id| registry.raw_struct_env().contains_key(&id)) {
        Vec::new()
    } else {
        return;
    };
    // #746: `type_params` (the *struct's* own params) may legitimately be
    // empty here -- this function is also the registration path for a method
    // that declares its own generics on an otherwise concrete target
    // (`extend Foo { fun describe<U: Aspect>(...) }`). Do not bail just
    // because the struct itself isn't generic; the per-method loop below
    // already folds each method's own `generics` into `quantified`/
    // `param_names` on top of whatever's here, empty or not.
    let generic_names = registry
        .struct_generic_names_for(current_module_path, target_name)
        .cloned()
        .unwrap_or_default();
    let mut type_gen_map: HashMap<String, TypeVar> = generic_names
        .iter()
        .cloned()
        .zip(type_params.iter().copied())
        .collect();
    // RFC-0121 item 2: an `extend<row R, row Rest> Session<..R>` block names its own
    // row generics. A row splice in the target (`..R`) is the struct's param at that
    // position, whatever the impl calls it; a row generic the target doesn't splice
    // (`Rest`) is an extra quantified var, pinned later by its decomposition equation.
    let mut impl_extra_row_vars: Vec<(String, TypeVar)> = Vec::new();
    if let crate::data::ast::TypeExpr::Named(_, target_args) = &ib.target_type {
        for (arg, &tv) in target_args.iter().zip(type_params.iter()) {
            if let crate::data::ast::TypeExpr::RowArg(tail) = arg
                && let Some(name) = tail.var.as_deref()
                && ib.generics.iter().any(|g| g.is_row && g.name == name)
            {
                type_gen_map.insert(name.to_string(), tv);
            }
        }
    }
    for g in ib.generics.iter().filter(|g| g.is_row) {
        if !type_gen_map.contains_key(&g.name) {
            let tv = type_var_gen.fresh();
            type_gen_map.insert(g.name.clone(), tv);
            impl_extra_row_vars.push((g.name.clone(), tv));
        }
    }
    // The impl's `where R = { labels.., ..Rest }` equations: a Row bound on `R`
    // and a remainder for `Rest`, exactly as for a free function.
    let mut impl_row_bounds: HashMap<TypeVar, Vec<GenericBound>> = HashMap::new();
    let mut impl_row_remainders: HashMap<TypeVar, (TypeVar, Vec<String>)> = HashMap::new();
    for eq in ib
        .where_clause
        .iter()
        .flat_map(|wc| wc.row_equations.iter())
    {
        let Some(&r_tv) = type_gen_map.get(eq.var.as_str()) else {
            continue;
        };
        impl_row_bounds
            .entry(r_tv)
            .or_default()
            .push(GenericBound::Row(
                crate::pipeline::type_checking::type_engine::RowConstraint {
                    fields: eq
                        .fields
                        .iter()
                        .map(|(label, ty)| {
                            crate::pipeline::type_checking::type_engine::RowConstraintField {
                                label: label.clone(),
                                ty: Some(ty.clone()),
                            }
                        })
                        .collect(),
                    open: true,
                },
            ));
        if let Some(&rest_tv) = eq
            .tail
            .var
            .as_deref()
            .and_then(|name| type_gen_map.get(name))
            && rest_tv != r_tv
        {
            impl_row_remainders.insert(
                rest_tv,
                (r_tv, eq.fields.iter().map(|(l, _)| l.clone()).collect()),
            );
        }
    }
    // RFC-0036: compute impl-level bounds from the impl block's generics + where clause.
    let synth = synth_generics_for_impl(
        &generic_names,
        &impl_generics_with_row_aliases(ib, &generic_names),
    );
    let impl_bounds = collect_type_param_bounds(&synth, ib.where_clause.as_ref());
    let impl_neg_bounds = collect_negative_type_param_bounds(&synth, ib.where_clause.as_ref());
    // RFC-0121 item 5: an impl-level `row R: { .. }` / `record T: { .. }` bound is only
    // checkable on a record-kinded param (`check_record_kind_requirement`), and that
    // kind must travel on each method's scheme, not just the method's own generics.
    let impl_record_kinds = collect_type_param_record_kinds(&synth, ib.where_clause.as_ref());
    let by_var: HashMap<TypeVar, Vec<GenericBound>> = type_params
        .iter()
        .zip(impl_bounds.iter())
        .filter(|(_, b)| !b.is_empty())
        .map(|(&tv, b)| (tv, b.clone()))
        .collect();
    let by_neg_var: HashMap<TypeVar, Vec<GenericBound>> = type_params
        .iter()
        .zip(impl_neg_bounds.iter())
        .filter(|(_, b)| !b.is_empty())
        .map(|(&tv, b)| (tv, b.clone()))
        .collect();
    let self_ty = InferType::Named(
        target_name.to_string(),
        type_params.iter().map(|tv| InferType::Var(*tv)).collect(),
        crate::data::types::NominalId::NONE,
    );
    for method in &ib.methods {
        // Only instance methods (those with a receiver) dispatch through the
        // method scheme env; static methods become joined-key schemes elsewhere.
        let Some(receiver) = method.params.first().and_then(|p| p.receiver.clone()) else {
            continue;
        };
        // metel-core#1124: the method tables are keyed by the target's own
        // `SymbolId`. `target_id` was resolved once above; if the target
        // somehow isn't resolvable (shouldn't happen for a legitimate `extend`
        // whose target type-checked), there is no id to register these
        // methods under -- skip rather than inventing one.
        let Some(owner) = target_id else {
            continue;
        };
        // Method-level generics (e.g. `U` in `fun map<U>`) get their own fresh
        // quantified vars in addition to the type's params.
        let mut gen_map = type_gen_map.clone();
        let mut quantified = type_params.clone();
        let mut param_names = generic_names.clone();
        for (name, tv) in &impl_extra_row_vars {
            quantified.push(*tv);
            param_names.push(name.clone());
        }
        for g in &method.generics {
            let tv = type_var_gen.fresh();
            gen_map.insert(g.name.clone(), tv);
            quantified.push(tv);
            param_names.push(g.name.clone());
        }
        // #746: the scheme's own `.bounds`/`.neg_bounds` (used for call-site
        // checking, e.g. `f.describe(bad_arg)`) previously only carried the
        // struct's/impl's bounds (`by_var`/`by_neg_var`, shared across every
        // method in this block) -- never a method's *own* bound. Merge this
        // method's own bounds in on a per-method copy; sharing the base maps
        // across methods but not mutating them keeps other methods in the
        // same impl block from seeing a bound that isn't theirs.
        let open_rows = desugar_method_open_row_params(method, type_var_gen);
        open_rows.quantify(&mut quantified, &mut param_names);
        let mut method_by_var = open_rows.merged_bounds(&by_var);
        for (tv, bounds) in &impl_row_bounds {
            method_by_var
                .entry(*tv)
                .or_default()
                .extend(bounds.iter().cloned());
        }
        for (tv, bounds) in super::inference::collect_fun_type_var_bounds(method, &gen_map) {
            method_by_var.entry(tv).or_default().extend(bounds);
        }
        let mut method_by_neg_var = by_neg_var.clone();
        for (tv, bounds) in super::inference::collect_negative_fun_type_var_bounds(method, &gen_map)
        {
            method_by_neg_var.entry(tv).or_default().extend(bounds);
        }
        let mut method_record_kinds =
            super::inference::collect_fun_type_var_record_kinds(method, &gen_map);
        method_record_kinds.extend(open_rows.record_kinds.iter().map(|(tv, k)| (*tv, *k)));
        for (tv, is_record) in type_params.iter().zip(&impl_record_kinds) {
            if *is_record {
                method_record_kinds.insert(*tv, true);
            }
        }
        // RFC-0121 §2: the impl's `where R = { .. }` bounds `R`, and a row bound
        // is only checkable on a record-kinded param (`check_record_kind_requirement`).
        for r_tv in impl_row_bounds.keys() {
            method_record_kinds.insert(*r_tv, true);
        }
        let mut param_types = vec![self_ty.clone()];
        for (i, p) in method
            .params
            .iter()
            .enumerate()
            .filter(|(_, p)| p.receiver.is_none())
        {
            if let Some(&tv) = open_rows.param_vars.get(&i) {
                param_types.push(InferType::Var(tv));
                continue;
            }
            let ann = p
                .type_ann
                .as_ref()
                .expect("declarations on generic types are fully annotated");
            param_types.push(type_expr_to_infer_with_generics(ann, &gen_map));
        }
        let ret_ty = method
            .return_type
            .as_ref()
            .map_or_else(InferType::unit, |ann| {
                type_expr_to_infer_with_generics(ann, &gen_map)
            });
        let scheme = TypeScheme {
            quantified_vars: quantified,
            param_names,
            bounds: vec![],
            neg_bounds: vec![],
            record_kinds: vec![],
            assoc_projections: vec![],
            assoc_eq_constraints: vec![],
            opaque_returns: vec![],
            open_row_params: vec![],
            row_remainders: vec![],
            ty: InferType::fun(param_types, ret_ty),
        }
        .with_bounds(&method_by_var)
        .with_neg_bounds(&method_by_neg_var)
        .with_record_kinds(&method_record_kinds)
        .with_open_row_params(&open_rows.vars)
        .with_row_remainders(&impl_row_remainders);
        // struct_tvars: only the type's params are pinned from the receiver;
        // method-level generics are recovered from the arguments at the call site.
        let struct_tvars = type_params.clone();
        registry.register_method_scheme(
            owner,
            method.name.clone(),
            scheme.clone(),
            struct_tvars.clone(),
        );
        registry.register_method_scheme_variant(
            owner,
            method.name.clone(),
            scheme,
            struct_tvars,
            ib.aspect_name.clone(),
            method.span.clone(),
        );
        registry.register_method_receiver(owner, method.name.clone(), receiver);
    }
}

/// RFC-0121 item 6: desugar an instance method's open-row-tailed parameters for
/// its registry-built scheme exactly as `infer_impl_method` does for its
/// inferred one -- a fresh, record-kinded, row-bounded quantified var standing
/// for the whole parameter (decomposition equations folded in, same code path).
/// An ill-formed row variable surfaces again, deterministically, from
/// `infer_impl_method`; here the parameter just gets an unconstrained var so
/// building the scheme never reaches the (unconvertible) `OpenRecord` node.
struct MethodOpenRowParams {
    param_vars: HashMap<usize, TypeVar>,
    bounds: HashMap<TypeVar, Vec<GenericBound>>,
    record_kinds: HashMap<TypeVar, bool>,
    vars: std::collections::HashSet<TypeVar>,
}

impl MethodOpenRowParams {
    /// Append this method's open-row vars to its scheme's quantified vars (with
    /// synthetic names, kept index-aligned with `quantified`).
    fn quantify(&self, quantified: &mut Vec<TypeVar>, param_names: &mut Vec<String>) {
        let mut vars: Vec<TypeVar> = self.vars.iter().copied().collect();
        vars.sort();
        for tv in vars {
            quantified.push(tv);
            param_names.push(format!("_OpenRow{}", tv.0));
        }
    }

    /// `base` plus this method's open-row bounds, on a per-method copy.
    fn merged_bounds(
        &self,
        base: &HashMap<TypeVar, Vec<GenericBound>>,
    ) -> HashMap<TypeVar, Vec<GenericBound>> {
        let mut merged = base.clone();
        for (tv, bounds) in &self.bounds {
            merged
                .entry(*tv)
                .or_default()
                .extend(bounds.iter().cloned());
        }
        merged
    }
}

fn desugar_method_open_row_params(
    method: &crate::data::ast::FunDecl,
    type_var_gen: &mut TypeVarGenerator,
) -> MethodOpenRowParams {
    let (mut param_vars, bounds, record_kinds, _tails) =
        super::inference::collect_open_record_param_vars_with(method, || type_var_gen.fresh())
            .unwrap_or_default();
    for (i, p) in method.params.iter().enumerate() {
        if matches!(p.type_ann, Some(TypeExpr::OpenRecord(..))) && !param_vars.contains_key(&i) {
            param_vars.insert(i, type_var_gen.fresh());
        }
    }
    let vars = param_vars.values().copied().collect();
    MethodOpenRowParams {
        param_vars,
        bounds,
        record_kinds,
        vars,
    }
}

fn register_array_impl_method_schemes(
    ib: &crate::data::ast::ImplBlock,
    type_var_gen: &mut TypeVarGenerator,
    registry: &mut TypeDefinitionRegistry,
) {
    let Some(element_name) = array_target_generic_name(ib) else {
        return;
    };
    let element_tv = type_var_gen.fresh();
    let mut type_gen_map = HashMap::new();
    type_gen_map.insert(element_name.to_string(), element_tv);
    let structural_self_type_expr =
        TypeExpr::Array(Box::new(TypeExpr::Named(element_name.to_string(), vec![])));
    let by_var: HashMap<TypeVar, Vec<GenericBound>> = std::iter::once(element_tv)
        .zip(collect_type_param_bounds(
            &ib.generics,
            ib.where_clause.as_ref(),
        ))
        .filter(|(_, b)| !b.is_empty())
        .collect();
    let by_neg_var: HashMap<TypeVar, Vec<GenericBound>> = std::iter::once(element_tv)
        .zip(collect_negative_type_param_bounds(
            &ib.generics,
            ib.where_clause.as_ref(),
        ))
        .filter(|(_, b)| !b.is_empty())
        .collect();
    let self_ty = InferType::Array(Box::new(InferType::Var(element_tv)));
    for method in &ib.methods {
        let Some(receiver) = method.params.first().and_then(|p| p.receiver.clone()) else {
            continue;
        };
        let mut gen_map = type_gen_map.clone();
        let mut quantified = vec![element_tv];
        let mut param_names = vec![element_name.to_string()];
        for g in &method.generics {
            let tv = type_var_gen.fresh();
            gen_map.insert(g.name.clone(), tv);
            quantified.push(tv);
            param_names.push(g.name.clone());
        }
        let open_rows = desugar_method_open_row_params(method, type_var_gen);
        open_rows.quantify(&mut quantified, &mut param_names);
        let method_by_var = open_rows.merged_bounds(&by_var);
        let mut param_types = vec![self_ty.clone()];
        for (i, p) in method
            .params
            .iter()
            .enumerate()
            .filter(|(_, p)| p.receiver.is_none())
        {
            if let Some(&tv) = open_rows.param_vars.get(&i) {
                param_types.push(InferType::Var(tv));
                continue;
            }
            let ann = p
                .type_ann
                .as_ref()
                .expect("declarations on structural array impls are fully annotated");
            let lowered = substitute_structural_self(ann, &structural_self_type_expr);
            param_types.push(type_expr_to_infer_with_generics(&lowered, &gen_map));
        }
        let ret_ty = method
            .return_type
            .as_ref()
            .map_or_else(InferType::unit, |ann| {
                let lowered = substitute_structural_self(ann, &structural_self_type_expr);
                type_expr_to_infer_with_generics(&lowered, &gen_map)
            });
        let scheme = TypeScheme {
            quantified_vars: quantified,
            param_names,
            bounds: vec![],
            neg_bounds: vec![],
            record_kinds: vec![],
            assoc_projections: vec![],
            assoc_eq_constraints: vec![],
            opaque_returns: vec![],
            open_row_params: vec![],
            row_remainders: vec![],
            ty: InferType::fun(param_types, ret_ty),
        }
        .with_bounds(&method_by_var)
        .with_neg_bounds(&by_neg_var)
        .with_record_kinds(&open_rows.record_kinds)
        .with_open_row_params(&open_rows.vars);
        registry.register_array_method_scheme(
            method.name.clone(),
            scheme.clone(),
            vec![element_tv],
        );
        registry.register_array_method_scheme_variant(
            method.name.clone(),
            scheme,
            vec![element_tv],
            ib.aspect_name.clone(),
            method.span.clone(),
        );
        registry.register_array_method_receiver(method.name.clone(), receiver);
    }
}

/// Register the method schemes of an `extend` on a record target. The receiver is one
/// quantified var carrying the impl's row condition as its bound and marked
/// record-kinded, so a call site matches a receiver through the ordinary bound check
/// and several impls of one aspect (disjoint rows) are separate candidates. Method
/// bodies are not inferred here: like every structural target, they are checked per
/// call against the concrete receiver (`impl_defers_method_bodies`).
fn register_record_impl_method_schemes(
    ib: &crate::data::ast::ImplBlock,
    row: &RowConstraint,
    type_var_gen: &mut TypeVarGenerator,
    registry: &mut TypeDefinitionRegistry,
) {
    let self_tv = type_var_gen.fresh();
    let mut type_gen_map = HashMap::new();
    type_gen_map.insert("Self".to_string(), self_tv);
    if let TypeExpr::OpenRecord(_, tail) = &ib.target_type
        && let Some(var) = tail.var.as_deref()
    {
        type_gen_map.insert(var.to_string(), self_tv);
    }
    let mut self_bounds = vec![GenericBound::Row(row.clone())];
    self_bounds.extend(record_target_all_fields(ib));
    let by_var: HashMap<TypeVar, Vec<GenericBound>> =
        std::iter::once((self_tv, self_bounds)).collect();
    let record_kinds: HashMap<TypeVar, bool> = std::iter::once((self_tv, true)).collect();
    let receiver_ty = InferType::Var(self_tv);
    for method in &ib.methods {
        let Some(receiver) = method.params.first().and_then(|p| p.receiver.clone()) else {
            continue;
        };
        let mut gen_map = type_gen_map.clone();
        let mut quantified = vec![self_tv];
        let mut param_names = vec!["Self".to_string()];
        for g in &method.generics {
            let tv = type_var_gen.fresh();
            gen_map.insert(g.name.clone(), tv);
            quantified.push(tv);
            param_names.push(g.name.clone());
        }
        let mut param_types = vec![receiver_ty.clone()];
        for p in method.params.iter().filter(|p| p.receiver.is_none()) {
            let ann = p
                .type_ann
                .as_ref()
                .expect("declarations on structural record impls are fully annotated");
            param_types.push(type_expr_to_infer_with_generics(ann, &gen_map));
        }
        let ret_ty = method
            .return_type
            .as_ref()
            .map_or_else(InferType::unit, |ann| {
                type_expr_to_infer_with_generics(ann, &gen_map)
            });
        let scheme = TypeScheme {
            quantified_vars: quantified,
            param_names,
            bounds: vec![],
            neg_bounds: vec![],
            record_kinds: vec![],
            assoc_projections: vec![],
            assoc_eq_constraints: vec![],
            opaque_returns: vec![],
            open_row_params: vec![],
            row_remainders: vec![],
            ty: InferType::fun(param_types, ret_ty),
        }
        .with_bounds(&by_var)
        .with_record_kinds(&record_kinds);
        registry.register_record_method_scheme_variant(
            method.name.clone(),
            scheme,
            vec![self_tv],
            ib.aspect_name.clone(),
            method.span.clone(),
        );
        registry.register_record_method_receiver(method.name.clone(), receiver);
    }
}

/// Register an `extend` on a record target: its methods as candidates, and (for a
/// positive impl) the row condition as a blanket impl so `T: Aspect` bounds hold for
/// exactly the records the condition accepts.
fn register_record_target_impl(
    ib: &crate::data::ast::ImplBlock,
    row: &RowConstraint,
    type_var_gen: &mut TypeVarGenerator,
    registry: &mut TypeDefinitionRegistry,
) {
    if ib.polarity != Polarity::Positive {
        return;
    }
    register_record_impl_method_schemes(ib, row, type_var_gen, registry);
    if let Some(aspect_name) = &ib.aspect_name {
        let mut pos = vec![GenericBound::Row(row.clone())];
        pos.extend(record_target_all_fields(ib));
        registry.register_bare_impl_bounds(aspect_name, vec![pos], vec![vec![]]);
    }
}

fn substitute_structural_self(te: &TypeExpr, replacement: &TypeExpr) -> TypeExpr {
    match te {
        TypeExpr::Named(name, args) if name == "Self" && args.is_empty() => replacement.clone(),
        TypeExpr::Named(name, args) => TypeExpr::Named(
            name.clone(),
            args.iter()
                .map(|arg| substitute_structural_self(arg, replacement))
                .collect(),
        ),
        TypeExpr::Unit => TypeExpr::Unit,
        TypeExpr::Tuple(items) => TypeExpr::Tuple(
            items
                .iter()
                .map(|item| substitute_structural_self(item, replacement))
                .collect(),
        ),
        TypeExpr::Record(fields) => TypeExpr::Record(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), substitute_structural_self(ty, replacement)))
                .collect(),
        ),
        TypeExpr::Array(inner) => TypeExpr::Array(Box::new(substitute_structural_self(
            inner.as_ref(),
            replacement,
        ))),
        TypeExpr::SizedArray(inner, len) => TypeExpr::SizedArray(
            Box::new(substitute_structural_self(inner.as_ref(), replacement)),
            *len,
        ),
        TypeExpr::Reference(inner) => TypeExpr::Reference(Box::new(substitute_structural_self(
            inner.as_ref(),
            replacement,
        ))),
        TypeExpr::MutReference(inner) => TypeExpr::MutReference(Box::new(
            substitute_structural_self(inner.as_ref(), replacement),
        )),
        TypeExpr::Fun {
            params,
            return_type: ret,
            call_multiplicity,
            call_mutation,
        } => TypeExpr::Fun {
            params: params
                .iter()
                .map(|param| substitute_structural_self(param, replacement))
                .collect(),
            return_type: ret
                .as_ref()
                .map(|ret_ty| Box::new(substitute_structural_self(ret_ty.as_ref(), replacement))),
            call_multiplicity: *call_multiplicity,
            call_mutation: *call_mutation,
        },
        TypeExpr::ImplAspect {
            bound,
            source_spell,
            span,
        } => TypeExpr::ImplAspect {
            bound: Box::new(substitute_structural_self(bound.as_ref(), replacement)),
            source_spell: source_spell.clone(),
            span: span.clone(),
        },
        TypeExpr::Projection {
            base,
            assoc_name,
            span,
        } => TypeExpr::Projection {
            base: Box::new(substitute_structural_self(base.as_ref(), replacement)),
            assoc_name: assoc_name.clone(),
            span: span.clone(),
        },
        TypeExpr::RecordProjection { path, fields, span } => TypeExpr::RecordProjection {
            path: path.clone(),
            fields: fields.clone(),
            span: span.clone(),
        },
        TypeExpr::DynAspect { bound, span } => TypeExpr::DynAspect {
            bound: Box::new(substitute_structural_self(bound.as_ref(), replacement)),
            span: span.clone(),
        },
        // RFC-0121: grammar-legal on a method's parameter too, but
        // `parse_fun_decl` itself rejects it there at parse time
        // (LIMIT-TYPES-001) -- a structural array-impl method's own type
        // expressions, the only thing this function processes, can
        // therefore never actually contain one.
        // RFC-0121 item 6: a method's record-tail parameter can name `Self`
        // in a field type (`{ x: Self, ..R }`) like a closed record can.
        TypeExpr::OpenRecord(fields, tail) => TypeExpr::OpenRecord(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), substitute_structural_self(ty, replacement)))
                .collect(),
            tail.clone(),
        ),
        // RFC-0121 installment 2: same restriction as `OpenRecord` above.
        TypeExpr::OpenRecordProjection { .. } => {
            unreachable!("parse_fun_decl rejects OpenRecordProjection on a method's parameter")
        }
        // RFC-0121 item 2 (metel-core#1310), representation-only slice:
        // `Session<..R>` -- unlike `OpenRecord`/`OpenRecordProjection`, this
        // *can* appear in a structural array-impl method's own parameter
        // type, parsed before `projections::check` gets a chance to reject
        // it. A row splice carries no `Self` reference to substitute.
        TypeExpr::RowArg(_) => te.clone(),
    }
}

fn register_impl_methods<'a>(
    methods: impl Iterator<Item = &'a crate::data::ast::FunDecl>,
    target_name: &str,
    current_module_path: &[String],
    type_var_gen: &mut TypeVarGenerator,
    registry: &mut TypeDefinitionRegistry,
) {
    // `self` on a primitive target must be the concrete primitive type
    // (e.g. Concrete(I32), not Named("i32")) so call sites unify (METEL-181).
    let self_ty = || {
        super::inference::primitive_type_from_name(target_name).map_or_else(
            || {
                InferType::Named(
                    target_name.to_string(),
                    vec![],
                    crate::data::types::NominalId::NONE,
                )
            },
            InferType::Concrete,
        )
    };
    // metel-core#1124: the method tables are keyed by the target's own
    // `SymbolId` -- resolved once here (covers both nominal structs/enums and
    // std::core's pre-seeded primitive ids). If the target somehow isn't
    // resolvable, there is no id to register these methods under; skip
    // rather than inventing one.
    let Some(owner) = registry.resolve_type_id(current_module_path, target_name) else {
        return;
    };
    for method in methods {
        let mut param_types = vec![];
        for p in &method.params {
            let pt = if p.name == "self" {
                self_ty()
            } else if matches!(p.type_ann, Some(TypeExpr::OpenRecord(..))) {
                // RFC-0121 item 6: a record-tail parameter has no concrete
                // type to pre-register; `infer_impl_method` replaces this
                // provisional entry with the real, row-bounded scheme.
                InferType::Var(type_var_gen.fresh())
            } else if let Some(ann) = &p.type_ann {
                type_expr_to_infer_with_self(ann, target_name)
            } else {
                InferType::Var(type_var_gen.fresh())
            };
            param_types.push(pt);
        }
        let ret_ty = method
            .return_type
            .as_ref()
            .map_or_else(InferType::unit, |ann| {
                type_expr_to_infer_with_self(ann, target_name)
            });
        registry.register_method(
            owner,
            method.name.clone(),
            InferType::fun(param_types, ret_ty),
        );
        if let Some(receiver) = method.params.first().and_then(|p| p.receiver.clone()) {
            registry.register_method_receiver(owner, method.name.clone(), receiver);
        }
    }
}

fn register_default_aspect_methods(
    ib: &crate::data::ast::ImplBlock,
    target_name: &str,
    type_var_gen: &mut TypeVarGenerator,
    registry: &mut TypeDefinitionRegistry,
    current_module_path: &[String],
) {
    let Some(aspect_name) = &ib.aspect_name else {
        return;
    };
    let Some(methods) = registry
        .aspect_method_defs_in(current_module_path, aspect_name)
        .cloned()
    else {
        return;
    };
    let provided: std::collections::HashSet<&str> =
        ib.methods.iter().map(|m| m.name.as_str()).collect();

    for method in methods {
        if method.default_body.is_none() || provided.contains(method.name.as_str()) {
            continue;
        }
        register_default_aspect_method(
            &method,
            target_name,
            aspect_name,
            type_var_gen,
            registry,
            current_module_path,
        );
    }
}

fn register_default_aspect_method(
    method: &AspectMethod,
    target_name: &str,
    aspect_name: &str,
    type_var_gen: &mut TypeVarGenerator,
    registry: &mut TypeDefinitionRegistry,
    current_module_path: &[String],
) {
    // RFC-0082 §1.2: bare associated-type names inside the aspect's own method
    // signatures (e.g. `Item` in `fun get_twice(self) -> Item { ... }`, sugar for
    // `Self::Item`) must resolve to the concrete binding this specific impl gave
    // for `Item`, not fall through to a dangling `Named("Item", [])`.
    // metel-core#1124: see `register_impl_methods`'s matching comment.
    let Some(owner) = registry.resolve_type_id(current_module_path, target_name) else {
        return;
    };
    let assoc_ctx = AssocResolveCtx {
        registry,
        current_module: current_module_path,
        current_aspect: Some(aspect_name),
    };
    let empty_generics = std::collections::HashMap::new();
    let mut param_types = vec![];
    for p in &method.params {
        let pt = if p.name == "self" {
            super::inference::primitive_type_from_name(target_name).map_or_else(
                || {
                    InferType::Named(
                        target_name.to_string(),
                        vec![],
                        crate::data::types::NominalId::NONE,
                    )
                },
                InferType::Concrete,
            )
        } else if let Some(ann) = &p.type_ann {
            type_expr_to_infer_with_assoc_ctx(ann, &empty_generics, Some(target_name), &assoc_ctx)
        } else {
            InferType::Var(type_var_gen.fresh())
        };
        param_types.push(pt);
    }
    let ret_ty = method
        .return_type
        .as_ref()
        .map_or_else(InferType::unit, |ann| {
            type_expr_to_infer_with_assoc_ctx(ann, &empty_generics, Some(target_name), &assoc_ctx)
        });
    registry.register_method(
        owner,
        method.name.clone(),
        InferType::fun(param_types, ret_ty),
    );
    if let Some(receiver) = method.params.first().and_then(|p| p.receiver.clone()) {
        registry.register_method_receiver(owner, method.name.clone(), receiver);
    }
}

/// Seed `ctx` with all built-in free-function bindings from `CorePrelude`,
/// plus built-in method registrations and aspect declarations.
pub(super) fn register_primitive_type_bindings(
    ctx: &mut InferContext,
    prelude: &super::CorePrelude,
) {
    // Free-function builtins all come from CorePrelude — no separate list needed.
    for (name, scheme) in prelude.schemes() {
        ctx.bind_poly_if_absent(name, scheme.clone());
    }

    // The primitive Display/From impls (to_string, the numeric From
    // cross-product, Char ↔ u32) are declared in the embedded std::core source
    // and registered by build_registry's impl-decl pass (METEL-181).
    // String::len is declared in the embedded std::core source (`impl String`)
    // and registered by build_registry's impl-decl pass.
    // T[]::len — handled as a special case in the typechecker; no TypeVar needed here.

    // The core aspects (Display/Iterable/From) are declared in the embedded
    // std::core source and registered by build_registry's decl pass (METEL-181).
}

/// Add all built-in function schemes from `CorePrelude` to `scheme_env`.
/// Used by the construction pass so builtin names are known during typed-AST building.
pub(super) fn register_builtin_schemes(
    scheme_env: &mut HashMap<String, TypeScheme>,
    prelude: &super::CorePrelude,
) {
    for (name, scheme) in prelude.schemes() {
        scheme_env
            .entry(name.clone())
            .or_insert_with(|| scheme.clone());
    }
}

/// Populate `map` with all built-in function schemes.
/// Called by `CorePrelude::default()` — this is the single canonical list.
pub(super) fn populate_std_schemes(
    map: &mut HashMap<String, TypeScheme>,
    type_var_gen: &mut TypeVarGenerator,
) {
    // All schemes — free functions and the List<T> static constructors — are
    // derived from the embedded std::core source (single source of truth,
    // METEL-181).
    populate_schemes_from_embedded_core(map, type_var_gen);
}
