/// A nominal type's resolved declaration identity, carried on `Type::Named`
/// (and `InferType::Named` in `typeinference`) as metadata (metel-core#1129,
/// groundwork for #1053).
///
/// **Deliberately excluded from `Type`'s equality** — its `PartialEq` impl
/// always returns `true`, so `Type`'s `#[derive(PartialEq)]` compares `Named`
/// variants exactly as it did before this field existed (name + args only).
/// Two `Type::Named` values naming the same spelling must keep comparing
/// equal even when only one of them has had its identity resolved; making
/// resolution success/failure observable through equality would make
/// unification and exhaustiveness checking spuriously reject programs that
/// type-checked before this field existed. This mirrors
/// [`crate::place::Projection::Field`]'s own `id: Option<FieldId>` (#1068):
/// resolved identity rides as metadata, the written name stays the
/// comparison key.
///
/// `None` is the explicit "not resolved (yet, or at all)" recovery state — a
/// value reconstructed with no resolver context, a structural/builtin type
/// with no interned declaration, or simply a call site that has not been
/// updated to populate it yet. Never a fabricated id.
#[derive(Debug, Clone, Default)]
pub struct NominalId(pub Option<crate::symbols::SymbolId>);

impl NominalId {
    /// No known identity — the default, and the correct value at any call
    /// site that cannot (yet) resolve one.
    pub const NONE: NominalId = NominalId(None);

    #[must_use]
    pub fn some(id: crate::symbols::SymbolId) -> Self {
        Self(Some(id))
    }

    #[must_use]
    pub fn get(&self) -> Option<crate::symbols::SymbolId> {
        self.0
    }
}

impl PartialEq for NominalId {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl From<Option<crate::symbols::SymbolId>> for NominalId {
    fn from(id: Option<crate::symbols::SymbolId>) -> Self {
        Self(id)
    }
}

/// Resolved types — produced by the type checker, consumed by the evaluator.
/// No type variables exist here; generics have been monomorphised.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Boolean,
    Str,
    Char,
    Unit,
    /// The bottom type `!`. Produced by expressions that never return (infinite
    /// loops with no reachable `break`, `return`, `panic!`). Coerces to any type.
    Never,
    // ── Sized integer types ───────────────────────────────────────────────────
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    // ── Sized float types ─────────────────────────────────────────────────────
    F32,
    F64,
    // ─────────────────────────────────────────────────────────────────────────
    Tuple(Vec<Type>),
    Record(Vec<(String, Type)>),
    Array(Box<Type>),
    SizedArray(Box<Type>, u64),
    Reference(Box<Type>),
    MutReference(Box<Type>),
    Fun(
        Vec<Type>,
        Box<Type>,
        CallMultiplicity,
        UseMultiplicity,
        CallMutation,
    ),
    /// A named type (struct, enum) with concrete type arguments after monomorphisation.
    /// The third field is the resolved declaration identity (metel-core#1129) —
    /// see [`NominalId`]'s doc for why it is excluded from equality.
    Named(String, Vec<Type>, NominalId),
    /// A narrowed residual of a struct's own row (RFC-0137, metel-core#857/#836) --
    /// `Handle.{ fd }`, produced by a struct's own field projection (`h.{ fd }`) when
    /// the projected fields are a genuine proper subset of the struct's declared row.
    /// Distinct from `Record`: a `Residual` carries the originating struct's brand and
    /// unifies only with another `Residual`/`Named` of the *same* brand, never with a
    /// same-shaped anonymous record -- that brand check is the entire point (RFC-0137
    /// §3's "eligibility" gate). `fields` is always lexicographically sorted by label,
    /// the same invariant `Record` maintains, so derived `PartialEq` compares
    /// correctly regardless of the source projection's written order. A projection
    /// naming *every* field the struct declares normalizes back to plain `Named`
    /// instead of constructing this variant (RFC-0137 §3's own worked example: a
    /// full-width projection is still just the struct, not a distinct form) -- so a
    /// `Residual`'s `fields` is always a strict, non-empty subset of the brand's own
    /// declared row.
    Residual {
        brand: String,
        fields: Vec<(String, Type)>,
    },
    /// `dyn Aspect` (RFC-0008, metel-core#865) -- an unsized existential type: the
    /// concrete type is erased, dispatch happens through a vtable. `aspect` names
    /// the principal (method-bearing) aspect; `type_args` are that aspect's own
    /// type arguments (`dyn Callable<i64, i64>` -> `["i64", "i64"]`). Unlike
    /// `Named`, this never refers to one concrete type -- unification is only ever
    /// against another `Dyn` of the same aspect and args, never against a `Named`
    /// concrete implementor (that asymmetry is what makes it existential).
    Dyn {
        aspect: String,
        type_args: Vec<Type>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum CallMultiplicity {
    Once,
    #[default]
    Many,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum UseMultiplicity {
    #[default]
    Move,
    Copy,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum CallMutation {
    #[default]
    Reading,
    Mutating,
}

#[must_use]
pub fn default_fun_type(params: Vec<Type>, ret: Type) -> Type {
    Type::Fun(
        params,
        Box::new(ret),
        CallMultiplicity::Many,
        UseMultiplicity::Copy,
        CallMutation::Reading,
    )
}

impl Type {
    /// Returns true if this is any integer type (signed or unsigned, any width).
    #[must_use]
    pub fn is_integer(&self) -> bool {
        matches!(
            self,
            Type::I64
                | Type::I8
                | Type::I16
                | Type::I32
                | Type::U8
                | Type::U16
                | Type::U32
                | Type::U64
        )
    }

    /// Returns true if this is any float type.
    #[must_use]
    pub fn is_float(&self) -> bool {
        matches!(self, Type::F64 | Type::F32)
    }

    /// Returns true if this is any numeric type (integer or float).
    #[must_use]
    pub fn is_numeric(&self) -> bool {
        self.is_integer() || self.is_float()
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::I64 => write!(f, "i64"),
            Type::F64 => write!(f, "f64"),
            Type::Boolean => write!(f, "boolean"),
            Type::Str => write!(f, "String"),
            Type::Char => write!(f, "Char"),
            Type::Unit => write!(f, "()"),
            Type::Never => write!(f, "!"),
            Type::I8 => write!(f, "i8"),
            Type::I16 => write!(f, "i16"),
            Type::I32 => write!(f, "i32"),
            Type::U8 => write!(f, "u8"),
            Type::U16 => write!(f, "u16"),
            Type::U32 => write!(f, "u32"),
            Type::U64 => write!(f, "u64"),
            Type::F32 => write!(f, "f32"),
            Type::Tuple(ts) => {
                write!(f, "(")?;
                for (i, t) in ts.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{t}")?;
                }
                write!(f, ")")
            }
            Type::Record(fields) => {
                write!(f, "{{ ")?;
                for (i, (name, ty)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{name}: {ty}")?;
                }
                write!(f, " }}")
            }
            Type::Array(t) => write!(f, "{t}[]"),
            Type::SizedArray(t, n) => write!(f, "[{t}; {n}]"),
            Type::Reference(t) => write!(f, "&{t}"),
            Type::MutReference(t) => write!(f, "&var {t}"),
            Type::Fun(params, ret, call_mult, _use_mult, call_mutation) => {
                if *call_mult == CallMultiplicity::Once {
                    write!(f, "once ")?;
                }
                if *call_mutation == CallMutation::Mutating {
                    write!(f, "var ")?;
                }
                write!(f, "|")?;
                for (i, t) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{t}")?;
                }
                write!(f, "| -> {ret}")
            }
            Type::Named(name, args, ..) => {
                write!(f, "{name}")?;
                if !args.is_empty() {
                    write!(f, "<")?;
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{a}")?;
                    }
                    write!(f, ">")?;
                }
                Ok(())
            }
            Type::Residual { brand, fields } => {
                write!(f, "{brand}.{{ ")?;
                for (i, (name, ty)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{name}: {ty}")?;
                }
                write!(f, " }}")
            }
            Type::Dyn { aspect, type_args } => {
                write!(f, "dyn {aspect}")?;
                if !type_args.is_empty() {
                    write!(f, "<")?;
                    for (i, a) in type_args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{a}")?;
                    }
                    write!(f, ">")?;
                }
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Type;

    #[test]
    fn mutable_reference_display_uses_language_spelling() {
        assert_eq!(
            Type::MutReference(Box::new(Type::I64)).to_string(),
            "&var i64"
        );
    }
}
