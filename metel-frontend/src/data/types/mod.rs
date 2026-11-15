/// A nominal type's resolved declaration identity, carried on `Type::Named`
/// (and `InferType::Named` in `type_engine`) as metadata (metel-core#1129,
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
/// [`crate::ownership::place::Projection::Field`]'s own `id: Option<FieldId>` (#1068):
/// resolved identity rides as metadata, the written name stays the
/// comparison key.
///
/// `None` is the explicit "not resolved (yet, or at all)" recovery state — a
/// value reconstructed with no resolver context, a structural/builtin type
/// with no interned declaration, or simply a call site that has not been
/// updated to populate it yet. Never a fabricated id.
#[derive(Debug, Clone, Default)]
pub struct NominalId(pub Option<crate::identity::symbols::SymbolId>);

impl NominalId {
    /// No known identity — the default, and the correct value at any call
    /// site that cannot (yet) resolve one.
    pub const NONE: NominalId = NominalId(None);

    #[must_use]
    pub fn some(id: crate::identity::symbols::SymbolId) -> Self {
        Self(Some(id))
    }

    #[must_use]
    pub fn get(&self) -> Option<crate::identity::symbols::SymbolId> {
        self.0
    }
}

impl PartialEq for NominalId {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl From<Option<crate::identity::symbols::SymbolId>> for NominalId {
    fn from(id: Option<crate::identity::symbols::SymbolId>) -> Self {
        Self(id)
    }
}

/// The canonical order of two row labels (RFC-0151): integer labels first, in numeric order (`.2` before `.10`),
/// then identifier labels in lexicographic order. Every place that keeps a row's fields in label order uses it, so
/// two rows with the same labels compare equal field by field.
#[must_use]
pub fn label_cmp(left: &str, right: &str) -> std::cmp::Ordering {
    fn integer(label: &str) -> Option<u64> {
        if !label.is_empty() && label.bytes().all(|byte| byte.is_ascii_digit()) {
            label.parse().ok()
        } else {
            None
        }
    }
    match (integer(left), integer(right)) {
        (Some(a), Some(b)) => a.cmp(&b).then_with(|| left.cmp(right)),
        (Some(_), None) => std::cmp::Ordering::Less,
        (None, Some(_)) => std::cmp::Ordering::Greater,
        (None, None) => left.cmp(right),
    }
}

/// Resolved types — produced by the type checker, consumed by the evaluator.
/// No type variables exist here; runtime generics have been monomorphised.
/// Ownership reconstruction may retain resolved symbolic row witnesses.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Boolean,
    Str,
    Char,
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
    Record(Vec<(String, Type)>),
    /// Ownership reconstruction retains an abstract row tail instead of pretending
    /// its unknown fields are absent. Runtime specializations normalize to Record.
    OpenRecord {
        fields: Vec<(String, Type)>,
        tail: Box<Type>,
    },
    /// A resolved ownership-only identity for unknown row fields. This is not a
    /// unification variable and must never be used as a concrete runtime type.
    SymbolicRow {
        name: String,
        field_aspects: Vec<String>,
        excluded_labels: Vec<String>,
        forbidden_fields: Vec<(String, Option<Type>)>,
    },
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
    /// `Residual`'s `fields` is always a strict (possibly empty) subset of the brand's own
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
    /// The unit type `()`: the empty closed row `.{}` (RFC-0231).
    #[must_use]
    pub fn unit() -> Self {
        Type::Record(Vec::new())
    }

    /// Whether this is a **`Tuple`** row (RFC-0151 section 5a): a closed row whose labels are exactly the integers
    /// `0 .. N-1`. Decided by inspecting the labels; the empty row is one. A row with a gap, an identifier label, or
    /// an open tail is not.
    #[must_use]
    pub fn is_tuple_row(&self) -> bool {
        matches!(self, Type::Record(fields)
            if fields
                .iter()
                .enumerate()
                .all(|(position, (label, _))| *label == position.to_string()))
    }

    /// Whether this is the unit type, the empty closed row.
    #[must_use]
    pub fn is_unit(&self) -> bool {
        matches!(self, Type::Record(fields) if fields.is_empty())
    }

    #[must_use]
    pub fn with_row_tail(fields: Vec<(String, Type)>, tail: Option<Box<Type>>) -> Self {
        match tail {
            Some(tail) if fields.is_empty() => *tail,
            Some(tail) => Self::OpenRecord { fields, tail },
            None => Self::Record(fields),
        }
    }

    #[must_use]
    pub fn row_tail(&self) -> Option<&Type> {
        match self {
            Self::OpenRecord { tail, .. } => Some(tail),
            Self::SymbolicRow { .. } => Some(self),
            _ => None,
        }
    }

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
            Type::Never => write!(f, "!"),
            Type::I8 => write!(f, "i8"),
            Type::I16 => write!(f, "i16"),
            Type::I32 => write!(f, "i32"),
            Type::U8 => write!(f, "u8"),
            Type::U16 => write!(f, "u16"),
            Type::U32 => write!(f, "u32"),
            Type::U64 => write!(f, "u64"),
            Type::F32 => write!(f, "f32"),
            // The empty closed row is the unit type (RFC-0231): one type, written `()`.
            Type::Record(fields) if fields.is_empty() => write!(f, "()"),
            Type::Record(fields) if is_dense_tuple_row(fields) => write_tuple_row(f, fields),
            Type::Record(fields) => {
                write!(f, ".{{ ")?;
                for (i, (name, ty)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, ".{name}: {ty}")?;
                }
                write!(f, " }}")
            }
            Type::OpenRecord { fields, tail } => fmt_open_record(f, fields, tail),
            Type::SymbolicRow { name, .. } => write!(f, "{name}"),
            Type::Array(t) => write!(f, "[{t}]"),
            Type::SizedArray(t, n) => write!(f, "[{t}; {n}]"),
            Type::Reference(t) => write!(f, "&{t}"),
            Type::MutReference(t) => write!(f, "&var {t}"),
            Type::Fun(params, ret, call_mult, use_mult, call_mutation) => {
                // RFC-0219: a copyable function type is written `copy |T| -> U`.
                if *use_mult == UseMultiplicity::Copy {
                    write!(f, "copy ")?;
                }
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
                    write!(f, ".{name}: {ty}")?;
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

fn fmt_open_record(
    f: &mut std::fmt::Formatter<'_>,
    fields: &[(String, Type)],
    tail: &Type,
) -> std::fmt::Result {
    write!(f, ".{{ ")?;
    for (name, ty) in fields {
        write!(f, ".{name}: {ty}, ")?;
    }
    write!(f, "..{tail} }}")
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod tuple_row_tests {
    use super::{Type, label_cmp};
    use std::cmp::Ordering;

    fn row(labels: &[&str]) -> Type {
        let mut fields: Vec<(String, Type)> = labels
            .iter()
            .map(|l| ((*l).to_string(), Type::I64))
            .collect();
        fields.sort_by(|a, b| label_cmp(&a.0, &b.0));
        Type::Record(fields)
    }

    #[test]
    fn integer_labels_come_first_in_numeric_order() {
        assert_eq!(label_cmp("2", "10"), Ordering::Less);
        assert_eq!(label_cmp("10", "x"), Ordering::Less);
        assert_eq!(label_cmp("x", "10"), Ordering::Greater);
        assert_eq!(label_cmp("a", "b"), Ordering::Less);
        let ordered = row(&["x", "10", "2", "0", "1"]);
        let Type::Record(fields) = ordered else {
            panic!()
        };
        let labels: Vec<&str> = fields.iter().map(|(l, _)| l.as_str()).collect();
        assert_eq!(labels, ["0", "1", "2", "10", "x"]);
    }

    #[test]
    fn a_tuple_row_has_exactly_the_labels_zero_to_n_minus_one() {
        assert!(row(&[]).is_tuple_row());
        assert!(row(&["0"]).is_tuple_row());
        assert!(row(&["0", "1", "2"]).is_tuple_row());
        assert!(row(&["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "10"]).is_tuple_row());
        assert!(!row(&["0", "2"]).is_tuple_row());
        assert!(!row(&["1"]).is_tuple_row());
        assert!(!row(&["0", "x"]).is_tuple_row());
        assert!(!Type::I64.is_tuple_row());
    }
}

/// RFC-0151: whether a closed row's labels are exactly `0 .. N-1` in order, the shape a tuple has. The empty row is
/// not counted: it is the unit type and prints as `()`.
#[must_use]
pub fn is_dense_tuple_row<T>(fields: &[(String, T)]) -> bool {
    !fields.is_empty()
        && fields
            .iter()
            .enumerate()
            .all(|(position, (label, _))| *label == position.to_string())
}

/// Write a dense row the way a tuple is written: `(A, B)`, and `(A,)` for one element.
///
/// # Errors
/// Propagates a formatter error.
pub fn write_tuple_row<T: std::fmt::Display>(
    f: &mut std::fmt::Formatter<'_>,
    fields: &[(String, T)],
) -> std::fmt::Result {
    write!(f, "(")?;
    for (index, (_, ty)) in fields.iter().enumerate() {
        if index > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{ty}")?;
    }
    if fields.len() == 1 {
        write!(f, ",")?;
    }
    write!(f, ")")
}
