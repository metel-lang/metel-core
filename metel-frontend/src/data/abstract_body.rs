//! Definition-time types, distinct from mutable inference variables and runtime types.

use crate::data::ast::{Literal, Span};
use crate::data::types::{CallMultiplicity, CallMutation, NominalId, Type, UseMultiplicity};
use crate::identity::{BindingId, FieldId, SymbolId};
use crate::ownership::place::Projection;

/// The binder prevents equal parameter positions in different definitions from aliasing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AbstractParameterId {
    pub binder: BindingId,
    pub index: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AbstractType {
    /// The callable signature alone cannot describe environment ownership.
    Closure {
        signature: Box<Self>,
        owned_captures: Vec<Self>,
    },
    Concrete(Type),
    Parameter(AbstractParameterId),
    Never,
    Function {
        parameters: Vec<Self>,
        result: Box<Self>,
        call: CallMultiplicity,
        usage: UseMultiplicity,
        mutation: CallMutation,
    },
    Tuple(Vec<Self>),
    Record(Vec<(String, Self)>),
    OpenRecord {
        fields: Vec<(String, Self)>,
        tail: Box<Self>,
    },
    Array(Box<Self>),
    SizedArray(Box<Self>, u64),
    Reference(Box<Self>),
    MutReference(Box<Self>),
    Named {
        name: String,
        arguments: Vec<Self>,
        identity: NominalId,
    },
    Residual {
        brand: String,
        fields: Vec<(String, Self)>,
    },
    Dyn {
        aspect: String,
        arguments: Vec<Self>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct AbstractParameter {
    pub id: AbstractParameterId,
    /// Presentation metadata, never a consumer's semantic lookup key.
    pub name: Option<String>,
}

/// Signature foundation for ADR-0063, not yet a complete ownership-analysis artifact.
/// Declared facts and typed body operations are delivered separately under #273.
#[derive(Debug, Clone, PartialEq)]
pub struct AbstractSignature {
    pub binder: BindingId,
    pub parameters: Vec<AbstractParameter>,
    pub ty: AbstractType,
    /// `None` means this signature-only artifact does not yet have an entailment
    /// environment; consumers must not interpret absence as an empty set of grants.
    pub facts: Option<Vec<AbstractParameterFacts>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AbstractAspect {
    pub identity: SymbolId,
    pub name: String,
    pub arguments: Vec<AbstractType>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AbstractBound {
    Aspect(AbstractAspect),
    Row {
        fields: Vec<(String, Option<AbstractType>)>,
        open: bool,
    },
    AllFields {
        aspects: Vec<AbstractAspect>,
        except: Vec<String>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct AbstractAssociatedEquality {
    pub aspect: AbstractAspect,
    pub name: String,
    pub ty: AbstractType,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AbstractAssociatedProjection {
    pub base: AbstractParameterId,
    pub aspect: AbstractAspect,
    pub name: String,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AbstractRowRemainder {
    pub source: AbstractParameterId,
    pub removed: Vec<String>,
}

/// Removing no labels is a typed row equality. Both preparation and ownership
/// use its equivalence class, including synthesized open-row parameters.
pub(crate) fn equal_parameter_facts(
    facts: &[AbstractParameterFacts],
    parameter: AbstractParameterId,
) -> Vec<&AbstractParameterFacts> {
    let mut equal = std::collections::HashSet::from([parameter]);
    let mut pending = vec![parameter];
    while let Some(current) = pending.pop() {
        for fact in facts {
            for remainder in &fact.remainders {
                if !remainder.removed.is_empty() {
                    continue;
                }
                let other = if current == fact.parameter {
                    Some(remainder.source)
                } else if current == remainder.source {
                    Some(fact.parameter)
                } else {
                    None
                };
                if let Some(other) = other
                    && equal.insert(other)
                {
                    pending.push(other);
                }
            }
        }
    }
    facts
        .iter()
        .filter(|fact| equal.contains(&fact.parameter))
        .collect()
}

#[derive(Debug, Clone, PartialEq)]
pub struct AbstractParameterFacts {
    pub parameter: AbstractParameterId,
    pub record_kind: bool,
    /// A structural row variable, distinct from a possibly nominal record type.
    pub row_kind: bool,
    pub open_row_parameter: bool,
    pub positive: Vec<AbstractBound>,
    pub negative: Vec<AbstractBound>,
    pub associated_equalities: Vec<AbstractAssociatedEquality>,
    pub projection: Option<AbstractAssociatedProjection>,
    /// All origins of a solved associated result, including branch alternatives.
    pub projection_origins: Vec<AbstractAssociatedProjection>,
    pub opaque_return: Option<(AbstractAspect, Type)>,
    pub remainders: Vec<AbstractRowRemainder>,
}

/// A staged handoff is not a successful ownership check. Pending operations keep
/// the legacy analysis path until every semantic decision they need is retained.
#[derive(Debug, Clone)]
pub enum AbstractBodyPreparation {
    Typed(AbstractBody),
    Pending { reason: String },
}

#[derive(Debug, Clone)]
pub struct AbstractBody {
    pub binder: BindingId,
    pub parameters: Vec<AbstractBinding>,
    /// Source spelling is presentation metadata; consumers key state by identity.
    pub binding_names: std::collections::HashMap<BindingId, String>,
    pub nominal_ownership: Vec<AbstractNominalOwnership>,
    pub block: AbstractBlock,
}

/// Definition-time coherence facts. An unknown conditional result is not a
/// negative proof, especially for a destructor on an enclosing place.
#[derive(Debug, Clone)]
pub struct AbstractNominalOwnership {
    pub ty: AbstractType,
    pub copy: Option<bool>,
    pub drop: Option<bool>,
}

#[derive(Debug, Clone)]
pub struct AbstractBinding {
    pub identity: BindingId,
    pub name: String,
    pub ty: AbstractType,
}

#[derive(Debug, Clone)]
pub struct AbstractBlock {
    pub statements: Vec<AbstractStatement>,
    pub tail: Option<Box<AbstractExpr>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum AbstractStatement {
    DestructureRecord {
        pattern: AbstractRecordPattern,
        mutable: bool,
        value: AbstractExpr,
    },
    Bind {
        binding: AbstractBinding,
        mutable: bool,
        value: AbstractExpr,
    },
    Expr(AbstractExpr),
    While {
        condition: AbstractExpr,
        body: AbstractBlock,
        span: Span,
    },
    For {
        init: Option<Box<AbstractStatement>>,
        condition: Option<Box<AbstractExpr>>,
        step: Option<Box<AbstractExpr>>,
        body: AbstractBlock,
        span: Span,
    },
    ForIn {
        binding: AbstractBinding,
        iterable: AbstractExpr,
        mode: AbstractIterationMode,
        body: AbstractBlock,
        span: Span,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbstractIterationMode {
    BorrowedArrayElement,
    OwnedArrayElement,
}

#[derive(Debug, Clone)]
pub struct AbstractRecordPattern {
    pub bindings: Vec<AbstractBinding>,
    pub discarded: Vec<(String, AbstractType)>,
    pub remainder: Option<AbstractBinding>,
}

#[derive(Debug, Clone)]
pub struct AbstractExpr {
    pub ty: AbstractType,
    pub kind: AbstractExprKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum AbstractMatchPattern {
    Wildcard,
    Literal(Literal),
    Binding(AbstractBinding),
    Variant {
        identity: crate::identity::VariantId,
        bindings: Vec<(crate::identity::FieldId, AbstractBinding)>,
    },
}

#[derive(Debug, Clone)]
pub enum AbstractExprKind {
    Match {
        scrutinee: Box<AbstractExpr>,
        arms: Vec<(AbstractMatchPattern, AbstractBlock)>,
    },
    Binding(BindingId),
    Literal(Literal),
    /// A selected global/static callable is not an owned lexical binding.
    StaticMember {
        owner: SymbolId,
        member: String,
    },
    UnitVariant(crate::identity::VariantId),
    NumericCast(Box<AbstractExpr>),
    /// The built-in array length operation borrows an existing array, but
    /// evaluating an owned temporary still consumes its construction inputs.
    ArrayLength(Box<AbstractExpr>),
    Binary {
        operator: crate::data::ast::BinOp,
        left: Box<AbstractExpr>,
        right: Box<AbstractExpr>,
    },
    Unary {
        operator: crate::data::ast::UnaryOp,
        operand: Box<AbstractExpr>,
    },
    Tuple(Vec<AbstractExpr>),
    Array(Vec<AbstractExpr>),
    RepeatArray {
        value: Box<AbstractExpr>,
        length: u64,
    },
    /// A record construction preserves its explicit fields and the source
    /// position of an owned row spread. Consumers must not mistake an open
    /// spread for a closed record merely because inference knows its additions.
    RecordLiteral {
        fields: Vec<(String, AbstractExpr)>,
        spread: Option<(Box<AbstractExpr>, usize)>,
    },
    /// The nominal identity and instantiated arguments live in the enclosing
    /// expression type; this variant retains the evaluated field operations.
    StructLiteral {
        fields: Vec<(String, AbstractExpr)>,
    },
    /// A nominal record projection retains its source operation because the
    /// result may be a branded residual rather than an ordinary record.
    RecordProjection {
        source: Box<AbstractExpr>,
        fields: Vec<String>,
    },
    /// Rebinding retains the root binding and projected target place. The
    /// target type and selection evidence describe the assignment at the
    /// definition site rather than reconstructing it from the RHS.
    Assign {
        operator: crate::data::ast::AssignOp,
        target: BindingId,
        projections: Vec<Projection>,
        target_type: AbstractType,
        selection: Option<AbstractFieldSelection>,
        inputs: Vec<AbstractExpr>,
        value: Box<AbstractExpr>,
    },
    Closure(AbstractClosure),
    Return(Option<Box<AbstractExpr>>),
    If {
        condition: Box<AbstractExpr>,
        then_branch: AbstractBlock,
        else_branch: Option<AbstractBlock>,
    },
    Loop(AbstractBlock),
    Break(Option<Box<AbstractExpr>>),
    Continue,
    Borrow {
        value: Box<AbstractExpr>,
        mutable: bool,
        temporary: bool,
    },
    Dereference(Box<AbstractExpr>),
    Index {
        object: Box<AbstractExpr>,
        index: Box<AbstractExpr>,
        auto_dereferences: usize,
    },
    TupleAccess {
        object: Box<AbstractExpr>,
        index: usize,
        auto_dereferences: usize,
    },
    Call(AbstractCall),
    FieldAccess {
        object: Box<AbstractExpr>,
        selection: AbstractFieldSelection,
        auto_dereferences: usize,
    },
    MethodCall(AbstractMethodCall),
}

#[derive(Debug, Clone)]
pub struct AbstractMethodCall {
    pub receiver: Box<AbstractExpr>,
    pub receiver_mode: AbstractReceiverMode,
    pub method: String,
    pub origin: AbstractMethodOrigin,
    pub signature: AbstractType,
    pub arguments: Vec<AbstractArgument>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbstractMethodOrigin {
    Aspect(SymbolId),
    Nominal(SymbolId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbstractReceiverMode {
    Value,
    SharedReference,
    MutableReference,
}

#[derive(Debug, Clone)]
pub enum AbstractFieldSelection {
    Nominal {
        label: String,
        field: FieldId,
    },
    Structural {
        label: String,
    },
    Granted {
        label: String,
        parameter: AbstractParameterId,
    },
}

#[derive(Debug, Clone)]
pub struct AbstractCall {
    pub callee: Box<AbstractExpr>,
    /// The solved, instantiated contract, not the callee's polymorphic scheme.
    pub signature: AbstractType,
    pub arguments: Vec<AbstractArgument>,
    pub auto_dereference: bool,
}

#[derive(Debug, Clone)]
pub struct AbstractArgument {
    pub value: AbstractExpr,
    pub mode: AbstractPassingMode,
}

#[derive(Debug, Clone)]
pub struct AbstractClosure {
    pub captures: Vec<AbstractCapture>,
    pub call: CallMultiplicity,
    pub mutation: CallMutation,
    pub parameters: Vec<AbstractBinding>,
    pub body: AbstractBlock,
}

#[derive(Debug, Clone)]
pub struct AbstractCapture {
    pub binding: BindingId,
    pub name: String,
    pub span: Span,
    pub mode: AbstractCaptureMode,
    /// The captured value's type at closure entry, before the closure body can
    /// narrow or reassign the enclosing binding.
    pub ty: AbstractType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbstractCaptureMode {
    Owned,
    ImplicitCopy,
    SharedReference,
    MutableReference,
    Clone,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbstractPassingMode {
    Value,
    SharedReference,
    MutableReference,
}

#[derive(Debug, Clone)]
pub struct AbstractPlace {
    pub binding: BindingId,
    pub projections: Vec<Projection>,
}

impl AbstractExpr {
    #[must_use]
    pub fn place(&self) -> Option<AbstractPlace> {
        match &self.kind {
            AbstractExprKind::Binding(binding) => Some(AbstractPlace {
                binding: *binding,
                projections: Vec::new(),
            }),
            AbstractExprKind::Dereference(object) => {
                let mut place = object.place()?;
                place.projections.push(Projection::Deref);
                Some(place)
            }
            AbstractExprKind::TupleAccess {
                object,
                index,
                auto_dereferences,
            } => {
                let mut place = object.place()?;
                place
                    .projections
                    .extend(std::iter::repeat_n(Projection::Deref, *auto_dereferences));
                place.projections.push(Projection::TupleIndex(*index));
                Some(place)
            }
            AbstractExprKind::Index {
                object,
                auto_dereferences,
                ..
            } => {
                let mut place = object.place()?;
                place
                    .projections
                    .extend(std::iter::repeat_n(Projection::Deref, *auto_dereferences));
                place.projections.push(Projection::OpaqueIndex);
                Some(place)
            }
            AbstractExprKind::FieldAccess {
                object,
                selection,
                auto_dereferences,
            } => {
                let mut place = object.place()?;
                place
                    .projections
                    .extend(std::iter::repeat_n(Projection::Deref, *auto_dereferences));
                let (label, id) = match selection {
                    AbstractFieldSelection::Nominal { label, field } => (label, Some(*field)),
                    AbstractFieldSelection::Structural { label }
                    | AbstractFieldSelection::Granted { label, .. } => (label, None),
                };
                place
                    .projections
                    .push(Projection::field_with_id(label.clone(), id));
                Some(place)
            }
            _ => None,
        }
    }
}
