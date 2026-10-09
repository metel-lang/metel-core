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

#[derive(Debug, Clone, PartialEq)]
pub struct AbstractParameterFacts {
    pub parameter: AbstractParameterId,
    pub record_kind: bool,
    pub open_row_parameter: bool,
    pub positive: Vec<AbstractBound>,
    pub negative: Vec<AbstractBound>,
    pub associated_equalities: Vec<AbstractAssociatedEquality>,
    pub projection: Option<AbstractAssociatedProjection>,
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
    pub block: AbstractBlock,
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
}

#[derive(Debug, Clone)]
pub struct AbstractExpr {
    pub ty: AbstractType,
    pub kind: AbstractExprKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum AbstractExprKind {
    Binding(BindingId),
    Literal(Literal),
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
    /// Plain local rebinding restores the tracked binding. More elaborate
    /// assignment places remain pending until their own selection facts are
    /// retained.
    Assign {
        target: BindingId,
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
    pub aspect: SymbolId,
    pub signature: AbstractType,
    pub arguments: Vec<AbstractArgument>,
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
    pub mode: AbstractCaptureMode,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbstractCaptureMode {
    Owned,
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
