//! Internal expression data structures and utilities associated to it.

mod arity;
mod child_iters;
mod binexpr_children;
mod factory;
mod ty;
mod expr_kind;
mod any_expr;
mod formulas;
mod terms;
mod ite;
mod symbol;
mod bool_expr;
mod visitor;

#[macro_use]
mod transformer;

/// An abstraction over an indirection to an entitiy `T`.
pub type P<T> = Box<T>;

pub use self::ty::{
    ArrayTy,
    BitvecTy,
    Type,
    TypeKind,
    TypeError,
    TypeResult,
    HasType,
    common_ty,
    have_common_ty,
    expect_bool_ty,
    expect_array_ty,
    expect_bitvec_ty,
    expect_concrete_bitvec_ty,
    expect_common_bitvec_ty,
    expect_common_bitvec_ty_n
};
pub use self::visitor::{
    VisitEvent,
    RecursiveTraverseVisitor,
    Visitor
};
pub use self::binexpr_children::{
    BinExprChildren
};
pub use self::ite::{
    IfThenElseChildren
};
pub use self::child_iters::{
    ChildrenIter,
    ChildrenIterMut,
    IntoChildrenIter,
    Children,
    ChildrenMut,
    IntoChildren,

    YieldEvent,
    AnyExprAndEvent,
    RecursiveChildrenIter,

    children_recursive_with_event,
    children_recursive_entering,
    children_recursive_leaving
};
pub use self::factory::{
    IntoAnyExprOrError,
    ExprTreeFactory,
    ExprTreeBuilder,
    PlainExprTreeBuilder
};
pub use self::formulas::{
    BinBoolExpr,
    NaryBoolExpr
};
pub use self::terms::{
    BitWidth,
    BinTermExpr,
    NaryTermExpr,
    ArrayReadChildren,
};
pub use self::any_expr::{
    AnyExpr,
    IntoBoxedAnyExpr
};
pub use self::expr_kind::{
    ExprKind,
    HasKind,
    HasPriority
};
pub use self::bool_expr::{
    BoolExpr,
    WrapWithNot,
    UnaryExpr,
    SingleChild,
    NaryExpr,
    DedupChildren,
    SortChildren,
    RetainChildren
};
pub use self::arity::{
    HasArity,
    recursive_arity,
    exceeds_recursive_arity
};
pub use self::transformer::{
    TransformEffect,
    Transformer,
    TransformEvent,
    TransformOutcome,
    AnyExprTransformer,
    AutoImplAnyExprTransformer,
    TraverseTransformer,
    forward_transform_any_expr_into
};

/// Re-exports all expression types.
pub mod expr {
    pub use super::ite::{
        IfThenElse
    };
    pub use super::symbol::{
        Symbol
    };
    pub use super::formulas::{
        BoolConst,
        BoolEquals,
        Not,
        And,
        Or,
        Xor,
        Implies
    };
    pub use super::terms::{
        BitvecConst,
        BitvecEquals,
        Neg,
        Add,
        Mul,
        Sub,
        UnsignedDiv,
        SignedDiv,
        SignedModulo,
        UnsignedRemainder,
        SignedRemainder,

        BitNot,
        BitAnd,
        BitOr,
        BitXor,

        SignedGreaterEquals,
        SignedGreaterThan,
        SignedLessEquals,
        SignedLessThan,
        UnsignedGreaterEquals,
        UnsignedGreaterThan,
        UnsignedLessEquals,
        UnsignedLessThan,

        ShiftLeft,
        LogicalShiftRight,
        ArithmeticShiftRight,

        Concat,
        Extract,
        SignExtend,
        ZeroExtend,

        ArrayRead,
        ArrayWrite
    };
}

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::*;
}
