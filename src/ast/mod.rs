//! Internal expression data structures and utilities associated to it.

mod any_expr;
mod arity;
mod binexpr_children;
mod traits;
mod child_iters;
mod context;
mod error;
mod expr_kind;
mod factory;
mod formulas;
mod ite;
mod symbol;
mod terms;
mod ty;
mod visitor;

#[macro_use]
mod transformer;

/// An abstraction over an indirection to an entitiy `T`.
pub type P<T> = Box<T>;

pub trait ExprMarker {
    /// The static kind of the expression.
    const EXPR_KIND: ExprKind;
}

pub use self::{
    context::{
        ArcContext,
        Context,
        ContextAnd,
        SymbolInterner,
        SymbolIdGenerator,
        TypeMap
    },
    error::{
        ExprError,
        ExprErrorKind,
        ExprResult,
        expect_matching_symbol_type
    },
    ty::{
        ArrayTy,
        BitvecTy,
        Type,
        TypeKind,
        TypeError,
        TypeErrorKind,
        TypeResult,
        HasType,
        common_ty,
        have_common_ty,
        expect_common_ty,
        expect_bool_ty,
        expect_array_ty,
        expect_bitvec_ty,
        expect_concrete_bitvec_ty,
        expect_common_bitvec_ty,
        expect_common_bitvec_ty_n
    },
    visitor::{
        VisitEvent,
        RecursiveTraverseVisitor,
        Visitor
    },
    binexpr_children::{
        BinExprChildren
    },
    ite::{
        IfThenElseChildren
    },
    child_iters::{
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
    },
    factory::{
        IntoAnyExprOrError,
        ExprTreeFactory,
        ExprTreeBuilder,
        PlainExprTreeBuilder
    },
    formulas::{
        BinBoolExpr,
        NaryBoolExpr
    },
    terms::{
        BitWidth,
        BinTermExpr,
        NaryTermExpr,
        ArrayReadChildren,
        CastError,
        CastErrorKind,
        CastResult,
        Bitvec,
        BitvecError,
        BitvecResult
    },
    any_expr::{
        AnyExpr,
        IntoBoxedAnyExpr
    },
    expr_kind::{
        ExprKind,
        HasKind,
        HasPriority
    },
    traits::{
        BoolExpr,
        WrapWithNot,
        UnaryExpr,
        SingleChild,
        NaryExpr,
        DedupChildren,
        SortChildren,
        RetainChildren
    },
    arity::{
        HasArity,
        recursive_arity,
        exceeds_recursive_arity
    },
    transformer::{
        TransformEffect,
        Transformer,
        TransformEvent,
        TransformOutcome,
        AnyExprTransformer,
        AutoImplAnyExprTransformer,
        TraverseTransformer,
        forward_transform_any_expr_into
    },
    symbol::{
        SymbolId,
        NamedSymbolId,
        GeneratedSymbolId
    }
};

/// Re-exports all expression types.
pub mod expr {
    pub use super::{
        ite::{
            IfThenElse
        },
        symbol::{
            Symbol
        },
        formulas::{
            BoolConst,
            BoolEquals,
            Not,
            And,
            Or,
            Xor,
            Implies
        },
        terms::{
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
        }
    };
}

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::*;
}
