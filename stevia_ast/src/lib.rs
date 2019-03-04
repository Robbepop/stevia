//! Internal expression data structures and utilities associated to it.

#![doc(html_root_url = "https://docs.rs/stevia_ast/0.1.0")]

// #![allow(missing_docs)]
// #![allow(dead_code)]

extern crate apint;
extern crate smallvec;
extern crate string_interner;
extern crate vec_map;

#[macro_use]
extern crate log;

#[macro_use]
extern crate indoc;

mod any_expr;
mod arity;
mod bin_children;
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
mod consistency_checker;
mod writer;

#[macro_use]
mod transformer;

use std::fmt;

/// An abstraction over an indirection to an entitiy `T`.
pub type P<T> = Box<T>;

pub trait ExprMarker: fmt::Debug + Copy + Clone + PartialEq + Eq {
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
    consistency_checker::{
        AssertConsistency,
        assert_consistency_recursively
    },
    error::{
        ExprError,
        ExprErrorKind,
        ExprResult
    },
    ty::{
        HasType,
        ArrayTy,
        BitvecTy,
        Type,
        TypeKind,

        TypeError,
        TypeErrorKind,
        TypeResult,

        expect_common_ty,
        expect_array_ty,
        expect_bitvec_ty,
        expect_type,
        expect_common_bitvec_ty,
        expect_common_bitvec_ty_n,

    },
    visitor::{
        VisitEvent,
        RecursiveTraverseVisitor,
        Visitor
    },
    bin_children::{
        BinaryChildren
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
        AnyExtendExpr,
        ExtendExpr,
        ComparisonExpr,
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
        RetainChildren,
        BinaryExpr
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
    },
    writer::{
        write_smtlib2
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
