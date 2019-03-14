//! Internal expression data structures and utilities associated to it.

#![doc(html_root_url = "https://docs.rs/stevia_ast/0.1.0")]

// #![allow(missing_docs)]
// #![allow(dead_code)]

mod any_expr;
mod arity;
mod bin_children;
mod unit_child;
mod traits;
mod child_iters;
mod context;
mod error;
mod factory;
mod formulas;
mod ite;
mod symbol;
mod terms;
pub mod ty;
mod visitor;
mod consistency_checker;
mod writer;

#[macro_use]
pub mod transformer;

use std::fmt;

/// An abstraction over an indirection to an entitiy `T`.
pub type P<T> = Box<T>;

/// A simple marker to mark expression types as such
/// and provide them with an expression kind.
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
    factory::{
        IntoAnyExprOrError,
        ExprTreeFactory,
        ExprTreeBuilder,
        PlainExprTreeBuilder
    },
    terms::{
        CastError,
        CastErrorKind,
        CastResult,
    },
    any_expr::{
        AnyExpr,
        IntoBoxedAnyExpr,
		ExprKind,
		HasKind,
        HasPriority,
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
    symbol::{
        SymbolId,
        NamedSymbolId,
        GeneratedSymbolId
    },
    writer::{
        write_smtlib2
    }
};

/// Facilities to iterate over portions of stevia expressions.
pub mod iter {
    pub use super::{
        visitor::{
            VisitEvent,
            RecursiveTraverseVisitor,
            Visitor
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
    };
}

/// Re-exports all expression types.
pub mod expr {
    /// Utility data structures for expressions.
    pub mod utils {
        pub use super::super::{
            unit_child::{
                UnaryChild
            },
            bin_children::{
                BinaryChildren
            },
            ite::{
                IfThenElseChildren
            },
            formulas::{
                BinBoolExpr,
                NaryBoolExpr
            },
            terms::{
                BinTermExpr,
                NaryTermExpr,
                AnyExtendExpr,
                ExtendExpr,
                ComparisonExpr,
                ArrayReadChildren,
            },
        };
    }

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
