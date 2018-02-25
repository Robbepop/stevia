use ast::prelude::*;

use std::cmp::Ordering;

pub mod prelude {
    pub use super::{
        BoolExpr,
        WrapWithNot,
        UnaryExpr,
        SingleChild,
        NaryExpr,
        DedupChildren,
        SortChildren
    };
}

/// Marker trait to mark boolean expressions.
/// 
/// This automatically implements methods on them that are safe for boolean expressions.
pub trait BoolExpr: WrapWithNot {}

/// Expressions that can be safely wrapped with a `Not` expression.
/// 
/// # Note
/// 
/// This trait is automatically implemented for all types that implement `BoolExpr`.
pub trait WrapWithNot {
    /// Wraps the given boolean expression with a not-expression.
    /// 
    /// This does not need to be type checked since this method is only available
    /// for boolean expressions.
    fn wrap_with_not(self) -> expr::Not;
}

impl<T> WrapWithNot for T where T: BoolExpr + IntoBoxedAnyExpr {
    fn wrap_with_not(self) -> expr::Not {
        unsafe{ expr::Not::new_unchecked(self.into_boxed_any_expr()) }
    }
}

/// Marker trait to mark unary expressions.
pub trait UnaryExpr: SingleChild {}

/// Types implementing this trait allow to query or take their single child expression.
pub trait SingleChild {
    /// Returns a shared reference to the only child expression.
    fn single_child(&self) -> &AnyExpr;
    /// Returns a mutable reference to the only child expression.
    fn single_child_mut(&mut self) -> &mut AnyExpr;
    /// Consumes `self` and returns its only child expression.
    fn into_single_child(self) -> AnyExpr;
    /// Consumes `self` and returns its only child expression in a box.
    /// 
    /// Use this to prevent unnecesary unboxing of unary child expressions.
    fn into_boxed_single_child(self) -> Box<AnyExpr>;
}

/// Marker trait to mark n-ary expressions.
pub trait NaryExpr:
    DedupChildren +
    SortChildren
{}

/// Types implementing this trait allow to deduplicate their child expressions.
pub trait DedupChildren {
    fn dedup_children(&mut self);
}

/// Types implementing this trait allow to sort their child expressions using the given comparator.
pub trait SortChildren {
    fn sort_children_by<F>(&mut self, comparator: F)
        where F: FnMut(&AnyExpr, &AnyExpr) -> Ordering;
}
