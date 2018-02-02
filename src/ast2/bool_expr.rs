use ast2::prelude::*;

pub mod prelude {
    pub use super::{
        BoolExpr,
        WrapWithNot
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

/// Marker trait to mark n-ary expressions.
pub trait NaryExpr:
    ChildsVec +
    ChildsVecMut +
    IntoChildsVec
{}

/// Types implementing this trait allow to access their child expressions as vec.
pub trait ChildsVec {
    fn childs_vec(&self) -> &Vec<AnyExpr>;
}

/// Types implementing this trait allow to access their child expressions as vec mutably.
pub trait ChildsVecMut {
    fn childs_vec_mut(&mut self) -> &mut Vec<AnyExpr>;
}

/// Types implementing this trait allow to be transformed into a vec of their childs.
pub trait IntoChildsVec {
    fn into_childs_vec(self) -> Vec<AnyExpr>;
}
