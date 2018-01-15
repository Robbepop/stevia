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
pub trait BoolExpr {}

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
