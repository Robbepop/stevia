use ast2::prelude::*;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        IntoBoxExpr
    };
}

/// Utility trait to transform `Expr` or `Box<Expr>` into `Box<Expr>` and
/// without unboxing the input in the `Box<Expr>` case.
pub trait IntoBoxExpr {
    /// Puts `self` into a `Box` if it isn't already boxed.
    fn into_box_expr(self) -> Box<Expr>;
}

impl IntoBoxExpr for Box<Expr> {
    /// Simply forwards the boxed `T`.
    /// 
    /// This is the "cheap" static case.
    fn into_box_expr(self) -> Box<Expr> {
        self
    }
}

impl IntoBoxExpr for Expr {
    /// Puts `T` into a box.
    /// 
    /// This is the "expensive" static case.
    fn into_box_expr(self) -> Box<Expr> {
        Box::new(self)
    }
}
