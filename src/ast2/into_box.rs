use ast2::prelude::*;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        IntoBoxExpr
    };
}

/// Utility trait to transform `AnyExpr` or `Box<AnyExpr>` into `Box<AnyExpr>` and
/// without unboxing the input in the `Box<AnyExpr>` case.
pub trait IntoBoxExpr {
    /// Puts `self` into a `Box` if it isn't already boxed.
    fn into_box_expr(self) -> Box<AnyExpr>;
}

impl IntoBoxExpr for Box<AnyExpr> {
    /// Simply forwards the boxed `T`.
    /// 
    /// This is the "cheap" static case.
    fn into_box_expr(self) -> Box<AnyExpr> {
        self
    }
}

impl IntoBoxExpr for AnyExpr {
    /// Puts `T` into a box.
    /// 
    /// This is the "expensive" static case.
    fn into_box_expr(self) -> Box<AnyExpr> {
        Box::new(self)
    }
}
