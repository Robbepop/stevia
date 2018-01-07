use ast2::prelude::*;

pub mod prelude {
    pub use super::{
        Not
    };
}

/// The logical Not formula expression.
/// 
/// This negate the inner boolean expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Not {
    child: P<Expr>
}

impl Not {
    pub fn new<E>(child: E) -> Result<Not, String>
        where E: IntoBoxExpr
    {
        let child = child.into_box_expr();
        if child.ty() != Type::Bool {
            return Err("Requires inner expression to be of boolean type for Not formula expression.".into())
        }
        Ok(Not{child})
    }
}
