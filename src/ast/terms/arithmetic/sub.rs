use ast::prelude::*;

pub mod prelude {
    pub use super::{
        Sub
    };
}

mod marker {
    use ast::prelude::*;
    use ast::terms::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct SubMarker;

    impl ExprMarker for SubMarker {
        const EXPR_KIND: ExprKind = ExprKind::Sub;
    }
}

/// Binary subtraction term expression.
/// 
/// Subtracts the right child from the left: left - right
pub type Sub = BinTermExpr<marker::SubMarker>;

impl From<Sub> for AnyExpr {
    fn from(expr: Sub) -> AnyExpr {
        AnyExpr::Sub(expr)
    }
}
