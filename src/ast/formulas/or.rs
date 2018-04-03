use ast::prelude::*;

pub mod prelude {
    pub use super::{
        Or
    };
}

mod marker {
    use ast::prelude::*;
    use ast::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct OrMarker;

    impl ExprMarker for OrMarker {
        const EXPR_KIND: ExprKind = ExprKind::Or;
    }
}

/// Or formula expression.
/// 
/// Represents boolean disjunction for all boolean child expressions.
pub type Or = NaryBoolExpr<marker::OrMarker>;

impl From<Or> for AnyExpr {
    fn from(expr: Or) -> AnyExpr {
        AnyExpr::Or(expr)
    }
}
