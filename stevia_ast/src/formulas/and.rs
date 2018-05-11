use crate::prelude::*;

pub mod prelude {
    pub use super::{
        And
    };
}

mod marker {
    use crate::prelude::*;
    use crate::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct AndMarker;

    impl ExprMarker for AndMarker {
        const EXPR_KIND: ExprKind = ExprKind::And;
    }
}

/// And formula expression.
/// 
/// Represents boolean conjunction for all boolean child expressions.
pub type And = NaryBoolExpr<marker::AndMarker>;

impl From<And> for AnyExpr {
    fn from(expr: And) -> AnyExpr {
        AnyExpr::And(expr)
    }
}
