use crate::prelude::*;

pub mod prelude {
    pub use super::{
        Implies
    };
}

mod marker {
    use crate::prelude::*;
    use crate::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct ImpliesMarker;

    impl ExprMarker for ImpliesMarker {
        const EXPR_KIND: ExprKind = ExprKind::Implies;
    }
}

/// Implies formula binary expression.
/// 
/// This is equal to the implication of the boolean logic.
pub type Implies = BinBoolExpr<marker::ImpliesMarker>;

impl From<Implies> for AnyExpr {
    fn from(expr: Implies) -> AnyExpr {
        AnyExpr::Implies(expr)
    }
}
