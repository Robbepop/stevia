use crate::expr::utils::BinBoolExpr;

mod marker {
    use crate::{ExprKind, ExprMarker};

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
