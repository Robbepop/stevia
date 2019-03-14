use crate::expr::utils::BinTermExpr;

mod marker {
    use crate::{ExprKind, ExprMarker};

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
