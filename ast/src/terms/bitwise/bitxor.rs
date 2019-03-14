use crate::expr::utils::BinTermExpr;

mod marker {
    use crate::{ExprKind, ExprMarker};

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct BitXorMarker;

    impl ExprMarker for BitXorMarker {
        const EXPR_KIND: ExprKind = ExprKind::BitXor;
    }
}

/// Binary bitwise-xor term expression.
pub type BitXor = BinTermExpr<marker::BitXorMarker>;
