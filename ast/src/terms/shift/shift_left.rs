use crate::expr::utils::BinTermExpr;

mod marker {
    use crate::prelude::*;
    use crate::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct ShiftLeftMarker;

    impl ExprMarker for ShiftLeftMarker {
        const EXPR_KIND: ExprKind = ExprKind::ShiftLeft;
    }
}

/// Binary shift-left term expression.
/// 
/// # Note
/// 
/// Shifting to left means shifting the bits of the term expression from
/// the least significant position to the most significant position.
pub type ShiftLeft = BinTermExpr<marker::ShiftLeftMarker>;
