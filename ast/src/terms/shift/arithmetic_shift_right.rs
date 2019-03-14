use crate::expr::utils::BinTermExpr;

mod marker {
    use crate::{ExprKind, ExprMarker};

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct ArithmeticShiftRightMarker;

    impl ExprMarker for ArithmeticShiftRightMarker {
        const EXPR_KIND: ExprKind = ExprKind::ArithmeticShiftRight;
    }
}

/// Binary arithmetic-shift-right term expression.
/// 
/// # Note
/// 
/// - Arithmetic shift-right respects the sign bit of the term expression.
/// - Shifting to left means shifting the bits of the term expression from
///   the most significant position to the least significant position.
pub type ArithmeticShiftRight = BinTermExpr<marker::ArithmeticShiftRightMarker>;
