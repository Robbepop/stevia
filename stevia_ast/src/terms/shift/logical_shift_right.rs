use crate::prelude::*;

pub mod prelude {
    pub use super::{
        LogicalShiftRight
    };
}

mod marker {
    use crate::prelude::*;
    use crate::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct LogicalShiftRightMarker;

    impl ExprMarker for LogicalShiftRightMarker {
        const EXPR_KIND: ExprKind = ExprKind::LogicalShiftRight;
    }
}

/// Binary logical-shift-right term expression.
/// 
/// # Note
/// 
/// - Logical shift-right does not respect the sign bit of the term expression.
/// - Shifting to left means shifting the bits of the term expression from
///   the most significant position to the least significant position.
pub type LogicalShiftRight = BinTermExpr<marker::LogicalShiftRightMarker>;

impl From<LogicalShiftRight> for AnyExpr {
    fn from(expr: LogicalShiftRight) -> AnyExpr {
        AnyExpr::LogicalShiftRight(expr)
    }
}
