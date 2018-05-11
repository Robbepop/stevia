use crate::prelude::*;

pub mod prelude {
    pub use super::{
        BitXor
    };
}

mod marker {
    use crate::prelude::*;
    use crate::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct BitXorMarker;

    impl ExprMarker for BitXorMarker {
        const EXPR_KIND: ExprKind = ExprKind::BitXor;
    }
}

/// Binary bitwise-xor term expression.
pub type BitXor = BinTermExpr<marker::BitXorMarker>;

impl From<BitXor> for AnyExpr {
    fn from(expr: BitXor) -> AnyExpr {
        AnyExpr::BitXor(expr)
    }
}
