use ast2::prelude::*;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        BitAnd
    };
}

mod marker {
    use ast2::prelude::*;
    use ast2::terms::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct BitAndMarker;

    impl ExprMarker for BitAndMarker {
        const EXPR_KIND: ExprKind = ExprKind::BitAnd;
    }
}

/// N-ary bitwise-and term expression for bitvector expressions.
/// 
/// Bitwise-and for all child term expressions.
pub type BitAnd = NaryTermExpr<marker::BitAndMarker>;

impl From<BitAnd> for AnyExpr {
    fn from(expr: BitAnd) -> AnyExpr {
        AnyExpr::BitAnd(expr)
    }
}
