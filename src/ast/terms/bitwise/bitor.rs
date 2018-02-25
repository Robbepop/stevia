use ast::prelude::*;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        BitOr
    };
}

mod marker {
    use ast::prelude::*;
    use ast::terms::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct BitOrMarker;

    impl ExprMarker for BitOrMarker {
        const EXPR_KIND: ExprKind = ExprKind::BitOr;
    }
}

/// N-ary bitwise-or term expression for bitvector expressions.
/// 
/// Bitwise-or for all child term expressions.
pub type BitOr = NaryTermExpr<marker::BitOrMarker>;

impl From<BitOr> for AnyExpr {
    fn from(expr: BitOr) -> AnyExpr {
        AnyExpr::BitOr(expr)
    }
}
