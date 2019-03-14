use crate::expr::utils::NaryTermExpr;

mod marker {
    use crate::prelude::*;
    use crate::ExprMarker;

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
