use crate::expr::utils::NaryTermExpr;

mod marker {
    use crate::prelude::*;
    use crate::ExprMarker;

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
