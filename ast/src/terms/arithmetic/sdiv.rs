use crate::expr::utils::BinTermExpr;

mod marker {
    use crate::prelude::*;
    use crate::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct SignedDivMarker;

    impl ExprMarker for SignedDivMarker {
        const EXPR_KIND: ExprKind = ExprKind::SignedDiv;
    }
}

/// Binary `SignedDiv` (signed division) term expression.
/// 
/// Divides the left child by the right: left / right
/// 
/// # Note
/// 
/// - On machine level signed and unsigned division are
///   two different operations and have to be treated differently.
pub type SignedDiv = BinTermExpr<marker::SignedDivMarker>;
