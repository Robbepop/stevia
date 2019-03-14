use crate::expr::utils::BinTermExpr;

mod marker {
    use crate::prelude::*;
    use crate::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct SignedRemainderMarker;

    impl ExprMarker for SignedRemainderMarker {
        const EXPR_KIND: ExprKind = ExprKind::SignedRemainder;
    }
}

/// Binary `SignedRemainder` term expression.
/// 
/// # Example
/// 
/// -21 divided by 4 gives -5 with a remainder of -1.
/// 
/// # Note
/// 
/// - On machine level signed and unsigned division are
///   two different operations and have to be treated differently.
pub type SignedRemainder = BinTermExpr<marker::SignedRemainderMarker>;
