use crate::expr::utils::BinBoolExpr;

mod marker {
    use crate::{ExprKind, ExprMarker};

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct XorMarker;

    impl ExprMarker for XorMarker {
        const EXPR_KIND: ExprKind = ExprKind::Xor;
    }
}

/// XOR (exclusive-or, either-or) formula binary expression.
/// 
/// # Note
/// 
/// - This evaluates to true whenever exactly one of its child
///   expressions evaluates to `true`.
/// - This can be understood as the boolean not-equals.
pub type Xor = BinBoolExpr<marker::XorMarker>;
