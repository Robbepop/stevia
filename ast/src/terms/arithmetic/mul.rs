use crate::expr::utils::NaryTermExpr;

mod marker {
    use crate::{ExprKind, ExprMarker};

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct MulMarker;

    impl ExprMarker for MulMarker {
        const EXPR_KIND: ExprKind = ExprKind::Mul;
    }
}

/// N-ary Mul term expression.
///
/// Arithmetically multiplies all child term expressions.
pub type Mul = NaryTermExpr<marker::MulMarker>;
