use crate::expr::utils::NaryBoolExpr;

mod marker {
    use crate::{ExprKind, ExprMarker};

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct AndMarker;

    impl ExprMarker for AndMarker {
        const EXPR_KIND: ExprKind = ExprKind::And;
    }
}

/// And formula expression.
/// 
/// Represents boolean conjunction for all boolean child expressions.
pub type And = NaryBoolExpr<marker::AndMarker>;
