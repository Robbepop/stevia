use crate::expr::utils::NaryBoolExpr;

mod marker {
    use crate::prelude::*;
    use crate::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct OrMarker;

    impl ExprMarker for OrMarker {
        const EXPR_KIND: ExprKind = ExprKind::Or;
    }
}

/// Or formula expression.
/// 
/// Represents boolean disjunction for all boolean child expressions.
pub type Or = NaryBoolExpr<marker::OrMarker>;
