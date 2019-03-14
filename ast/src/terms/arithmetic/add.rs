use crate::expr::utils::NaryTermExpr;

mod marker {
    use crate::prelude::*;
    use crate::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct AddMarker;

    impl ExprMarker for AddMarker {
        const EXPR_KIND: ExprKind = ExprKind::Add;
    }
}

/// Add term expression for adding a number of bitvector expressions.
///
/// Arithmetically sums up all child term expressions.
pub type Add = NaryTermExpr<marker::AddMarker>;
