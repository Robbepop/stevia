use ast::prelude::*;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::Add;
}

mod marker {
    use ast::prelude::*;
    use ast::terms::ExprMarker;

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

impl From<Add> for AnyExpr {
    fn from(expr: Add) -> AnyExpr {
        AnyExpr::Add(expr)
    }
}
