use ast2::prelude::*;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::Mul;
}

mod marker {
    use ast2::prelude::*;
    use ast2::terms::ExprMarker;

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

impl From<Mul> for AnyExpr {
    fn from(expr: Mul) -> AnyExpr {
        AnyExpr::Mul(expr)
    }
}
