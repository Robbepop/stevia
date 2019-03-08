use crate::prelude::*;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::Mul;
}

mod marker {
    use crate::prelude::*;
    use crate::ExprMarker;

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
