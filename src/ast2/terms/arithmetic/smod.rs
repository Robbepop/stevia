use ast2::prelude::*;

pub mod prelude {
    pub use super::{
        SignedModulo
    };
}

mod marker {
    use ast2::prelude::*;
    use ast2::terms::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct SignedModuloMarker;

    impl ExprMarker for SignedModuloMarker {
        const EXPR_KIND: ExprKind = ExprKind::SignedModulo;
    }
}

/// Binary `SignedModulo` (signed remainder) where its sign matches the sign of the divisor.
/// 
/// # Example
/// 
/// -21 mod 4 is 3 because -21 + 4 x 6 is 3.
/// 
/// # Note
/// 
/// - There purposely is no `Umod` term expression since it has no difference to
///   the `Urem` term expression. Use this instead.
/// - On machine level signed and unsigned division are
///   two different operations and have to be treated differently.
pub type SignedModulo = BinTermExpr<marker::SignedModuloMarker>;

impl From<SignedModulo> for AnyExpr {
    fn from(expr: SignedModulo) -> AnyExpr {
        AnyExpr::SignedModulo(expr)
    }
}
