use ast::prelude::*;

pub mod prelude {
    pub use super::{
        SignedDiv
    };
}

mod marker {
    use ast::prelude::*;
    use ast::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct SignedDivMarker;

    impl ExprMarker for SignedDivMarker {
        const EXPR_KIND: ExprKind = ExprKind::SignedDiv;
    }
}

/// Binary `SignedDiv` (signed division) term expression.
/// 
/// Divides the left child by the right: left / right
/// 
/// # Note
/// 
/// - On machine level signed and unsigned division are
///   two different operations and have to be treated differently.
pub type SignedDiv = BinTermExpr<marker::SignedDivMarker>;

impl From<SignedDiv> for AnyExpr {
    fn from(expr: SignedDiv) -> AnyExpr {
        AnyExpr::SignedDiv(expr)
    }
}
