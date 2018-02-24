use ast2::prelude::*;

pub mod prelude {
    pub use super::{
        UnsignedDiv
    };
}

mod marker {
    use ast2::prelude::*;
    use ast2::terms::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct UnsignedDivMarker;

    impl ExprMarker for UnsignedDivMarker {
        const EXPR_KIND: ExprKind = ExprKind::UnsignedDiv;
    }
}

/// Binary `UnsignedDiv` (unsigned division) term expression.
/// 
/// Divides the left child by the right: left / right
/// 
/// # Note
/// 
/// - On machine level signed and unsigned division are
///   two different operations and have to be treated differently.
pub type UnsignedDiv = BinTermExpr<marker::UnsignedDivMarker>;

impl From<UnsignedDiv> for AnyExpr {
    fn from(expr: UnsignedDiv) -> AnyExpr {
        AnyExpr::UnsignedDiv(expr)
    }
}
