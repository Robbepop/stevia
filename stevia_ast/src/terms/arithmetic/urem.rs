use crate::prelude::*;

pub mod prelude {
    pub use super::{
        UnsignedRemainder
    };
}

mod marker {
    use crate::prelude::*;
    use crate::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct UnsignedRemainderMarker;

    impl ExprMarker for UnsignedRemainderMarker {
        const EXPR_KIND: ExprKind = ExprKind::UnsignedRemainder;
    }
}

/// Binary `UnsignedRemainder` term expression.
/// 
/// # Note
/// 
/// - On machine level signed and unsigned division are
///   two different operations and have to be treated differently.
pub type UnsignedRemainder = BinTermExpr<marker::UnsignedRemainderMarker>;

impl From<UnsignedRemainder> for AnyExpr {
    fn from(expr: UnsignedRemainder) -> AnyExpr {
        AnyExpr::UnsignedRemainder(expr)
    }
}
