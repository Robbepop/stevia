use crate::prelude::*;

pub mod prelude {
    pub use super::{
        BoolEquals
    };
}

mod marker {
    use crate::prelude::*;
    use crate::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct BoolEqualsMarker;

    impl ExprMarker for BoolEqualsMarker {
        const EXPR_KIND: ExprKind = ExprKind::BoolEquals;
    }
}

/// Boolean equality (also known as n-ary if-and-only-if) formula expression.
/// 
/// # Note
/// 
/// - This evaluates to true whenever exactly all of its child
///   expressions either evaluate to `true` or `false`.
/// - This can be understood as the logical equality.
pub type BoolEquals = NaryBoolExpr<marker::BoolEqualsMarker>;
