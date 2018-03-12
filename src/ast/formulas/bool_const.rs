use ast::prelude::*;

pub mod prelude {
    pub use super::{
        BoolConst
    };
}

/// A constant boolean expression.
/// 
/// This represents either `true` or `false` and is
/// a leaf expression without any child expressions.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BoolConst {
    /// The constant boolean value.
    pub val: bool
}

impl From<bool> for BoolConst {
    /// Creates a new `BoolConst` from the given `bool`.
    fn from(flag: bool) -> BoolConst {
        if flag { BoolConst::t() } else { BoolConst::f() }
    }
}

impl BoolConst {
    /// Returns a new `BoolConst` representing constant `true`.
    #[inline]
    pub fn t() -> BoolConst {
        BoolConst{ val: true }
    }

    /// Returns a new `BoolConst` representing constant `false`.
    #[inline]
    pub fn f() -> BoolConst {
        BoolConst{ val: false }
    }
}

impl BoolExpr for BoolConst {}

impl Children for BoolConst {
    fn children(&self) -> ChildrenIter {
        ChildrenIter::none()
    }
}

impl ChildrenMut for BoolConst {
    fn children_mut(&mut self) -> ChildrenIterMut {
        ChildrenIterMut::none()
    }
}

impl IntoChildren for BoolConst {
    fn into_children(self) -> IntoChildrenIter {
        IntoChildrenIter::none()
    }
}

impl HasType for BoolConst {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl HasKind for BoolConst {
    fn kind(&self) -> ExprKind {
        ExprKind::BoolConst
    }
}

impl HasArity for BoolConst {
    fn arity(&self) -> usize {
        0
    }
}

impl From<BoolConst> for AnyExpr {
    fn from(bool_const: BoolConst) -> AnyExpr {
        AnyExpr::BoolConst(bool_const)
    }
}
