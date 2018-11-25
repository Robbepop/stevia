use crate::prelude::*;

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
	#[inline]
	fn children_slice(&self) -> &[AnyExpr] {
		&[]
	}
}

impl ChildrenMut for BoolConst {
	#[inline]
	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		&mut []
	}
}

impl IntoChildren for BoolConst {
    fn into_children_vec(self) -> Vec<AnyExpr> {
        Vec::new()
    }
}

impl HasType for BoolConst {
	#[inline]
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl HasKind for BoolConst {
	#[inline]
    fn kind(&self) -> ExprKind {
        ExprKind::BoolConst
    }
}

impl HasArity for BoolConst {
	#[inline]
    fn arity(&self) -> usize {
        0
    }
}
