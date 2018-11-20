use crate::prelude::*;

pub mod prelude {
    pub use super::{
        BitNot
    };
}

/// The bitwise not term expression.
/// 
/// This flips all bits of the inner term expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitNot {
    /// The inner child formula expression.
    pub child: P<AnyExpr>,
    /// The bit width of this term expression.
    pub bitvec_ty: BitvecTy
}

impl BitNot {
    /// Creates a new `BitNot` term expression for the given child expression.
    /// 
    /// # Note
    /// 
    /// Infers the bitvector type for this expression from its child expression.
    /// 
    /// # Errors
    /// 
    /// - If the given child expression is not of bitvec type.
    pub fn new<E>(child: E) -> ExprResult<Self>
        where E: IntoBoxedAnyExpr
    {
        let child = child.into_boxed_any_expr();
        let bitvec_ty = expect_bitvec_ty(&*child)
			.map_err(ExprError::from)
            .map_err(|e| e.context_msg(
                "Expected the child expression of the BitNot expression to be of bitvector type."
            ))?;
        Ok(BitNot{bitvec_ty, child})
    }
}

impl Children for BitNot {
	fn children_slice(&self) -> &[AnyExpr] {
		unsafe {
			std::slice::from_raw_parts(&*self.child as *const AnyExpr, 1)
		}
	}
}

impl ChildrenMut for BitNot {
	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		unsafe {
			std::slice::from_raw_parts_mut(&mut *self.child as *mut AnyExpr, 1)
		}
	}
}

impl IntoChildren for BitNot {
    fn into_children_vec(self) -> Vec<AnyExpr> {
		let ptr = Box::leak(self.child) as *mut AnyExpr;
		unsafe {
			Vec::from_raw_parts(ptr, 1, 1)
		}
    }
}

impl HasType for BitNot {
    fn ty(&self) -> Type {
        self.bitvec_ty.ty()
    }
}

impl HasKind for BitNot {
    fn kind(&self) -> ExprKind {
        ExprKind::BitNot
    }
}

impl HasArity for BitNot {
    fn arity(&self) -> usize {
        1
    }
}

impl From<BitNot> for AnyExpr {
    fn from(bitnot: BitNot) -> AnyExpr {
        AnyExpr::BitNot(bitnot)
    }
}

impl UnaryExpr for BitNot {}

impl SingleChild for BitNot {
    fn single_child(&self) -> &AnyExpr {
        &*self.child
    }

    fn single_child_mut(&mut self) -> &mut AnyExpr {
        &mut *self.child
    }

    fn into_single_child(self) -> AnyExpr {
        *self.child
    }

    fn into_boxed_single_child(self) -> Box<AnyExpr> {
        self.child
    }
}
