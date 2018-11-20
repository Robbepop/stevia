use crate::prelude::*;

pub mod prelude {
    pub use super::Neg;
}

/// The arithmetic negation term expression.
///
/// This negate the inner term expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Neg {
    /// The inner child formula expression.
    pub child: P<AnyExpr>,
    /// The bit width of this term expression.
    pub bitvec_ty: BitvecTy,
}

impl Neg {
    /// Creates a new `Neg` term expression for the given child expression.
    ///
    /// # Note
    ///
    /// Infers the bitvector type for this expression from its child expression.
    ///
    /// # Errors
    ///
    /// - If the given child expression is not of bitvec type.
    pub fn new<E>(child: E) -> ExprResult<Self>
    where
        E: IntoBoxedAnyExpr,
    {
        let child = child.into_boxed_any_expr();
        let bitvec_ty = expect_bitvec_ty(&*child)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(
                    "Expected the child expression of the Neg expression to be of bitvector type.",
                )
            })?;
        Ok(Neg { bitvec_ty, child })
    }
}

impl Children for Neg {
    fn children(&self) -> ChildrenIter {
        ChildrenIter::unary(&self.child)
    }

	fn children_slice(&self) -> &[AnyExpr] {
		unsafe {
			std::slice::from_raw_parts(&*self.child as *const AnyExpr, 1)
		}
	}
}

impl ChildrenMut for Neg {
    fn children_mut(&mut self) -> ChildrenIterMut {
        ChildrenIterMut::unary(&mut self.child)
    }

	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		unsafe {
			std::slice::from_raw_parts_mut(&mut *self.child as *mut AnyExpr, 1)
		}
	}
}

impl IntoChildren for Neg {
    fn into_children_vec(self) -> Vec<AnyExpr> {
		let ptr = Box::leak(self.child) as *mut AnyExpr;
		unsafe {
			Vec::from_raw_parts(ptr, 1, 1)
		}
    }
}

impl HasType for Neg {
    fn ty(&self) -> Type {
        self.bitvec_ty.ty()
    }
}

impl HasKind for Neg {
    fn kind(&self) -> ExprKind {
        ExprKind::Neg
    }
}

impl HasArity for Neg {
    fn arity(&self) -> usize {
        1
    }
}

impl From<Neg> for AnyExpr {
    fn from(neg: Neg) -> AnyExpr {
        AnyExpr::Neg(neg)
    }
}

impl UnaryExpr for Neg {}

impl SingleChild for Neg {
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
