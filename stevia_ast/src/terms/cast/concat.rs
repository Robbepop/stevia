use crate::prelude::*;

/// Binary concatenate term expression.
///
/// Concatenates the given bitvec term expressions together.
/// The resulting term expression has a width that is equal to
/// the sum of the bit width of both child term expressions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Concat {
    /// The two child term expressions.
    pub children: P<BinExprChildren>,
    /// The resulting bit width.
    ///
    /// The purpose of this is to cache the bitwidth so that
    /// it does not have to be recomputed all the time over.
    ///
    /// Caching this value is useful since the bit width cannot
    /// change during the lifetime of this expression.
    pub bitvec_ty: BitvecTy,
}

impl Concat {
    /// Returns a new `Concat` (concatenate) term expression with the
    /// given child term expressions.
    ///
    /// # Errors
    ///
    /// - If any of the two given child expressions is not of bitvec type.
    pub fn new<E1, E2>(lhs: E1, rhs: E2) -> ExprResult<Concat>
    where
        E1: Into<AnyExpr>,
        E2: Into<AnyExpr>,
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        let lhs_bvty = expect_bitvec_ty(&lhs)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg("Expected bitvector type for the left hand-side child expression of the concat expression.")
            })?;
        let rhs_bvty = expect_bitvec_ty(&rhs)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg("Expected bitvector type for the right hand-side child expression of the concat expression.")
            })?;
        let concat_bvty = BitvecTy::from(lhs_bvty.width().len_bits() + rhs_bvty.width().len_bits());
        Ok(Concat {
            bitvec_ty: concat_bvty,
            children: BinExprChildren::new_boxed(lhs, rhs),
        })
    }
}

impl Children for Concat {
    fn children(&self) -> ChildrenIter {
        self.children.children()
    }

	fn children_slice(&self) -> &[AnyExpr] {
		self.children.children_slice()
	}
}

impl ChildrenMut for Concat {
    fn children_mut(&mut self) -> ChildrenIterMut {
        self.children.children_mut()
    }

	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		self.children.children_slice_mut()
	}
}

impl IntoChildren for Concat {
    fn into_children_vec(self) -> Vec<AnyExpr> {
		let ptr = Box::leak(self.children) as *mut BinExprChildren as *mut AnyExpr;
		unsafe {
			Vec::from_raw_parts(ptr, 2, 2)
		}
    }
}

impl HasType for Concat {
    fn ty(&self) -> Type {
        self.bitvec_ty.ty()
    }
}

impl HasKind for Concat {
    fn kind(&self) -> ExprKind {
        ExprKind::Concat
    }
}

impl HasArity for Concat {
    fn arity(&self) -> usize {
        2
    }
}

impl From<Concat> for AnyExpr {
    fn from(expr: Concat) -> AnyExpr {
        AnyExpr::Concat(expr)
    }
}
