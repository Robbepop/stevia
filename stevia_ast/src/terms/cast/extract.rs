use crate::prelude::*;

/// Binary concatenate term expression.
///
/// Concatenates the given bitvec term expressions together.
/// The resulting term expression has a width that is equal to
/// the sum of the bit width of both child term expressions.
///
/// The extracted bits are [lo, hi) of the source term expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Extract {
    /// The source term expression that is to be extracted.
    pub src: P<AnyExpr>,
    /// The index of the hi bit position where lo < hi.
    pub hi: usize,
    /// The index of the lo bit position where lo < hi.
    pub lo: usize,
}

impl Extract {
    /// Returns a new `Extract` term expression for the given source child term expression
    /// in the range of [lo, hi) that are also given as term expressions.
    ///
    /// # Errors
    ///
    /// - If any of the two given child expressions is not of bitvec type or
    ///   has an unmatching bit width to the given bit width.
    pub fn new<E>(src: E, hi: usize, lo: usize) -> ExprResult<Extract>
    where
        E: IntoBoxedAnyExpr,
    {
        let src = src.into_boxed_any_expr();
        let src_width = expect_bitvec_ty(&*src)
			.map_err(ExprError::from)
            .map_err(|e| e.context_msg(
                "Encountered non-bitvector type for the child expression of an Extract expression."
            ))?;
        let extract = Extract { hi, lo, src };
        if lo >= hi {
            return Err(CastError::extract_lo_greater_equal_hi(extract).into());
        }
        if BitvecTy::from(hi) > src_width {
            return Err(CastError::extract_hi_overflow(extract).into());
        }
        Ok(extract)
    }

    /// Returns the bitvec type of this `Extract` term expression.
    pub fn bitvec_ty(&self) -> BitvecTy {
        BitvecTy::from(self.hi - self.lo)
    }
}

impl Children for Extract {
	fn children_slice(&self) -> &[AnyExpr] {
		unsafe {
			std::slice::from_raw_parts(&*self.src as *const AnyExpr, 1)
		}
	}
}

impl ChildrenMut for Extract {
	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		unsafe {
			std::slice::from_raw_parts_mut(&mut *self.src as *mut AnyExpr, 1)
		}
	}
}

impl IntoChildren for Extract {
    fn into_children_vec(self) -> Vec<AnyExpr> {
		let ptr = Box::leak(self.src) as *mut AnyExpr;
		unsafe {
			Vec::from_raw_parts(ptr, 1, 1)
		}
    }
}

impl HasType for Extract {
    fn ty(&self) -> Type {
        self.bitvec_ty().ty()
    }
}

impl HasKind for Extract {
    fn kind(&self) -> ExprKind {
        ExprKind::Extract
    }
}

impl HasArity for Extract {
    fn arity(&self) -> usize {
        1
    }
}

impl From<Extract> for AnyExpr {
    fn from(extract: Extract) -> AnyExpr {
        AnyExpr::Extract(extract)
    }
}
