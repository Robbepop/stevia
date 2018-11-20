use crate::prelude::*;
use crate::ExprMarker;

use std::marker::PhantomData;

/// Any extend expression.
/// 
/// # Note
/// 
/// This is mainly used for generic error reporting specific
/// to extend expressions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AnyExtendExpr {
    Sign(SignExtend),
    Zero(ZeroExtend)
}

impl From<SignExtend> for AnyExtendExpr {
    fn from(expr: SignExtend) -> Self {
        AnyExtendExpr::Sign(expr)
    }
}

impl From<ZeroExtend> for AnyExtendExpr {
    fn from(expr: ZeroExtend) -> Self {
        AnyExtendExpr::Zero(expr)
    }
}

impl AnyExtendExpr {
    pub fn bitvec_ty(&self) -> BitvecTy {
        use self::AnyExtendExpr::*;
        match self {
            Sign(extend) => extend.bitvec_ty,
            Zero(extend) => extend.bitvec_ty
        }
    }
}

impl HasKind for AnyExtendExpr {
    fn kind(&self) -> ExprKind {
        use self::AnyExtendExpr::*;
        match self {
            Sign(extend) => extend.kind(),
            Zero(extend) => extend.kind()
        }
    }
}

/// Generic binary extend term expression.
///
/// # Note
///
/// This generic expression is used as foundation for sign and zero
/// extend expressions since they share a lot of behaviour.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExtendExpr<M> {
    /// The source term expression for extension.
    pub src: P<AnyExpr>,
    /// The target bit width.
    ///
    /// This is also the bit width of this term expression.
    pub bitvec_ty: BitvecTy,
    /// Marker to differentiate term expressions from each
    /// other using the type system.
    marker: PhantomData<M>,
}

impl ZeroExtend {
    /// Returns a new zero-extend expression for the given child term expressions.
    ///
    /// # Errors
    ///
    /// - If the bit width of the child term expression is greater than
    ///   the target extension bit width.
    pub fn new<E>(target_width: BitWidth, src: E) -> ExprResult<Self>
    where
        E: IntoBoxedAnyExpr,
    {
        let src = src.into_boxed_any_expr();
        let src_bvty = expect_bitvec_ty(&*src)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(
                    "Expected bitvector type for the child expression of a zero-extend expression.",
                )
            })?;
        let extend = Self {
            bitvec_ty: BitvecTy::from(target_width),
            src,
            marker: PhantomData,
        };
        if target_width < src_bvty.width() {
            return Err(CastError::extend_to_smaller(src_bvty, extend).into());
        }
        Ok(extend)
    }
}

impl SignExtend {
    /// Returns a new sign-extend expression for the given child term expressions.
    ///
    /// # Errors
    ///
    /// - If the bit width of the child term expression is greater than
    ///   the target extension bit width.
    pub fn new<E>(target_width: BitWidth, src: E) -> ExprResult<Self>
    where
        E: IntoBoxedAnyExpr,
    {
        let src = src.into_boxed_any_expr();
        let src_bvty = expect_bitvec_ty(&*src)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(
                    "Expected bitvector type for the child expression of a sign-extend expression.",
                )
            })?;
        let extend = Self {
            bitvec_ty: BitvecTy::from(target_width),
            src,
            marker: PhantomData,
        };
        if target_width < src_bvty.width() {
            return Err(CastError::extend_to_smaller(src_bvty, extend).into());
        }
        Ok(extend)
    }
}

impl<M> Children for ExtendExpr<M> {
	fn children_slice(&self) -> &[AnyExpr] {
		unsafe {
			std::slice::from_raw_parts(&*self.src as *const AnyExpr, 1)
		}
	}
}

impl<M> ChildrenMut for ExtendExpr<M> {
	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		unsafe {
			std::slice::from_raw_parts_mut(&mut *self.src as *mut AnyExpr, 1)
		}
	}
}

impl<M> IntoChildren for ExtendExpr<M>
where
	Self: Into<AnyExpr>
{
    fn into_children_vec(self) -> Vec<AnyExpr> {
		let ptr = Box::leak(self.src) as *mut AnyExpr;
		unsafe {
			Vec::from_raw_parts(ptr, 1, 1)
		}
    }
}

impl<M> HasType for ExtendExpr<M> {
    fn ty(&self) -> Type {
        self.bitvec_ty.ty()
    }
}

impl<M> HasKind for ExtendExpr<M>
where
    M: ExprMarker,
{
    fn kind(&self) -> ExprKind {
        M::EXPR_KIND
    }
}

impl<M> HasArity for ExtendExpr<M> {
    fn arity(&self) -> usize {
        1
    }
}

mod marker {
    use crate::prelude::*;
    use crate::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct SignExtendMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct ZeroExtendMarker;

    impl ExprMarker for SignExtendMarker {
        const EXPR_KIND: ExprKind = ExprKind::SignExtend;
    }

    impl ExprMarker for ZeroExtendMarker {
        const EXPR_KIND: ExprKind = ExprKind::ZeroExtend;
    }
}

/// Zero-extend term expression.
///
/// Extends the source child term expression to the given bit width.
/// This extend operation respects the sign of the term expression.
pub type ZeroExtend = ExtendExpr<marker::ZeroExtendMarker>;

impl From<ZeroExtend> for AnyExpr {
    fn from(expr: ZeroExtend) -> AnyExpr {
        AnyExpr::ZeroExtend(expr)
    }
}

/// Sign-extend term expression.
///
/// Extends the source child term expression to the given bit width.
/// This extend operation respects the sign of the term expression.
pub type SignExtend = ExtendExpr<marker::SignExtendMarker>;

impl From<SignExtend> for AnyExpr {
    fn from(expr: SignExtend) -> AnyExpr {
        AnyExpr::SignExtend(expr)
    }
}
