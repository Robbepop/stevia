use crate::{
    P,
    ExprResult,
    AnyExpr,
    ExprError,
    BoolExpr,
    HasKind,
    ExprKind,
    HasArity,
    BinaryExpr,
    ty::{
        BitvecTy,
        expect_common_bitvec_ty,
        HasType,
        Type,
    },
    expr::utils::BinaryChildren,
    iter::{
        Children,
        ChildrenMut,
        IntoChildren,
    },
    ExprMarker,
};
use std::marker::PhantomData;

pub mod prelude {
    pub use super::{
        ComparisonExpr,
        SignedGreaterEquals,
        SignedGreaterThan,
        SignedLessEquals,
        SignedLessThan,
        UnsignedGreaterEquals,
        UnsignedGreaterThan,
        UnsignedLessEquals,
        UnsignedLessThan,
    };
}

/// Generic comparison term expression.
///
/// # Note
///
/// Used by concrete binary formula expressions as base template.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ComparisonExpr<M> {
    /// The two child term expressions.
    pub children: P<BinaryChildren>,
    /// The bit width of this expression.
    ///
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub children_bitvec_ty: BitvecTy,
    /// Marker to differentiate bool expressions from each
    /// other using the type system.
    marker: PhantomData<M>,
}

impl<M> ComparisonExpr<M>
where
    M: ExprMarker,
{
    /// Returns a new comparison expression for the given two child expressions.
    ///
    /// # Note
    ///
    /// Infers the concrete bitvector type of the resulting expression from its children.
    ///
    /// # Errors
    ///
    /// - If `lhs` or `rhs` do not share a common bitvec type.
    pub fn new<E1, E2>(lhs: E1, rhs: E2) -> ExprResult<Self>
    where
        E1: Into<AnyExpr>,
        E2: Into<AnyExpr>,
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        let common_ty = expect_common_bitvec_ty(&lhs, &rhs)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(format!(
                    "Expect common type among children of comparison expression of type {}.",
                    M::EXPR_KIND.camel_name()
                ))
            })?;
        Ok(unsafe{ Self::new_unchecked(common_ty, lhs, rhs) })
    }

    /// Creates a new comparison expression between `lhs` and `rhs`.
    ///
    /// # Safety
    ///
    /// This does not check the type validity of `lhs` and `rhs` and thus
    /// should be used with care.
    pub unsafe fn new_unchecked<E1, E2>(bvty: BitvecTy, lhs: E1, rhs: E2) -> Self
    where
        E1: Into<AnyExpr>,
        E2: Into<AnyExpr>,
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        debug_assert!(expect_common_bitvec_ty(&lhs, &rhs).is_ok());
        Self::from_raw_parts(bvty, BinaryChildren::new_boxed(lhs, rhs))
    }

    /// Creates a new comparison expression from the given raw parts.
    /// 
    /// # Safety
    /// 
    /// This does not check the type validity of the given raw parts and thus
    /// should be used with care.
    pub unsafe fn from_raw_parts(bvty: BitvecTy, children: P<BinaryChildren>) -> Self {
        Self {
            children_bitvec_ty: bvty,
            children,
            marker: PhantomData,
        }
    }
}

impl<M> BoolExpr for ComparisonExpr<M>
where
    Self: Into<AnyExpr>,
{
}

impl<M> Children for ComparisonExpr<M> {
	#[inline]
	fn children_slice(&self) -> &[AnyExpr] {
		self.children.children_slice()
	}
}

impl<M> ChildrenMut for ComparisonExpr<M> {
	#[inline]
	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		self.children.children_slice_mut()
	}
}

impl<M> IntoChildren for ComparisonExpr<M>
where
	Self: Into<AnyExpr>
{
    fn into_children_vec(self) -> Vec<AnyExpr> {
		let ptr = Box::leak(self.children) as *mut BinaryChildren as *mut AnyExpr;
		unsafe {
			Vec::from_raw_parts(ptr, 2, 2)
		}
    }
}

impl<M> HasType for ComparisonExpr<M> {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl<M> HasKind for ComparisonExpr<M>
where
    M: ExprMarker,
{
    fn kind(&self) -> ExprKind {
        M::EXPR_KIND
    }
}

impl<M> HasArity for ComparisonExpr<M> {
    fn arity(&self) -> usize {
        2
    }
}

impl<M> BinaryExpr for ComparisonExpr<M> {
    fn lhs_child(&self) -> &AnyExpr {
        self.children.lhs_child()
    }
    fn rhs_child(&self) -> &AnyExpr {
        self.children.rhs_child()
    }
}

mod marker {
    use crate::prelude::*;
    use crate::ExprMarker;

    macro_rules! gen_expr_marker {
        ($name:ident, $kind:expr) => {
            #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
            pub struct $name;
            impl ExprMarker for $name {
                const EXPR_KIND: ExprKind = $kind;
            }
        };
    }

    gen_expr_marker!(SignedGreaterEqualsMarker, ExprKind::SignedGreaterEquals);
    gen_expr_marker!(SignedGreaterThanMarker, ExprKind::SignedGreaterThan);
    gen_expr_marker!(SignedLessEqualsMarker, ExprKind::SignedLessEquals);
    gen_expr_marker!(SignedLessThanMarker, ExprKind::SignedLessThan);
    gen_expr_marker!(UnsignedGreaterEqualsMarker, ExprKind::UnsignedGreaterEquals);
    gen_expr_marker!(UnsignedGreaterThanMarker, ExprKind::UnsignedGreaterThan);
    gen_expr_marker!(UnsignedLessEqualsMarker, ExprKind::UnsignedLessEquals);
    gen_expr_marker!(UnsignedLessThanMarker, ExprKind::UnsignedLessThan);
}

/// Binary signed greater-than-or-equals term expression.
///
/// # Note
///
/// Greater equals comparison is different for signed and unsigned parameters.
pub type SignedGreaterEquals = ComparisonExpr<marker::SignedGreaterEqualsMarker>;

/// Binary signed greater-than term expression.
///
/// # Note
///
/// Greater equals comparison is different for signed and unsigned parameters.
pub type SignedGreaterThan = ComparisonExpr<marker::SignedGreaterThanMarker>;

/// Binary signed less-than-or-equals term expression.
///
/// # Note
///
/// Less equals comparison is different for signed and unsigned parameters.
pub type SignedLessEquals = ComparisonExpr<marker::SignedLessEqualsMarker>;

/// Binary signed less-than term expression.
///
/// # Note
///
/// Less equals comparison is different for signed and unsigned parameters.
pub type SignedLessThan = ComparisonExpr<marker::SignedLessThanMarker>;

/// Binary signed greater-than-or-equals term expression.
///
/// # Note
///
/// Greater equals comparison is different for signed and unsigned parameters.
pub type UnsignedGreaterEquals = ComparisonExpr<marker::UnsignedGreaterEqualsMarker>;

/// Binary unsigned greater-than term expression.
///
/// # Note
///
/// Greater equals comparison is different for signed and unsigned parameters.
pub type UnsignedGreaterThan = ComparisonExpr<marker::UnsignedGreaterThanMarker>;

/// Binary unsigned less-than-or-equals term expression.
///
/// # Note
///
/// Less equals comparison is different for signed and unsigned parameters.
pub type UnsignedLessEquals = ComparisonExpr<marker::UnsignedLessEqualsMarker>;

/// Binary unsigned less-than term expression.
///
/// # Note
///
/// Less equals comparison is different for signed and unsigned parameters.
pub type UnsignedLessThan = ComparisonExpr<marker::UnsignedLessThanMarker>;
