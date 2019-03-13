use crate::{
    AnyExpr,
    BinaryChildren,
    ExprMarker,
    ExprResult,
    ExprError,
    BoolExpr,
    iter::{
        Children,
        ChildrenIterMut,
        ChildrenIter,
        ChildrenMut,
        IntoChildren,
    },
    HasKind,
    ExprKind,
    HasArity,
    BinaryExpr,
    P,
    ty::{
        Type,
        HasType,
        expect_type,
    },
};
use std::marker::PhantomData;

/// Generic binary formula expression.
///
/// Used by concrete binary formula expressions as base template.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BinBoolExpr<M> {
    /// The two child expressions.
    pub children: P<BinaryChildren>,
    /// Marker to differentiate bool expressions from each
    /// other using the type system.
    marker: PhantomData<M>,
}

impl<M> BinBoolExpr<M>
where
    M: ExprMarker,
{
    /// Returns a new binary formula expression with the given child expressions.
    ///
    /// # Errors
    ///
    /// - If `lhs` or `rhs` are not of bool type.
    pub fn new<E1, E2>(lhs: E1, rhs: E2) -> ExprResult<Self>
    where
        E1: Into<AnyExpr>,
        E2: Into<AnyExpr>,
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        expect_type(Type::Bool, &lhs)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(format!(
                    "Expected boolean type for the left hand-side expression of the {} expression.",
                    M::EXPR_KIND.camel_name()
                ))
            })?;
        expect_type(Type::Bool, &rhs)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(format!(
                    "Expected boolean type for the right hand-side expression of the {} expression.",
                    M::EXPR_KIND.camel_name()
                ))
            })?;
        Ok(unsafe{ Self::new_unchecked(lhs, rhs) })
    }

    /// Returns a new binary formula expression with the given child expressions.
    /// 
    /// # Safety
    /// 
    /// This does not check the type integrity of the given child expressions
    /// and thus should be used with care.
    pub unsafe fn new_unchecked<E1, E2>(lhs: E1, rhs: E2) -> Self
    where
        E1: Into<AnyExpr>,
        E2: Into<AnyExpr>
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        debug_assert!(expect_type(Type::Bool, &lhs).is_ok());
        debug_assert!(expect_type(Type::Bool, &rhs).is_ok());
        Self {
            children: BinaryChildren::new_boxed(lhs, rhs),
            marker: PhantomData,
        }
    }
}

impl<M> BoolExpr for BinBoolExpr<M>
where
    Self: Into<AnyExpr>,
{
}

impl<M> Children for BinBoolExpr<M> {
	#[inline]
    fn children(&self) -> ChildrenIter {
        self.children.children()
	}

	#[inline]
	fn children_slice(&self) -> &[AnyExpr] {
		self.children.children_slice()
	}
}

impl<M> ChildrenMut for BinBoolExpr<M> {
	#[inline]
    fn children_mut(&mut self) -> ChildrenIterMut {
        self.children.children_mut()
    }

	#[inline]
	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		self.children.children_slice_mut()
	}
}

impl<M> IntoChildren for BinBoolExpr<M>
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

impl<M> HasType for BinBoolExpr<M> {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl<M> HasKind for BinBoolExpr<M>
where
    M: ExprMarker,
{
    fn kind(&self) -> ExprKind {
        M::EXPR_KIND
    }
}

impl<M> HasArity for BinBoolExpr<M> {
    fn arity(&self) -> usize {
        2
    }
}

impl<M> BinaryExpr for BinBoolExpr<M> {
    fn lhs_child(&self) -> &AnyExpr {
        self.children.lhs_child()
    }

    fn rhs_child(&self) -> &AnyExpr {
        self.children.rhs_child()
    }
}
