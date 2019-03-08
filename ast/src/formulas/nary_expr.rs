use crate::prelude::*;
use crate::ExprMarker;

use std::marker::PhantomData;
use std::cmp::Ordering;

pub mod prelude {
    pub use super::NaryBoolExpr;
}

/// Generic n-ary formula expression.
///
/// Used by concrete n-ary formula expressions as base template.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NaryBoolExpr<M> {
    /// The child formula expressions.
    pub children: Vec<AnyExpr>,
    /// Marker to differentiate bool expressions from each
    /// other using the type system.
    marker: PhantomData<M>,
}

impl<M> NaryBoolExpr<M>
where
    M: ExprMarker,
{
    /// Returns a new n-ary formula expression from the given raw parts.
    ///
    /// # Safety
    /// 
    /// This does not check the type integrity of the given child expressions
    /// and thus should be used with care.
    /// 
    /// # Note
    ///
    /// This is just a convenience method and performs no type checking on its arguments.
    unsafe fn from_raw_parts(children: Vec<AnyExpr>) -> Self {
        Self{ children, marker: PhantomData }
    }

    /// Returns a new n-ary formula expression with the given child expressions.
    ///
    /// # Note
    ///
    /// Since the given child expressions are the only child expressions this
    /// n-ary formula expression is actually a binary formula expression upon
    /// construction.
    ///
    /// # Errors
    ///
    /// - If `lhs` or `rhs` are not of bool type.
    pub fn binary<E1, E2>(lhs: E1, rhs: E2) -> ExprResult<Self>
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
                    "Expected boolean type for the left hand-side expression of the binary {} expression.",
                    M::EXPR_KIND.camel_name()
                ))
            })?;
        expect_type(Type::Bool, &rhs)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(format!(
                    "Expected boolean type for the right hand-side expression of the binary {} expression.",
                    M::EXPR_KIND.camel_name()
                ))
            })?;
        Ok(unsafe{ Self::binary_unchecked(lhs, rhs) })
    }

    /// Returns a new n-ary formula expression with the given child expressions.
    ///
    /// # Note
    ///
    /// Since the given child expressions are the only child expressions this
    /// n-ary formula expression is actually a binary formula expression upon
    /// construction.
    ///
    /// # Safety
    ///
    /// This is unsafe since it does not check the type requirements for the given child expressions.
    pub unsafe fn binary_unchecked<E1, E2>(lhs: E1, rhs: E2) -> Self
    where
        E1: Into<AnyExpr>,
        E2: Into<AnyExpr>,
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        debug_assert!(expect_type(Type::Bool, &lhs).is_ok());
        debug_assert!(expect_type(Type::Bool, &rhs).is_ok());
        Self::from_raw_parts(vec![lhs, rhs])
    }

    /// Returns a new n-ary formula expression.
    ///
    /// # Errors
    ///
    /// - If the given iterator has less than two elements.
    /// - If not all expressions yielded by the given iteration are of boolean type.
    pub fn nary<I, E>(children: I) -> ExprResult<Self>
    where
        I: IntoIterator<Item = E>,
		E: Into<AnyExpr> + HasType
    {
        let children = children.into_iter().collect::<Vec<_>>();
        if children.len() < 2 {
            return Err(
                ExprError::too_few_children(2, children.len()).context_msg(
                    format!(
                        "Expected at least 2 child expressions for the {} expression.",
                        M::EXPR_KIND.camel_name()
                    ),
                ),
            );
        }
        for (n, child) in children.iter().enumerate() {
            expect_type(Type::Bool, child)
			    .map_err(ExprError::from)
                .map_err(|e| {
                    e.context_msg(format!(
                        "Expected boolean type for the child expression at index {:?} of the {} expression.",
                        n,
                        M::EXPR_KIND.camel_name()
                    ))
                })?;
        }
        Ok(unsafe{ Self::nary_unchecked(children) })
    }

    /// Returns a new n-ary formula expression from the given child expressions.
    /// 
    /// # Safety
    /// 
    /// This does not check the type integrity of the given child expressions
    /// and thus should be used with care.
    pub unsafe fn nary_unchecked<I, E>(children: I) -> Self
    where
        I: IntoIterator<Item = E>,
		E: Into<AnyExpr> + HasType
    {
        let children = children
			.into_iter()
			.map(Into::into)
			.collect::<Vec<_>>();
        debug_assert!(children.len() >= 2);
        debug_assert!(children.iter().all(|e| expect_type(Type::Bool, e).is_ok()));
        Self::from_raw_parts(children)
    }
}

impl<M> BoolExpr for NaryBoolExpr<M>
where
    Self: Into<AnyExpr>,
{
}

impl<M> Children for NaryBoolExpr<M> {
	#[inline]
    fn children(&self) -> ChildrenIter {
        ChildrenIter::from_slice(&self.children)
    }

	#[inline]
	fn children_slice(&self) -> &[AnyExpr] {
		&self.children
	}
}

impl<M> ChildrenMut for NaryBoolExpr<M> {
	#[inline]
    fn children_mut(&mut self) -> ChildrenIterMut {
        ChildrenIterMut::from_slice(&mut self.children)
    }

	#[inline]
	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		&mut self.children
	}
}

impl<M> IntoChildren for NaryBoolExpr<M>
where
	Self: Into<AnyExpr>
{
    fn into_children_vec(self) -> Vec<AnyExpr> {
		self.children
    }
}

impl<M> HasType for NaryBoolExpr<M> {
	#[inline]
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl<M> HasKind for NaryBoolExpr<M>
where
    M: ExprMarker,
{
	#[inline]
    fn kind(&self) -> ExprKind {
        M::EXPR_KIND
    }
}

impl<M> HasArity for NaryBoolExpr<M> {
	#[inline]
    fn arity(&self) -> usize {
        self.children.len()
    }
}

impl<M> DedupChildren for NaryBoolExpr<M> {
    fn dedup_children(&mut self) {
        self.children.dedup()
    }
}

impl<M> SortChildren for NaryBoolExpr<M> {
    fn sort_children_by<F>(&mut self, comparator: F)
    where
        F: FnMut(&AnyExpr, &AnyExpr) -> Ordering,
    {
        self.children.sort_unstable_by(comparator)
    }
}

impl<M> RetainChildren for NaryBoolExpr<M> {
    fn retain_children<P>(&mut self, predicate: P)
    where
        P: FnMut(&AnyExpr) -> bool,
    {
        self.children.retain(predicate);
    }
}
