use crate::AnyExpr;
use crate::child_iters::{ChildrenIter, ChildrenIterMut, IntoChildrenIter};

/// Types that implement this trait allow to traverse their children immutably.
pub trait Children {
    /// Iterates over the child expressions of `self` immutably.
	#[inline]
    fn children(&self) -> ChildrenIter {
		ChildrenIter::from_slice(self.children_slice())
	}

	fn children_slice(&self) -> &[AnyExpr];
}

/// Types that implement this trait allow to traverse their children mutably.
pub trait ChildrenMut {
    /// Iterates over the child expressions of `self` mutably.
	#[inline]
    fn children_mut(&mut self) -> ChildrenIterMut {
		ChildrenIterMut::from_slice(self.children_slice_mut())
	}

	fn children_slice_mut(&mut self) -> &mut [AnyExpr];
}

/// Types that implement this trait allow to be transformed
/// into a consuming children iter.
pub trait IntoChildren {
    /// Transforms `self` into a consuming children iter.
    fn into_children(self) -> IntoChildrenIter
	where
		Self: Sized
	{
		IntoChildrenIter::from_expr(self)
	}

	fn into_children_vec(self) -> Vec<AnyExpr>;
}
