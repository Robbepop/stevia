use crate::AnyExpr;
use crate::child_iters::{ChildrenIter, ChildrenIterMut, IntoChildrenIter};

/// Types that implement this trait allow to traverse their children immutably.
pub trait Children {
    /// Iterates over the child expressions of `self` immutably.
    fn children(&self) -> ChildrenIter;

	fn children_slice(&self) -> &[AnyExpr];
}

/// Types that implement this trait allow to traverse their children mutably.
pub trait ChildrenMut {
    /// Iterates over the child expressions of `self` mutably.
    fn children_mut(&mut self) -> ChildrenIterMut;

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
