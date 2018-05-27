use crate::child_iters::{
    ChildrenIter,
    ChildrenIterMut,
    IntoChildrenIter
};

/// Types that implement this trait allow to traverse their children immutably.
pub trait Children {
    /// Iterates over the child expressions of `self` immutably.
    fn children(&self) -> ChildrenIter;
}

/// Types that implement this trait allow to traverse their children mutably.
pub trait ChildrenMut {
    /// Iterates over the child expressions of `self` mutably.
    fn children_mut(&mut self) -> ChildrenIterMut;
}

/// Types that implement this trait allow to be transformed
/// into a consuming children iter.
pub trait IntoChildren {
    /// Transforms `self` into a consuming children iter.
    fn into_children(self) -> IntoChildrenIter;
}
