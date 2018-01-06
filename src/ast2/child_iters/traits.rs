use ast2::child_iters::prelude::*;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        Childs,
        ChildsMut,
        IntoChilds
    };
}

/// Types that implement this trait allow to traverse their childs immutably.
pub trait Childs {
    /// Iterates over the child expressions of `self` immutably.
    fn childs(&self) -> ChildsIter;
}

/// Types that implement this trait allow to traverse their childs mutably.
pub trait ChildsMut {
    /// Iterates over the child expressions of `self` mutably.
    fn childs_mut(&mut self) -> ChildsIterMut;
}

/// Types that implement this trait allow to be transformed
/// into a consuming childs iter.
pub trait IntoChilds {
    /// Transforms `self` into a consuming childs iter.
    fn into_childs(self) -> IntoChildsIter;
}
