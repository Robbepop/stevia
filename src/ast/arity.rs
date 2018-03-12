use ast::prelude::*;

/// Reexports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        HasArity
    };
}

/// Types that implement this trait can be queried for their arity.
/// 
/// The arity of an expression is equal to the number of its child expressions.
pub trait HasArity {
    /// Returns the arity of `self`.
    /// 
    /// This is equal to the number of child expressions of `self`.
    fn arity(&self) -> usize;

    /// Returns `true` if `self` has no child expressions.
    #[inline]
    fn is_leaf(&self) -> bool {
        self.arity() == 0
    }

    /// Returns `true` if `self` has child expressions.
    #[inline]
    fn has_children(&self) -> bool {
        self.arity() > 0
    }
}

/// Returns the accumulated arity of the given entity and all of its children recursively.
/// 
/// This is used to identify complex expressions with many recursive child expressions.
pub fn recursive_arity<T>(expr: &T) -> usize
    where T: HasArity + Children
{
    expr.arity() + expr.children().map(|c| recursive_arity(c)).sum::<usize>()
}
