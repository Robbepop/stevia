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
    fn has_childs(&self) -> bool {
        self.arity() > 0
    }
}
