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
    fn has_childs(&self) -> bool {
        self.arity() > 0
    }
}

/// Returns the accumulated arity of the given entity and all of its childs recursively.
/// 
/// This is used to identify complex expressions with many recursive child expressions.
pub fn recursive_arity<T>(expr: &T) -> usize
    where T: HasArity + Childs
{
    expr.arity() + expr.childs().map(|c| recursive_arity(c)).sum::<usize>()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_recursive_arity() {
        let b = PlainExprTreeBuilder::default();
        let input = b.and_n(vec![
            b.bool_var("a"),
            b.not(
                b.or_n(vec![
                    b.bool_var("b"),
                    b.bool_var("c"),
                    b.not(
                        b.bool_var("d")
                    )
                ])
            ),
            b.xor(
                b.not(
                    b.bool_var("d")
                ),
                b.bool_var("b")
            )
        ]).unwrap();
        assert_eq!(recursive_arity(&input), 11)
    }
}
