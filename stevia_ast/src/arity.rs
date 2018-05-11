use crate::prelude::*;

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
    1 + expr.children().map(|c| recursive_arity(c)).sum::<usize>()
}

/// Returns `true` if the given expression tree exceeds a recursive arity of `min_arity`.
/// 
/// # Note
/// 
/// This operation is generally more efficient than querying for the same upper arity bound
/// with `recursive_arity` and should be preferred.
pub fn exceeds_recursive_arity<T>(min_arity: usize, expr: &T) -> bool
    where T: HasArity + Children
{
    fn exceeds_recursive_arity_of<T>(actual_arity: &mut usize, min_arity: usize, expr: &T) -> bool
        where T: HasArity + Children
    {
        *actual_arity += expr.arity();
        if *actual_arity >= min_arity {
            return true
        }
        for child in expr.children() {
            if exceeds_recursive_arity_of(actual_arity, min_arity, child) {
                return true
            }
        }
        false
    }
    exceeds_recursive_arity_of(&mut 0, min_arity, expr)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dummy_expr_with_arity_1() -> AnyExpr {
        let b = PlainExprTreeBuilder::default();
        b.bool_const(true).unwrap()
    }

    fn dummy_expr_with_arity_4() -> AnyExpr {
        let b = PlainExprTreeBuilder::default();
        b.cond(
            b.bool_var("a"),
            b.bitvec_var(BitvecTy::w32(), "x"),
            b.bitvec_var(BitvecTy::w32(), "y"),
        ).unwrap()
    }

    fn dummy_expr_with_arity_12() -> AnyExpr {
        let b = PlainExprTreeBuilder::default();
        b.and_n(vec![
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
        ]).unwrap()
    }

    mod recursive_arity {
        use super::*;

        #[test]
        fn arity_1() {
            assert_eq!(recursive_arity(&dummy_expr_with_arity_1()), 1)
        }

        #[test]
        fn arity_4() {
            assert_eq!(recursive_arity(&dummy_expr_with_arity_4()), 4)
        }

        #[test]
        fn arity_12() {
            assert_eq!(recursive_arity(&dummy_expr_with_arity_12()), 12)
        }
    }

    mod exceeds_recursive_arity {
        use super::*;

        #[test]
        fn arity_1() {
            let expr = dummy_expr_with_arity_1();
            assert!(!exceeds_recursive_arity(42, &expr));
            assert!(!exceeds_recursive_arity( 1, &expr));
            assert!( exceeds_recursive_arity( 0, &expr));
        }

        #[test]
        fn arity_4() {
            let expr = dummy_expr_with_arity_4();
            assert!(!exceeds_recursive_arity(42, &expr));
            assert!(!exceeds_recursive_arity( 4, &expr));
            assert!( exceeds_recursive_arity( 3, &expr));
            assert!( exceeds_recursive_arity( 0, &expr));
        }
        #[test]
        fn arity_12() {
            let expr = dummy_expr_with_arity_12();
            assert!(!exceeds_recursive_arity(42, &expr));
            assert!(!exceeds_recursive_arity(12, &expr));
            assert!( exceeds_recursive_arity(11, &expr));
            assert!( exceeds_recursive_arity( 0, &expr));
        }
    }
}
