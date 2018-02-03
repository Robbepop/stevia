use ast2::prelude::*;
use simplifier::prelude::*;

use itertools::Itertools;

pub mod prelude {
    pub use super::BoolSymbolicSolver;
}

/// This simplification procedure dissolves symbolic tautologies or contradictions
/// for boolean expressions.
/// 
/// This works best if used after an expression normalization transformation and
/// might be expensive for deeply nested expression trees that have many similarities.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BoolSymbolicSolver;

fn is_logical_contradiction(lhs: &AnyExpr, rhs: &AnyExpr) -> bool {
    if let (&AnyExpr::Not(ref lhs), & ref rhs) = (lhs, rhs) {
        return lhs.single_child() == rhs
    }
    if let (& ref lhs, &AnyExpr::Not(ref rhs)) = (lhs, rhs) {
        return lhs == rhs.single_child()
    }
    return false
}

impl AutoImplAnyTransformer for BoolSymbolicSolver {}

impl Transformer for BoolSymbolicSolver {
    fn transform_cond(&self, cond: expr::IfThenElse) -> TransformOutcome {
        TransformOutcome::identity(cond)
        // if c then a else a => a
    }

    fn transform_bool_equals(&self, bool_equals: expr::BoolEquals) -> TransformOutcome {
        // If there exists any pair that logically contradicts each other
        // then this is always false.
        if bool_equals.childs()
                      .cartesian_product(bool_equals.childs())
                      .any(|(lhs, rhs)| is_logical_contradiction(lhs, rhs))
        {
            return TransformOutcome::transformed(expr::BoolConst::from(false))
        }
        TransformOutcome::identity(bool_equals)
    }

    fn transform_and(&self, and: expr::And) -> TransformOutcome {
        // If there exists any pair that logically contradicts each other
        // then this is always false.
        if and.childs()
              .cartesian_product(and.childs())
              .any(|(lhs, rhs)| is_logical_contradiction(lhs, rhs))
        {
            return TransformOutcome::transformed(expr::BoolConst::from(false))
        }
        TransformOutcome::identity(and)
    }

    fn transform_or(&self, or: expr::Or) -> TransformOutcome {
        // If there exists any pair that logically contradicts each other
        // then this is always true.
        if or.childs()
             .cartesian_product(or.childs())
             .any(|(lhs, rhs)| is_logical_contradiction(lhs, rhs))
        {
            return TransformOutcome::transformed(expr::BoolConst::from(true))
        }
        TransformOutcome::identity(or)
    }

    fn transform_xor(&self, xor: expr::Xor) -> TransformOutcome {
        // If both child expressions are equal this is always false.
        if xor.childs.lhs == xor.childs.rhs {
            return TransformOutcome::transformed(expr::BoolConst::from(false))
        }
        // If both child expressions form a logical contradiction this is always true.
        if is_logical_contradiction(&xor.childs.lhs, &xor.childs.rhs) {
            return TransformOutcome::transformed(expr::BoolConst::from(true))
        }
        TransformOutcome::identity(xor)
    }

    fn transform_implies(&self, implies: expr::Implies) -> TransformOutcome {
        // If both child expressions are equal this is true.
        if implies.childs.lhs == implies.childs.rhs {
            return TransformOutcome::transformed(expr::BoolConst::from(true))
        }
        // If both child expressions form a logical contradiction this is
        // equal to the right-hand side child expression following these rules:
        // 
        // *  not(a) =>     a   -->      a
        // *      a  => not(a)  -->  not(a)
        if is_logical_contradiction(&implies.childs.lhs, &implies.childs.rhs) {
            return TransformOutcome::transformed(implies.childs.rhs)
        }
        TransformOutcome::identity(implies)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod bool_equals {
        use super::*;

        #[test]
        fn pair_contradiction() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bool_equals_n(vec![
                b.bool_var("a"),
                b.bool_var("b"),
                b.not(b.bool_var("a")),
                b.bool_var("c")
            ]).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, b.bool_const(false).unwrap());
        }
    }

    mod and {
        use super::*;

        #[test]
        fn pair_contradiction() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.and_n(vec![
                b.bool_var("a"),
                b.bool_var("b"),
                b.not(b.bool_var("a")),
                b.bool_var("c")
            ]).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, b.bool_const(false).unwrap());
        }
    }

    mod or {
        use super::*;

        #[test]
        fn pair_contradiction() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.or_n(vec![
                b.bool_var("a"),
                b.bool_var("b"),
                b.not(b.bool_var("a")),
                b.bool_var("c")
            ]).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, b.bool_const(true).unwrap());
        }
    }

    mod xor {
        use super::*;

        #[test]
        fn lhs_rhs_equals() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.xor(
                b.bool_var("a"),
                b.bool_var("a")
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, b.bool_const(false).unwrap());
        }

        #[test]
        fn a_xor_not_a() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.xor(
                b.bool_var("a"),
                b.not(b.bool_var("a"))
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, b.bool_const(true).unwrap());
        }
    }

    mod implies {
        use super::*;

        #[test]
        fn lhs_rhs_equals() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.implies(
                b.bool_var("a"),
                b.bool_var("a")
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, b.bool_const(true).unwrap());
        }

        #[test]
        fn not_a_implies_a() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.implies(
                b.not(b.bool_var("a")),
                b.bool_var("a")
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, b.bool_var("a").unwrap());
        }

        #[test]
        fn a_implies_not_a() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.implies(
                b.bool_var("a"),
                b.not(b.bool_var("a"))
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, b.not(b.bool_var("a")).unwrap());
        }
    }
}
