use ast2::prelude::*;
use simplifier::prelude::*;

pub mod prelude {
    pub use super::BoolConstPropagator;
}

/// This simplification procedure propagates constant values through boolean expressions.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BoolConstPropagator;

impl AutoImplAnyTransformer for BoolConstPropagator {}

impl Transformer for BoolConstPropagator {
    fn transform_cond(&self, cond: expr::IfThenElse) -> TransformOutcome {
        // Reduce to then case if condition is constant true and else case
        // if condition is constant false.
        if let Some(flag) = cond.childs.cond.get_if_bool_const() {
            if flag {
                return TransformOutcome::transformed(cond.childs.then_case)
            } else {
                return TransformOutcome::transformed(cond.childs.else_case)
            }
        }
        let opt_then_const = cond.childs.then_case.get_if_bool_const();
        let opt_else_const = cond.childs.else_case.get_if_bool_const();
        if let (Some(then_const), Some(else_const)) = (opt_then_const, opt_else_const) {
            // If both childs are of the same value the conditional will always result in
            // the same value and can be reduced to exactly that.
            if then_const == else_const {
                return TransformOutcome::transformed(expr::BoolConst::from(then_const))
            }
            // If then and else are true and false respectively we can reduce the conditional
            // to its condition.
            if then_const && !else_const {
                return TransformOutcome::transformed(cond.childs.cond)
            }
            // If then and else are false and true respectively we can reduce the conditional
            // to the negation of its condition.
            if !then_const && else_const {
                return TransformOutcome::transformed(
                    unsafe{ expr::Not::new_unchecked(cond.childs.cond) })
            }
        }
        TransformOutcome::identity(cond)
    }

    fn transform_bool_equals(&self, bool_equals: expr::BoolEquals) -> TransformOutcome {
        // Count number of constant true and false expressions in this boolean equality.
        let (mut n_true, mut n_false) = (0, 0);
        bool_equals
            .childs()
            .filter_map(|c| c.get_if_bool_const())
            .for_each(|b| if b { n_true += 1 } else { n_false += 1 } );
        // Return constant true if either all childs are constant true or false.
        if n_true == bool_equals.arity() || n_false == bool_equals.arity() {
            return TransformOutcome::transformed(expr::BoolConst::from(true))
        }
        // Return constant false if there are constant true and false childs.
        if n_true > 0 && n_false > 0 {
            return TransformOutcome::transformed(expr::BoolConst::from(false))
        }
        TransformOutcome::identity(bool_equals)
    }

    fn transform_and(&self, and: expr::And) -> TransformOutcome {
        // If any child expression is false this is false.
        if and.childs().any(|c| c.is_bool_const(false)) {
            return TransformOutcome::transformed(expr::BoolConst::from(false))
        }
        // If all child expressions are true this is true.
        if and.childs().all(|c| c.is_bool_const(true)) {
            return TransformOutcome::transformed(expr::BoolConst::from(true))
        }
        TransformOutcome::identity(and)
    }

    fn transform_or(&self, or: expr::Or) -> TransformOutcome {
        // If any child expression is true this is true.
        if or.childs().any(|c| c.is_bool_const(true)) {
            return TransformOutcome::transformed(expr::BoolConst::from(true))
        }
        // If all child expressions are false this is false.
        if or.childs().all(|c| c.is_bool_const(false)) {
            return TransformOutcome::transformed(expr::BoolConst::from(false))
        }
        TransformOutcome::identity(or)
    }

    fn transform_not(&self, not: expr::Not) -> TransformOutcome {
        // Simply invert the constant value of the inner child.
        if let Some(flag) = not.child.get_if_bool_const() {
            return TransformOutcome::transformed(expr::BoolConst::from(!flag))
        }
        TransformOutcome::identity(not)
    }

    fn transform_xor(&self, xor: expr::Xor) -> TransformOutcome {
        let lhs_opt_const = xor.childs.lhs.get_if_bool_const();
        let rhs_opt_const = xor.childs.rhs.get_if_bool_const();
        // This is true if both constant childs are not equal.
        if let (Some(c1), Some(c2)) = (lhs_opt_const, rhs_opt_const) {
            return TransformOutcome::transformed(expr::BoolConst::from(c1 != c2))
        }
        TransformOutcome::identity(xor)
    }

    fn transform_implies(&self, implies: expr::Implies) -> TransformOutcome {
        let lhs_opt_const = implies.childs.lhs.get_if_bool_const();
        let rhs_opt_const = implies.childs.rhs.get_if_bool_const();
        // If both parameters are const, simply calculate the implication.
        if let (Some(c1), Some(c2)) = (lhs_opt_const, rhs_opt_const) {
            return TransformOutcome::transformed(expr::BoolConst::from((!c1) || c2))
        }
        if let Some(c1) = lhs_opt_const {
            // If left-hand side is false this is always true.
            if !c1 {
                return TransformOutcome::transformed(expr::BoolConst::from(true))
            }
            // If left-hand side is true this is equal to the right-hand side.
            else {
                return TransformOutcome::transformed(implies.childs.rhs)
            }
        }
        if let Some(c1) = rhs_opt_const {
            // If right-hand side is true this is always true.
            if c1 {
                return TransformOutcome::transformed(expr::BoolConst::from(true))
            }
            // If right-hand side is false this is equal to inverted left-hand side.
            else {
                return TransformOutcome::transformed(
                    unsafe{ expr::Not::new_unchecked(implies.childs.lhs) } )
            }
        }
        TransformOutcome::identity(implies)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod cond {
        use super::*;

        #[test]
        fn const_condition() {
            fn test_for(flag: bool) {
                let b = PlainExprTreeBuilder::default();
                let mut expr = b.cond(
                    b.bool_const(flag),
                    b.bool_var("a"),
                    b.bool_var("b")
                ).unwrap();
                Simplifier::default().simplify(&mut expr);
                let expected = b.bool_var(if flag { "a" } else { "b" }).unwrap();
                assert_eq!(expr, expected);
            }
            test_for(true);
            test_for(false);
        }

        #[test]
        fn const_then_else() {
            fn test_for(then_case: bool, else_case: bool) {
                let b = PlainExprTreeBuilder::default();
                let mut expr = b.cond(
                    b.bool_var("a"),
                    b.bool_const(then_case),
                    b.bool_const(else_case)
                ).unwrap();
                Simplifier::default().simplify(&mut expr);
                if then_case == else_case {
                    assert_eq!(expr, b.bool_const(then_case).unwrap());
                }
                if then_case && !else_case {
                    assert_eq!(expr, b.bool_var("a").unwrap());
                }
                if !then_case && else_case {
                    assert_eq!(expr, b.not(b.bool_var("a")).unwrap());
                }
            }
            test_for( true,  true);
            test_for( true, false);
            test_for(false,  true);
            test_for(false, false);
        }
    }

    #[test]
    fn bool_equals() {
        fn test_for(lhs: bool, rhs: bool) {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bool_equals(
                b.bool_const(lhs),
                b.bool_const(rhs)
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            if lhs == rhs {
                assert_eq!(expr, b.bool_const(true).unwrap());
            }
            else {
                assert_eq!(expr, b.bool_const(false).unwrap());
            }
        }
        test_for( true,  true);
        test_for( true, false);
        test_for(false,  true);
        test_for(false, false);
    }

    #[test]
    fn and() {
        fn test_for(lhs: bool, rhs: bool) {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.and(
                b.bool_const(lhs),
                b.bool_const(rhs)
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            if lhs && rhs {
                assert_eq!(expr, b.bool_const(true).unwrap())
            }
            else {
                assert_eq!(expr, b.bool_const(false).unwrap());
            }
        }
        test_for( true,  true);
        test_for( true, false);
        test_for(false,  true);
        test_for(false, false);
    }

    #[test]
    fn or() {
        fn test_for(lhs: bool, rhs: bool) {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.or(
                b.bool_const(lhs),
                b.bool_const(rhs)
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            if lhs || rhs {
                assert_eq!(expr, b.bool_const(true).unwrap())
            }
            else {
                assert_eq!(expr, b.bool_const(false).unwrap());
            }
        }
        test_for( true,  true);
        test_for( true, false);
        test_for(false,  true);
        test_for(false, false);
    }

    #[test]
    fn xor() {
        fn test_for(lhs: bool, rhs: bool) {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.xor(
                b.bool_const(lhs),
                b.bool_const(rhs)
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            if lhs ^ rhs {
                assert_eq!(expr, b.bool_const(true).unwrap())
            }
            else {
                assert_eq!(expr, b.bool_const(false).unwrap());
            }
        }
        test_for( true,  true);
        test_for( true, false);
        test_for(false,  true);
        test_for(false, false);
    }

    mod implies {
        use super::*;

        #[test]
        fn both_const() {
            fn test_for(lhs: bool, rhs: bool) {
                let b = PlainExprTreeBuilder::default();
                let mut expr = b.implies(
                    b.bool_const(lhs),
                    b.bool_const(rhs)
                ).unwrap();
                Simplifier::default().simplify(&mut expr);
                if !lhs || rhs {
                    assert_eq!(expr, b.bool_const(true).unwrap())
                }
                else {
                    assert_eq!(expr, b.bool_const(false).unwrap());
                }
            }
            test_for( true,  true);
            test_for( true, false);
            test_for(false,  true);
            test_for(false, false);
        }

        #[test]
        fn lhs_const() {
            fn test_for(lhs: bool) {
                let b = PlainExprTreeBuilder::default();
                let mut expr = b.implies(
                    b.bool_const(lhs),
                    b.bool_var("a")
                ).unwrap();
                Simplifier::default().simplify(&mut expr);
                if !lhs {
                    assert_eq!(expr, b.bool_const(true).unwrap())
                }
                else {
                    assert_eq!(expr, b.bool_var("a").unwrap());
                }
            }
            test_for(true);
            test_for(false);
        }

        #[test]
        fn rhs_const() {
            fn test_for(rhs: bool) {
                let b = PlainExprTreeBuilder::default();
                let mut expr = b.implies(
                    b.bool_var("a"),
                    b.bool_const(rhs)
                ).unwrap();
                Simplifier::default().simplify(&mut expr);
                if rhs {
                    assert_eq!(expr, b.bool_const(true).unwrap())
                }
                else {
                    assert_eq!(expr, b.not(b.bool_var("a")).unwrap());
                }
            }
            test_for(true);
            test_for(false);
        }
    }

    #[test]
    fn not() {
        fn test_for(flag: bool) {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.not(
                b.bool_const(flag)
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            if !flag {
                assert_eq!(expr, b.bool_const(true).unwrap())
            }
            else {
                assert_eq!(expr, b.bool_const(false).unwrap());
            }
        }
        test_for( true);
        test_for(false);
    }
}
