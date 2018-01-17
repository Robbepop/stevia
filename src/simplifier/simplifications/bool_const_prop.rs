use ast2::prelude::*;
use simplifier::prelude::*;

pub mod prelude {
    pub use super::BoolConstPropagator;
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BoolConstPropagator;

impl AutoImplAnyTransformer for BoolConstPropagator {}

impl Transformer for BoolConstPropagator {
    fn transform_cond(&self, cond: expr::IfThenElse) -> AnyExprAndTransformResult {
        match cond.childs.cond.get_if_bool_const() {
            Some(flag) => if flag {
                AnyExprAndTransformResult::transformed(cond.childs.then_case)
            } else {
                AnyExprAndTransformResult::transformed(cond.childs.else_case)
            },
            None => AnyExprAndTransformResult::identity(cond),
        }
    }

    fn transform_bool_equals(&self, bool_equals: expr::BoolEquals) -> AnyExprAndTransformResult {
        // Count number of constant true and false expressions in this boolean equality.
        let (mut n_true, mut n_false) = (0, 0);
        bool_equals
            .childs()
            .filter_map(|c| c.get_if_bool_const())
            .for_each(|b| if b { n_true += 1 } else { n_false += 1 } );
        // Return constant true if either all childs are constant true or false.
        if n_true == bool_equals.arity() || n_false == bool_equals.arity() {
            return AnyExprAndTransformResult::transformed(expr::BoolConst::from(true))
        }
        // Return constant false if there are constant true and false childs.
        if n_true > 0 && n_false > 0 {
            return AnyExprAndTransformResult::transformed(expr::BoolConst::from(false))
        }
        AnyExprAndTransformResult::identity(bool_equals)
    }

    fn transform_and(&self, and: expr::And) -> AnyExprAndTransformResult {
        if and.childs().any(|c| c.is_bool_const(false)) {
            return AnyExprAndTransformResult::transformed(expr::BoolConst::from(false))
        }
        if and.childs().all(|c| c.is_bool_const(true)) {
            return AnyExprAndTransformResult::transformed(expr::BoolConst::from(true))
        }
        AnyExprAndTransformResult::identity(and)
    }

    fn transform_or(&self, or: expr::Or) -> AnyExprAndTransformResult {
        if or.childs().any(|c| c.is_bool_const(true)) {
            return AnyExprAndTransformResult::transformed(expr::BoolConst::from(true))
        }
        if or.childs().all(|c| c.is_bool_const(false)) {
            return AnyExprAndTransformResult::transformed(expr::BoolConst::from(false))
        }
        AnyExprAndTransformResult::identity(or)
    }

    fn transform_not(&self, not: expr::Not) -> AnyExprAndTransformResult {
        if let Some(flag) = not.child.get_if_bool_const() {
            return AnyExprAndTransformResult::transformed(expr::BoolConst::from(!flag))
        }
        AnyExprAndTransformResult::identity(not)
    }

    fn transform_xor(&self, xor: expr::Xor) -> AnyExprAndTransformResult {
        let lhs_opt_const = xor.childs.lhs.get_if_bool_const();
        let rhs_opt_const = xor.childs.rhs.get_if_bool_const();
        if let (Some(c1), Some(c2)) = (lhs_opt_const, rhs_opt_const) {
            return AnyExprAndTransformResult::transformed(expr::BoolConst::from(c1 != c2))
        }
        AnyExprAndTransformResult::identity(xor)
    }

    fn transform_implies(&self, implies: expr::Implies) -> AnyExprAndTransformResult {
        let lhs_opt_const = implies.childs.lhs.get_if_bool_const();
        let rhs_opt_const = implies.childs.rhs.get_if_bool_const();
        if let (Some(c1), Some(c2)) = (lhs_opt_const, rhs_opt_const) {
            return AnyExprAndTransformResult::transformed(expr::BoolConst::from((!c1) || c2))
        }
        AnyExprAndTransformResult::identity(implies)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cond() {
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
        test_for( true,  true);
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
        test_for( true,  true);
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
        test_for( true,  true);
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
        test_for( true,  true);
    }

    #[test]
    fn implies() {
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
        test_for( true,  true);
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
