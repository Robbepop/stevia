use stevia_ast::{
    prelude::*,
};
use itertools::Itertools;

/// This simplification procedure dissolves symbolic tautologies or contradictions
/// for boolean expressions.
/// 
/// This works best if used after an expression normalization transformation and
/// might be expensive for deeply nested expression trees that have many similarities.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BoolSymbolicSolver;

impl<'ctx> From<&'ctx Context> for BoolSymbolicSolver {
    fn from(_: &'ctx Context) -> Self {
        Self::default()
    }
}

fn is_logical_contradiction(lhs: &AnyExpr, rhs: &AnyExpr) -> bool {
    if let (&AnyExpr::Not(ref lhs), rhs) = (lhs, rhs) {
        return lhs.single_child() == rhs
    }
    if let (lhs, &AnyExpr::Not(ref rhs)) = (lhs, rhs) {
        return lhs == rhs.single_child()
    }
    false
}

impl AutoImplAnyExprTransformer for BoolSymbolicSolver {}

impl Transformer for BoolSymbolicSolver {
    fn transform_cond(&self, ite: expr::IfThenElse) -> TransformOutcome {
        // If then and else cases are equal we can lower the entire if-then-else
        // to either one. The condition can be dropped since it has no effect to
        // the result. We simply lower to the then-case in this situation.
        if ite.children.then_case == ite.children.else_case {
            return TransformOutcome::transformed(ite.children.then_case)
        }
        // If the condition is a logical-negation we can drop the negation by
        // swapping the then and else case.
        if let box IfThenElseChildren{ cond: AnyExpr::Not(not), then_case, else_case } = ite.children {
            return TransformOutcome::transformed(unsafe{
                expr::IfThenElse::new_unchecked(
                    not.into_single_child(),
                    else_case,
                    then_case
                )
            })
        }
        TransformOutcome::identity(ite)
    }

    fn transform_bool_equals(&self, bool_equals: expr::BoolEquals) -> TransformOutcome {
        // If there exists any pair that logically contradicts each other
        // then this is always false.
        if bool_equals.children()
                      .cartesian_product(bool_equals.children())
                      .any(|(lhs, rhs)| is_logical_contradiction(lhs, rhs))
        {
            return TransformOutcome::transformed(expr::BoolConst::from(false))
        }
        TransformOutcome::identity(bool_equals)
    }

    fn transform_and(&self, and: expr::And) -> TransformOutcome {
        // If there exists any pair that logically contradicts each other
        // then this is always false.
        if and.children()
              .cartesian_product(and.children())
              .any(|(lhs, rhs)| is_logical_contradiction(lhs, rhs))
        {
            return TransformOutcome::transformed(expr::BoolConst::from(false))
        }
        TransformOutcome::identity(and)
    }

    fn transform_or(&self, or: expr::Or) -> TransformOutcome {
        // If there exists any pair that logically contradicts each other
        // then this is always true.
        if or.children()
             .cartesian_product(or.children())
             .any(|(lhs, rhs)| is_logical_contradiction(lhs, rhs))
        {
            return TransformOutcome::transformed(expr::BoolConst::from(true))
        }
        TransformOutcome::identity(or)
    }

    fn transform_xor(&self, xor: expr::Xor) -> TransformOutcome {
        // If both child expressions are equal this is always false.
        if xor.children.lhs == xor.children.rhs {
            return TransformOutcome::transformed(expr::BoolConst::from(false))
        }
        // If both child expressions form a logical contradiction this is always true.
        if is_logical_contradiction(&xor.children.lhs, &xor.children.rhs) {
            return TransformOutcome::transformed(expr::BoolConst::from(true))
        }
        TransformOutcome::identity(xor)
    }

    fn transform_implies(&self, implies: expr::Implies) -> TransformOutcome {
        // If both child expressions are equal this is true.
        if implies.children.lhs == implies.children.rhs {
            return TransformOutcome::transformed(expr::BoolConst::from(true))
        }
        // If both child expressions form a logical contradiction this is
        // equal to the right-hand side child expression following these rules:
        // 
        // *  not(a) =>     a   -->      a
        // *      a  => not(a)  -->  not(a)
        if is_logical_contradiction(&implies.children.lhs, &implies.children.rhs) {
            return TransformOutcome::transformed(implies.children.rhs)
        }
        TransformOutcome::identity(implies)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prelude::*;

    type BoolSymbolicSolverSimplifier = BaseSimplifier<BoolSymbolicSolver>;

    fn create_simplifier() -> BoolSymbolicSolverSimplifier {
        BoolSymbolicSolverSimplifier::default()
    }

    fn simplify(expr: &mut AnyExpr) -> TransformEffect {
        create_simplifier().simplify(expr)
    }

    fn assert_simplified<E1, E2>(input: E1, expected: E2)
        where E1: IntoAnyExprOrError,
              E2: IntoAnyExprOrError
    {
        let mut input = input.into_any_expr_or_error().unwrap();
        let expected = expected.into_any_expr_or_error().unwrap();
        simplify(&mut input);
        assert_eq!(input, expected);
    }

    fn new_builder() -> PlainExprTreeBuilder {
        PlainExprTreeBuilder::default()
    }

    mod if_then_else {
        use super::*;

        #[test]
        fn then_else_equals() {
            let b = new_builder();
            assert_simplified(
                b.cond(
                    b.bool_var("a"),
                    b.bool_var("b"),
                    b.bool_var("b")
                ),
                b.bool_var("b")
            )
        }

        #[test]
        fn not_cond() {
            let b = new_builder();
            assert_simplified(
                b.cond(
                    b.not(b.bool_var("a")),
                    b.bool_var("b"),
                    b.bool_var("c")
                ),
                b.cond(
                    b.bool_var("a"),
                    b.bool_var("c"),
                    b.bool_var("b")
                )
            )
        }
    }

    mod bool_equals {
        use super::*;

        #[test]
        fn pair_contradiction() {
            let b = new_builder();
            assert_simplified(
                b.bool_equals_n(vec![
                    b.bool_var("a"),
                    b.bool_var("b"),
                    b.not(b.bool_var("a")),
                    b.bool_var("c")
                ]),
                b.bool_const(false)
            )
        }
    }

    mod and {
        use super::*;

        #[test]
        fn pair_contradiction() {
            let b = new_builder();
            assert_simplified(
                b.and_n(vec![
                    b.bool_var("a"),
                    b.bool_var("b"),
                    b.not(b.bool_var("a")),
                    b.bool_var("c")
                ]),
                b.bool_const(false)
            )
        }
    }

    mod or {
        use super::*;

        #[test]
        fn pair_contradiction() {
            let b = new_builder();
            assert_simplified(
                b.or_n(vec![
                    b.bool_var("a"),
                    b.bool_var("b"),
                    b.not(b.bool_var("a")),
                    b.bool_var("c")
                ]),
                b.bool_const(true)
            )
        }
    }

    mod xor {
        use super::*;

        #[test]
        fn lhs_rhs_equals() {
            let b = new_builder();
            assert_simplified(
                b.xor(
                    b.bool_var("a"),
                    b.bool_var("a")
                ),
                b.bool_const(false)
            )
        }

        #[test]
        fn a_xor_not_a() {
            let b = new_builder();
            assert_simplified(
                b.xor(
                    b.bool_var("a"),
                    b.not(b.bool_var("a"))
                ),
                b.bool_const(true)
            )
        }
    }

    mod implies {
        use super::*;

        #[test]
        fn lhs_rhs_equals() {
            let b = new_builder();
            assert_simplified(
                b.implies(
                    b.bool_var("a"),
                    b.bool_var("a")
                ),
                b.bool_const(true)
            )
        }

        #[test]
        fn not_a_implies_a() {
            let b = new_builder();
            assert_simplified(
                b.implies(
                    b.not(b.bool_var("a")),
                    b.bool_var("a")
                ),
                b.bool_var("a")
            )
        }

        #[test]
        fn a_implies_not_a() {
            let b = new_builder();
            assert_simplified(
                b.implies(
                    b.bool_var("a"),
                    b.not(b.bool_var("a"))
                ),
                b.not(b.bool_var("a"))
            )
        }
    }
}
