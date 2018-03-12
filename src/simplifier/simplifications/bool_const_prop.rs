use ast::prelude::*;

pub mod prelude {
    pub use super::BoolConstPropagator;
}

/// This simplification procedure propagates constant values through boolean expressions.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
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
        if let (Some(then_const), None) = (opt_then_const, opt_else_const) {
            if then_const {
                // If then is true return equisatisfiable or: `(ite c ⊤ e)` ➔ `(or c e)`
                return TransformOutcome::transformed(
                    unsafe{ expr::Or::binary_unchecked(cond.childs.cond, cond.childs.else_case) });
            }
            else {
                // If then is false return equisatisfiable and: `(ite c ⊥ e)` ➔ `(and (not c) e)`
                return TransformOutcome::transformed(
                    unsafe{ expr::And::binary_unchecked(
                        expr::Not::new_unchecked(cond.childs.cond), cond.childs.else_case) });
            }
        }
        if let (None, Some(else_const)) = (opt_then_const, opt_else_const) {
            if else_const {
                // If else is true return equisatisfiable and: `(ite c t ⊤)` ➔ `(or (not c) t)`
                return TransformOutcome::transformed(
                    unsafe{ expr::Or::binary_unchecked(
                        expr::Not::new_unchecked(cond.childs.cond), cond.childs.then_case) });
            }
            else {
                // If else is false return equisatisfiable or: `(ite c t ⊥)` ➔ `(and c t)`
                return TransformOutcome::transformed(
                    unsafe{ expr::And::binary_unchecked(cond.childs.cond, cond.childs.then_case) });
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
        // Remove any constant true expression if existing.
        //
        // If there is only one child expression remaining we lower the
        // and expression to this single remaining child.
        if and.childs().any(|c| c.is_bool_const(true)) {
            let mut and = and;
            and.retain_children(|c| !c.is_bool_const(true));
            // The former simplifications prevent situations where there
            // are no elements left in the and expression.
            assert!(and.arity() > 0);
            if and.arity() == 1 {
                // Only a single child expression is left after removing
                // all constant true expressions so we lower the and expression
                // to its only remaining expression.
                let only_child = and.into_childs().next().unwrap();
                return TransformOutcome::transformed(only_child);
            }
            return TransformOutcome::transformed(and);
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
        // Remove any constant false expression if existing.
        //
        // If there is only one child expression remaining we lower the
        // and expression to this single remaining child.
        if or.childs().any(|c| c.is_bool_const(false)) {
            let mut or = or;
            or.retain_children(|c| !c.is_bool_const(false));
            // The former simplifications prevent situations where there
            // are no elements left in the and expression.
            assert!(or.arity() > 0);
            if or.arity() == 1 {
                // Only a single child expression is left after removing
                // all constant false expressions so we lower the and expression
                // to its only remaining expression.
                let only_child = or.into_childs().next().unwrap();
                return TransformOutcome::transformed(only_child);
            }
            return TransformOutcome::transformed(or);
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
        if let Some(c1) = lhs_opt_const {
            // If the left-hand side is false this is equal to the right-hand side.
            if !c1 {
                return TransformOutcome::transformed(xor.childs.rhs)
            }
            // If the left-hand side is true this is equal to the negated right-hand side.
            else {
                return TransformOutcome::transformed(
                    unsafe{ expr::Not::new_unchecked(xor.childs.rhs) } )
            }
        }
        if let Some(c1) = rhs_opt_const {
            // If the right-hand side is false this is equal to the right-hand side.
            if !c1 {
                return TransformOutcome::transformed(xor.childs.lhs)
            }
            // If the right-hand side is true this is equal to the negated right-hand side.
            else {
                return TransformOutcome::transformed(
                    unsafe{ expr::Not::new_unchecked(xor.childs.lhs) } )
            }
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
            // If the left-hand side is false this is always true.
            if !c1 {
                return TransformOutcome::transformed(expr::BoolConst::from(true))
            }
            // If the left-hand side is true this is equal to the right-hand side.
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
    use simplifier::prelude::*;

    modular_ast_transformer! {
        struct BoolConstPropagatorTransformer {
            _0: BoolConstPropagator
        }
    }
    type BoolConstPropagatorSimplifier = BaseSimplifier<BoolConstPropagatorTransformer>;

    fn create_simplifier() -> BoolConstPropagatorSimplifier {
        BoolConstPropagatorSimplifier::default()
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

    mod cond {
        use super::*;

        #[test]
        fn const_condition() {
            fn test_for(flag: bool) {
                let b = new_builder();
                assert_simplified(
                    b.cond(
                        b.bool_const(flag),
                        b.bool_var("a"),
                        b.bool_var("b")
                    ),
                    b.bool_var(if flag { "a" } else { "b" })
                )
            }
            test_for(true);
            test_for(false);
        }

        #[test]
        fn const_then_else() {
            fn test_for(then_case: bool, else_case: bool) {
                let b = new_builder();
                let expr = b.cond(
                    b.bool_var("a"),
                    b.bool_const(then_case),
                    b.bool_const(else_case)
                );
                if then_case == else_case {
                    return assert_simplified(expr, b.bool_const(then_case))
                }
                if then_case && !else_case {
                    return assert_simplified(expr, b.bool_var("a"))
                }
                if !then_case && else_case {
                    return assert_simplified(expr, b.not(b.bool_var("a")))
                }
            }
            test_for( true,  true);
            test_for( true, false);
            test_for(false,  true);
            test_for(false, false);
        }

        #[test]
        fn then_true_lower_or() {
            let b = new_builder();
            assert_simplified(
                b.cond(
                    b.bool_var("a"),
                    b.bool_const(true),
                    b.bool_var("b")
                ),
                b.or(
                    b.bool_var("a"),
                    b.bool_var("b")
                )
            )
        }

        #[test]
        fn then_false_lower_and() {
            let b = new_builder();
            assert_simplified(
                b.cond(
                    b.bool_var("a"),
                    b.bool_const(false),
                    b.bool_var("b")
                ),
                b.and(
                    b.not(b.bool_var("a")),
                    b.bool_var("b")
                )
            )
        }

        #[test]
        fn else_true_lower_or() {
            let b = new_builder();
            assert_simplified(
                b.cond(
                    b.bool_var("a"),
                    b.bool_var("b"),
                    b.bool_const(true)
                ),
                b.or(
                    b.not(b.bool_var("a")),
                    b.bool_var("b")
                )
            )
        }

        #[test]
        fn else_false_lower_or() {
            let b = new_builder();
            assert_simplified(
                b.cond(
                    b.bool_var("a"),
                    b.bool_var("b"),
                    b.bool_const(false)
                ),
                b.and(
                    b.bool_var("a"),
                    b.bool_var("b")
                )
            )
        }
    }

    #[test]
    fn bool_equals() {
        fn test_for(lhs: bool, rhs: bool) {
            let b = new_builder();
            assert_simplified(
                b.bool_equals(
                    b.bool_const(lhs),
                    b.bool_const(rhs)
                ),
                b.bool_const(lhs == rhs)
            )
        }
        test_for( true,  true);
        test_for( true, false);
        test_for(false,  true);
        test_for(false, false);
    }

    mod and {
        use super::*;

        #[test]
        fn drop_true() {
            let b = new_builder();
            assert_simplified(
                b.and_n(vec![
                    b.bool_const(true),
                    b.bool_var("a"),
                    b.bool_const(true),
                    b.bool_var("b")
                ]),
                b.and(
                    b.bool_var("a"),
                    b.bool_var("b")
                )
            )
        }

        #[test]
        fn drop_true_single() {
            let b = new_builder();
            assert_simplified(
                b.and_n(vec![
                    b.bool_const(true),
                    b.bool_var("a"),
                    b.bool_const(true),
                ]),
                b.bool_var("a")
            )
        }

        #[test]
        fn any_all() {
            fn test_for(lhs: bool, rhs: bool) {
                let b = new_builder();
                assert_simplified(
                    b.and(
                        b.bool_const(lhs),
                        b.bool_const(rhs)
                    ),
                    b.bool_const(lhs && rhs)
                )
            }
            test_for( true,  true);
            test_for( true, false);
            test_for(false,  true);
            test_for(false, false);
        }
    }

    mod or {
        use super::*;

        #[test]
        fn drop_true() {
            let b = new_builder();
            assert_simplified(
                b.or_n(vec![
                    b.bool_const(false),
                    b.bool_var("a"),
                    b.bool_const(false),
                    b.bool_var("b")
                ]),
                b.or(
                    b.bool_var("a"),
                    b.bool_var("b")
                )
            )
        }

        #[test]
        fn drop_true_single() {
            let b = new_builder();
            assert_simplified(
                b.or_n(vec![
                    b.bool_const(false),
                    b.bool_var("a"),
                    b.bool_const(false),
                ]),
                b.bool_var("a")
            )
        }

        #[test]
        fn any_all() {
            fn test_for(lhs: bool, rhs: bool) {
                let b = new_builder();
                assert_simplified(
                    b.or(
                        b.bool_const(lhs),
                        b.bool_const(rhs)
                    ),
                    b.bool_const(lhs || rhs)
                )
            }
            test_for( true,  true);
            test_for( true, false);
            test_for(false,  true);
            test_for(false, false);
        }
    }

    mod xor {
        use super::*;

        #[test]
        fn lhs_const() {
            fn test_for(lhs: bool) {
                let b = new_builder();
                assert_simplified(
                    b.xor(
                        b.bool_const(lhs),
                        b.bool_var("a")
                    ),
                    if lhs {
                        b.not(b.bool_var("a"))
                    }
                    else {
                        b.bool_var("a")
                    }
                )
            }
            test_for(true);
            test_for(false);
        }

        #[test]
        fn rhs_const() {
            fn test_for(rhs: bool) {
                let b = new_builder();
                assert_simplified(
                    b.xor(
                        b.bool_var("a"),
                        b.bool_const(rhs)
                    ),
                    if rhs {
                        b.not(b.bool_var("a"))
                    }
                    else {
                        b.bool_var("a")
                    }
                )
            }
            test_for(true);
            test_for(false);
        }

        #[test]
        fn pure_const() {
            fn test_for(lhs: bool, rhs: bool) {
                let b = new_builder();
                assert_simplified(
                    b.xor(
                        b.bool_const(lhs),
                        b.bool_const(rhs)
                    ),
                    b.bool_const(lhs ^ rhs)
                )
            }
            test_for( true,  true);
            test_for( true, false);
            test_for(false,  true);
            test_for(false, false);
        }
    }

    mod implies {
        use super::*;

        #[test]
        fn both_const() {
            fn test_for(lhs: bool, rhs: bool) {
                let b = new_builder();
                assert_simplified(
                    b.implies(
                        b.bool_const(lhs),
                        b.bool_const(rhs)
                    ),
                    b.bool_const(!lhs || rhs)
                )
            }
            test_for( true,  true);
            test_for( true, false);
            test_for(false,  true);
            test_for(false, false);
        }

        #[test]
        fn lhs_const() {
            fn test_for(lhs: bool) {
                let b = new_builder();
                assert_simplified(
                    b.implies(
                        b.bool_const(lhs),
                        b.bool_var("a")
                    ),
                    if !lhs {
                        b.bool_const(true)
                    }
                    else {
                        b.bool_var("a")
                    }
                )
            }
            test_for(true);
            test_for(false);
        }

        #[test]
        fn rhs_const() {
            fn test_for(rhs: bool) {
                let b = new_builder();
                assert_simplified(
                    b.implies(
                        b.bool_var("a"),
                        b.bool_const(rhs)
                    ),
                    if rhs {
                        b.bool_const(true)
                    }
                    else {
                        b.not(b.bool_var("a"))
                    }
                )
            }
            test_for(true);
            test_for(false);
        }
    }

    #[test]
    fn not() {
        fn test_for(flag: bool) {
            let b = new_builder();
            assert_simplified(
                b.not(b.bool_const(flag)),
                b.bool_const(!flag)
            )
        }
        test_for( true);
        test_for(false);
    }
}
