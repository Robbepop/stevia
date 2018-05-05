use ast::prelude::*;

use std::collections::HashMap;

/// The If-Constraint-Propagator memorizes condition expressions of If-Then-Else constructs
/// and replaces equal expressions in the then-case and else-case with constants true and false
/// respectively.
/// 
/// This simplification thus eliminates conditions that check for properties that have been
/// already verified or falsified at the given position within the expression tree.
/// 
/// # Details
/// 
/// With the current transformer architecture this simplification cannot be fully integrated
/// into the standard transformation procedure and can only work as a post-processing step.
/// The reason for this is that it requires a more controled way of traversing through the
/// expression tree that is currently not supported by the transformer architecture.
/// 
/// # Problems with the current Design
/// 
/// Since we are using a single hashmap that is constantly updated during traversal of the
/// expression tree we cannot easily process this in parallel if we wish to in future version
/// of stevia.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct IfConstraintPropagator;

impl From<ArcContext> for IfConstraintPropagator {
    fn from(_: ArcContext) -> Self {
        IfConstraintPropagator
    }
}

impl AnyExprTransformer for IfConstraintPropagator {
    fn transform_any_expr(&self, expr: &mut AnyExpr, event: TransformEvent) -> TransformEffect {
        // This entire transformation is only allowed during the post-processing step.
        //
        // The reason is that the current transformer architecture isn't flexible enough
        // to allow for different traversing strategies through the expression tree which
        // this simplification requires to work properly.
        if event != TransformEvent::PostProcessing {
            return TransformEffect::Identity
        }
        propagate_if_constraint(expr, &mut HashMap::new())
    }

    fn transform_any_expr_into(&self, expr: AnyExpr, event: TransformEvent) -> TransformOutcome {
        let mut expr = expr;
        let effect = self.transform_any_expr(&mut expr, event);
        TransformOutcome::new(effect, expr)
    }
}

/// Called upon encountering a new if-then-else construct during if-constraint propagation.
/// 
/// This effectively splits the seen map into a then-case and else-case for true and false
/// polarity of the condition respectively and continues to traverse recursively through
/// the given expression sub tree.
fn split_if_costraint<'e>(cond: &'e mut expr::IfThenElse, seen: &mut HashMap<&'e AnyExpr, bool>) -> TransformEffect {
    let (cond, then_case, else_case) = cond.as_children_tuple_mut();
    let mut effect = TransformEffect::Identity;

    // Traverse through then-case with `true` polarity.
    seen.insert(&*cond, true);
    effect |= propagate_if_constraint(then_case, seen);

    // Traverse through else-case with `false` polarity.
    // seen.upsert(&*cond, || false, |v| *v = false);
    *seen.get_mut(&*cond).unwrap() = false;
    effect |= propagate_if_constraint(else_case, seen);

    // Remove item from moved-only hashtable to not confuse other siblings
    // of the expression tree.
    seen.remove(&*cond);

    effect
}

/// Propagates the constraints that have already been seen recursively through the
/// given expression tree.
/// Upon encountering another if-then-else structure the propagation is split for
/// then-case and else-case respectively and propagated further.
fn propagate_if_constraint<'e>(expr: &'e mut AnyExpr, seen: &mut HashMap<&'e AnyExpr, bool>) -> TransformEffect {
    // Replace the current expression with a constant value if it was already seen.
    // 
    // Since conditions of if-expressions are always of boolean type this replacement
    // is only applicable for boolean expressions.
    if expr.ty() == Type::Bool && seen.contains_key(&*expr) {
        let polarity: bool = *seen.get(&*expr).unwrap();
        *expr = AnyExpr::from(expr::BoolConst::from(polarity));
        return TransformEffect::Transformed
    }
    // For If-Then-Else expressions split traversing and memorize its condition if its
    // condition wasn't already seen.
    if let AnyExpr::IfThenElse(cond) = expr {
        if !seen.contains_key(&cond.children.cond) {
            return split_if_costraint(cond, seen)
        }
    }
    // For normal expressions simply traverse through child expressions and accumulate
    // their transform effects.
    let mut effect = TransformEffect::Identity;
    for child in expr.children_mut() {
        effect |= propagate_if_constraint(child, seen)
    }
    effect
}

#[cfg(test)]
mod tests {
    use super::*;
    use simplifier::prelude::*;
    use simplifier::simplifications;

    modular_ast_transformer! {
        struct ModularIfConstraintPropagator {
            _0: IfConstraintPropagator,
            _1: simplifications::BoolConstPropagator,
            _2: simplifications::BoolSymbolicSolver
        }
    }
    type IfConstraintPropagatorSimplifier = BaseSimplifier<ModularIfConstraintPropagator>;

    fn create_simplifier() -> IfConstraintPropagatorSimplifier {
        IfConstraintPropagatorSimplifier::default()
    }

    fn simplify(expr: &mut AnyExpr) {
        create_simplifier().exhaustive_simplify(expr)
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

    #[test]
    fn regression_dont_overlap() {
        let b = new_builder();
        let unsimplifiable =
            b.and(
                b.cond(
                    b.bool_var("a"),
                    b.cond(
                        b.bool_var("b"),
                        b.bool_var("c"),
                        b.bool_var("d")
                    ),
                    b.bool_var("e")
                ),
                b.cond(
                    b.bool_var("a"),
                    b.cond(
                        b.bool_var("b"),
                        b.bool_var("c"),
                        b.bool_var("d")
                    ),
                    b.bool_var("e")
                )
            );
        assert_simplified(
            unsimplifiable.clone(),
            unsimplifiable
        )
    }

    #[test]
    fn complex() {
        let b = new_builder();
        assert_simplified(
            b.cond(
                b.and(
                    b.bool_var("a"),
                    b.bool_var("b")
                ),
                b.cond(
                    b.and(
                        b.bool_var("a"),
                        b.bool_var("b")
                    ),
                    b.bool_var("c"),
                    b.bool_var("d")
                ),
                b.or(
                    b.and(
                        b.bool_var("a"),
                        b.bool_var("b")
                    ),
                    b.bool_var("c")
                )
            ),
            b.bool_var("c")
        )
    }
}
