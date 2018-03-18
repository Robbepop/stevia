use ast::prelude::*;

use chashmap::CHashMap;
use std::rc::Rc;

pub mod prelude {
    pub use super::{
        IfConstraintPropagator
    };
}

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
/// Currently we use the `chashmap` crate from `crates.io`. This is a published utility
/// of the Redox `tfs` (next-generation file system) library. As of today (2018-03-18)
/// it is missing an important feature for better parity with `std::collections::HashMap`
/// that is required by this implementation since otherwise the compiler incorrectly
/// infers lifetimes of many parts of the program.
/// 
/// Another problem is that there currently is no elegant solution to how the seen-hashmap
/// is used throughout the recursive traversal of the expression tree.
/// Upon encountering an if-then-else expression we clone the hashmap exactly once for the
/// else-case part. The then-case part simply takes over the current hashmap, updates it,
/// traverses through the sub-tree recursively and finally removes the entry from the hashmap
/// again to not confuse other parts of the expression tree. This has the advantage of just
/// a single deep-clone per if-then-else expression and the huge disadvantage of the
/// interdependency between disjoint subtrees. This could be fixed by two deep-clones per if-then-else
/// or probably by yet another traversal strategy that may even remove all deep-clones.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct IfConstraintPropagator;

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
        propagate_if_constraint(expr, Rc::new(CHashMap::new()))
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
fn split_if_costraint<'e>(cond: &'e mut expr::IfThenElse, seen: Rc<CHashMap<&'e AnyExpr, bool>>) -> TransformEffect {
    // Create a deep clone of the hashmap and insert the condition with
    // polarity of true and false for then and else cases respectively.
    let seen_then: &CHashMap<&'e AnyExpr, bool> = &*seen;
    let seen_then = Rc::new(seen_then.clone());
    let seen_else = seen;
    let (cond, then_case, else_case) = cond.as_children_tuple_mut();
    seen_then.insert(&*cond, true);
    seen_else.insert(&*cond, false);
    // Now recursively propagate the new constraint (and all constraints before)
    // through then and else cases with their respective polarities.
    let mut effect = TransformEffect::Identity;
    effect |= propagate_if_constraint(then_case, seen_then);
    effect |= propagate_if_constraint(else_case, seen_else.clone());
    // Remove item from moved-only hashtable to not confuse other siblings
    // of the expression tree.
    seen_else.remove(&*cond);
    effect
}

/// Propagates the constraints that have already been seen recursively through the
/// given expression tree.
/// Upon encountering another if-then-else structure the propagation is split for
/// then-case and else-case respectively and propagated further.
fn propagate_if_constraint<'e>(expr: &'e mut AnyExpr, seen: Rc<CHashMap<&'e AnyExpr, bool>>) -> TransformEffect {
    // Replace the current expression with a constant value if it was already seen.
    // 
    // Since conditions of if-expressions are always of boolean type this replacement
    // is only applicable for boolean expressions.
    if expr.ty() == Type::Bool {
        if seen.contains_key(&*expr) {
            let polarity: bool = *seen.get(&*expr).unwrap();
            *expr = AnyExpr::from(expr::BoolConst::from(polarity));
            return TransformEffect::Transformed
        }
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
        effect |= propagate_if_constraint(child, seen.clone())
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
