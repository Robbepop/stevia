use ast::prelude::*;

use std::collections::HashSet;

use either::Either;
use itertools::Itertools;

pub mod prelude {
    pub use super::TermSymbolicSolver;
}

/// This simplification procedure dissolves term expressions with symbolic simplifications.
/// 
/// This works best if used after an expression normalization transformation and
/// might be expensive for deeply nested expression trees that have many similarities.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct TermSymbolicSolver;

impl AutoImplAnyTransformer for TermSymbolicSolver {}

/// Returns `true` if `lhs` and `rhs` share at least one same child expression.
fn have_overlapping_children(lhs: &AnyExpr, rhs: &AnyExpr) -> bool {
    let seen = lhs.childs().collect::<HashSet<_>>();
    for child in rhs.childs() {
        if seen.contains(child) {
            return true
        }
    }
    false
}

fn join_equalities_bool(and: expr::And) -> TransformOutcome {
    // Separate equality expressions from the rest of the children.
    let (mut eqs, mut rest): (Vec<_>, Vec<_>) = and.into_childs().partition_map(|c| {
        match c {
            AnyExpr::BoolEquals(eq) => Either::Left(eq),
            other                   => Either::Right(other)
        }
    });
    // Assert that this is not called when there is nothing to do.
    assert!(!eqs.is_empty());
    let mut undecided_eqs = vec![];
    let mut needs_update = true;
    while needs_update {
        undecided_eqs.extend(eqs.drain(1..));
        needs_update = false;
        'outer_1: for eq in undecided_eqs.drain(..) {
            for eq_group in &mut eqs {
                if eq.childs().any(|c| eq_group.childs.contains(c)) {
                    eq_group.childs.extend(eq.into_childs());
                    needs_update = true;
                    continue 'outer_1;
                }
            }
            eqs.push(eq);
        }
    }
    // If rest was empty and eqs has only one element we can return it and are done.
    if rest.is_empty() && (eqs.len() == 1) {
        return TransformOutcome::transformed(eqs.pop().unwrap())
    }
    rest.extend(eqs.into_iter().map(AnyExpr::from));
    TransformOutcome::transformed(expr::And::nary(rest).unwrap())
}

fn simplify_and(and: expr::And) -> TransformOutcome {
    // If there are two or more boolean equalities within this and expression
    // there might be possibilities to join them.
    if and.childs().filter(|c| c.kind() == ExprKind::BoolEquals).count() >= 2 &&
       and.childs().tuple_combinations().any(|(lhs, rhs)| have_overlapping_children(lhs, rhs))
    {
        return join_equalities_bool(and)
    }
    TransformOutcome::identity(and)
}

impl Transformer for TermSymbolicSolver {
    fn transform_and(&self, and: expr::And) -> TransformOutcome {
        simplify_and(and)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simplifier::prelude::*;

    create_modular_ast_transformer! {
        struct TermSymbolicSolverTransformer;
        (_0, TermSymbolicSolver)
    }
    type TermSymbolicSolverSimplifier = BaseSimplifier<TermSymbolicSolverTransformer>;

    fn create_simplifier() -> TermSymbolicSolverSimplifier {
        TermSymbolicSolverSimplifier::default()
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

    mod join_equalities {
        use super::*;

        #[test]
        fn bool_no_rest() {
            let b = new_builder();
            assert_simplified(
                b.and(
                    b.bool_equals(
                        b.bool_var("a"),
                        b.bool_var("b")
                    ),
                    b.bool_equals(
                        b.bool_var("b"),
                        b.bool_var("c")
                    )
                ),
                b.bool_equals_n(vec![
                    b.bool_var("a"),
                    b.bool_var("b"),
                    b.bool_var("b"),
                    b.bool_var("c")
                ])
            )
        }

        #[test]
        fn bool_with_rest() {
            let b = new_builder();
            assert_simplified(
                b.and_n(vec![
                    b.bool_var("a"),
                    b.bool_equals(
                        b.bool_var("d"),
                        b.bool_var("e")
                    ),
                    b.bool_var("b"),
                    b.bool_equals(
                        b.bool_var("f"),
                        b.bool_var("e")
                    ),
                    b.bool_var("c"),
                ]),
                b.and_n(vec![
                    b.bool_var("a"),
                    b.bool_var("b"),
                    b.bool_var("c"),
                    b.bool_equals_n(vec![
                        b.bool_var("d"),
                        b.bool_var("e"),
                        b.bool_var("f"),
                        b.bool_var("e")
                    ]),
                ])
            )
        }

        #[test]
        fn bool_many_eqs() {
            let b = new_builder();
            assert_simplified(
                b.and_n(vec![
                    // Chunk 1
                    b.bool_equals(
                        b.bool_var("a"),
                        b.bool_var("b"),
                    ),
                    // Chunk 2
                    b.bool_equals(
                        b.bool_var("c"),
                        b.bool_var("d"),
                    ),
                    // Chunk 3
                    b.bool_equals(
                        b.bool_var("e"),
                        b.bool_var("f"),
                    ),
                    // Chunk 4
                    b.bool_equals(
                        b.bool_var("g"),
                        b.bool_var("h"),
                    ),
                    // Connects chunk 1 and 4
                    b.bool_equals(
                        b.bool_var("a"),
                        b.bool_var("h"),
                    ),
                    // Connects chunk 2 and 3
                    b.bool_equals(
                        b.bool_var("e"),
                        b.bool_var("c"),
                    ),
                ]),
                b.and(
                    b.bool_equals_n(vec![
                        b.bool_var("a"),
                        b.bool_var("b"),
                        b.bool_var("a"),
                        b.bool_var("h"),
                        b.bool_var("g"),
                        b.bool_var("h"),
                    ]),
                    b.bool_equals_n(vec![
                        b.bool_var("c"),
                        b.bool_var("d"),
                        b.bool_var("e"),
                        b.bool_var("c"),
                        b.bool_var("e"),
                        b.bool_var("f"),
                    ])
                )
            )
        }
    }
}
