use ast::prelude::*;

pub mod prelude {
    pub use super::{
        InvolutionSimplifier
    };
}

/// Resolves double negations into their equivalent forms without negation.
/// 
/// # Examples
/// 
/// - `not(not(a))` is simplified to `a`
/// - `neg(neg(x))` is simplified to `x`
/// - `bitvec_not(bitvec_not(x))` is simplified to `x`
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct InvolutionSimplifier;

impl AutoImplAnyTransformer for InvolutionSimplifier {}

impl Transformer for InvolutionSimplifier {
    fn transform_not(&self, not: expr::Not) -> TransformOutcome {
        // If there is a pair of nested not we can remove both negations.
        if let box AnyExpr::Not(notnot) = not.child {
            return TransformOutcome::transformed(*notnot.child)
        }
        // For not-and we can apply De Morgan's laws: `(not (and a b))` -> `(or (not a) (not b))`
        if let box AnyExpr::And(and) = not.child {
            return TransformOutcome::transformed(
                expr::Or::nary(
                    and.into_childs()
                       .map(|c| expr::Not::new(c).unwrap())
                       .map(AnyExpr::from))
                       .unwrap()
            )
        }
        // For not-and we can apply De Morgan's laws: `(not (or a b))` -> `(and (not a) (not b))`
        if let box AnyExpr::Or(or) = not.child {
            return TransformOutcome::transformed(
                expr::And::nary(
                    or.into_childs()
                      .map(|c| expr::Not::new(c).unwrap())
                      .map(AnyExpr::from))
                      .unwrap()
            )
        }
        TransformOutcome::identity(not)
    }

    fn transform_neg(&self, neg: expr::Neg) -> TransformOutcome {
        // If there is a pair of nested negation we can remove both negations.
        if let box AnyExpr::Neg(negneg) = neg.child {
            return TransformOutcome::transformed(*negneg.child)
        }
        TransformOutcome::identity(neg)
    }

    fn transform_bitnot(&self, bitnot: expr::BitNot) -> TransformOutcome {
        // If there is a pair of nested bitwise-not we can remove both negations.
        if let box AnyExpr::BitNot(bitnotnot) = bitnot.child {
            return TransformOutcome::transformed(*bitnotnot.child)
        }
        TransformOutcome::identity(bitnot)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simplifier::prelude::*;

    create_modular_ast_transformer! {
        struct InvolutionSimplifierTransformer;
        (_0, InvolutionSimplifier)
    }
    type InvolutionSimplifierSimplifier = BaseSimplifier<InvolutionSimplifierTransformer>;

    fn create_simplifier() -> InvolutionSimplifierSimplifier {
        InvolutionSimplifierSimplifier::default()
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

    #[test]
    fn notnot() {
        let b = new_builder();
        assert_simplified(
            b.not(b.not(b.bool_var("a"))),
            b.bool_var("a")
        )
    }

    #[test]
    fn de_morgan_and() {
        let b = new_builder();
        assert_simplified(
            b.not(
                b.and(
                    b.bool_var("a"),
                    b.bool_var("b")
                )
            ),
            b.or(
                b.not(
                    b.bool_var("a")
                ),
                b.not(
                    b.bool_var("b")
                )
            )
        )
    }

    #[test]
    fn de_morgan_or() {
        let b = new_builder();
        assert_simplified(
            b.not(
                b.or(
                    b.bool_var("a"),
                    b.bool_var("b")
                )
            ),
            b.and(
                b.not(
                    b.bool_var("a")
                ),
                b.not(
                    b.bool_var("b")
                )
            )
        )
    }

    #[test]
    fn negneg() {
        let b = new_builder();
        assert_simplified(
            b.bitvec_neg(b.bitvec_neg(b.bitvec_var(BitvecTy::w32(), "x"))),
            b.bitvec_var(BitvecTy::w32(), "x")
        )
    }

    #[test]
    fn bitnotnot() {
        let b = new_builder();
        assert_simplified(
            b.bitvec_not(b.bitvec_not(b.bitvec_var(BitvecTy::w32(), "x"))),
            b.bitvec_var(BitvecTy::w32(), "x")
        )
    }
}
