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
        if let box AnyExpr::Not(notnot) = not.child {
            return TransformOutcome::transformed(*notnot.child)
        }
        TransformOutcome::identity(not)
    }

    fn transform_neg(&self, neg: expr::Neg) -> TransformOutcome {
        if let box AnyExpr::Neg(negneg) = neg.child {
            return TransformOutcome::transformed(*negneg.child)
        }
        TransformOutcome::identity(neg)
    }

    fn transform_bitnot(&self, bitnot: expr::BitNot) -> TransformOutcome {
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
