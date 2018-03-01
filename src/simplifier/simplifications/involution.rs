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
    use simplifier::Simplifier;

    #[test]
    fn notnot() {
        let b = PlainExprTreeBuilder::default();
        let mut expr = b.not(b.not(b.bool_var("a"))).unwrap();
        Simplifier::default().simplify(&mut expr);
        assert_eq!(expr, b.bool_var("a").unwrap());
    }

    #[test]
    fn negneg() {
        let b = PlainExprTreeBuilder::default();
        let mut expr = b.bitvec_neg(b.bitvec_neg(b.bitvec_var(BitvecTy::w32(), "x"))).unwrap();
        Simplifier::default().simplify(&mut expr);
        assert_eq!(expr, b.bitvec_var(BitvecTy::w32(), "x").unwrap());
    }

    #[test]
    fn bitnotnot() {
        let b = PlainExprTreeBuilder::default();
        let mut expr = b.bitvec_not(b.bitvec_not(b.bitvec_var(BitvecTy::w32(), "x"))).unwrap();
        Simplifier::default().simplify(&mut expr);
        assert_eq!(expr, b.bitvec_var(BitvecTy::w32(), "x").unwrap());
    }
}
