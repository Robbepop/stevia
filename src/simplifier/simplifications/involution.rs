use ast2::prelude::*;
use simplifier::prelude::*;

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
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct InvolutionSimplifier;

impl AutoImplAnyTransformer for InvolutionSimplifier {}

impl expr::Not {
    /// Returns `true` if this not-expression is a double negation.
    pub fn is_double_not(&self) -> bool {
        match self.child.kind() {
            ExprKind::Not => true,
            _ => false
        }
    }
}

impl expr::Neg {
    /// Returns `true` if this neg-expression is a double negation.
    pub fn is_double_neg(&self) -> bool {
        match self.child.kind() {
            ExprKind::Neg => true,
            _ => false
        }
    }
}

impl expr::BitNot {
    /// Returns `true` if this bitnot-expression is a double negation.
    pub fn is_double_bitnot(&self) -> bool {
        match self.child.kind() {
            ExprKind::BitNot => true,
            _ => false
        }
    }
}

impl Transformer for InvolutionSimplifier {
    fn transform_not(&self, not: expr::Not) -> AnyExprAndTransformResult {
        if !not.is_double_not() {
            return AnyExprAndTransformResult::identity(not)
        }
        match *not.child {
            AnyExpr::Not(notnot) => {
                AnyExprAndTransformResult::transformed(*notnot.child)
            }
            _ => unreachable!()
        }
    }

    fn transform_neg(&self, neg: expr::Neg) -> AnyExprAndTransformResult {
        if !neg.is_double_neg() {
            return AnyExprAndTransformResult::identity(neg)
        }
        match *neg.child {
            AnyExpr::Neg(negneg) => {
                AnyExprAndTransformResult::transformed(*negneg.child)
            }
            _ => unreachable!()
        }
    }

    fn transform_bitnot(&self, bitnot: expr::BitNot) -> AnyExprAndTransformResult {
        if !bitnot.is_double_bitnot() {
            return AnyExprAndTransformResult::identity(bitnot)
        }
        match *bitnot.child {
            AnyExpr::BitNot(bitnotnot) => {
                AnyExprAndTransformResult::transformed(*bitnotnot.child)
            }
            _ => unreachable!()
        }
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
