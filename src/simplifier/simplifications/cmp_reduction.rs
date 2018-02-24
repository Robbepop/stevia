use ast2::prelude::*;
use simplifier::prelude::*;

pub mod prelude {
    pub use super::{
        ComparisonReducer
    };
}

/// Reduces this `SignedGreaterEquals` to using less-than as only comparison.
fn reduce_sge_to_slt(sge: expr::SignedGreaterEquals) -> expr::Not {
    unsafe{ expr::SignedLessThan::new_unchecked(sge.childs_bitvec_ty, sge.childs) }.wrap_with_not()
}

/// Reduces this `SignedLessThan` to using less-than as only comparison.
fn reduce_sgt_to_slt(sgt: expr::SignedGreaterThan) -> expr::SignedLessThan {
    let mut sgt = sgt;
    sgt.childs.swap_childs();
    unsafe{ expr::SignedLessThan::new_unchecked(sgt.childs_bitvec_ty, sgt.childs) }
}

/// Creates a new `SignedLessEquals` expression from the given `SignedGreaterThan`.
fn reduce_sle_to_slt(sle: expr::SignedLessEquals) -> expr::Not {
    let mut sle = sle;
    sle.childs.swap_childs();
    unsafe{ expr::SignedLessThan::new_unchecked(sle.childs_bitvec_ty, sle.childs).wrap_with_not() }
}

/// Reduces this `UnsignedGreaterEquals` to using less-than as only comparison.
fn reduce_uge_to_ult(uge: expr::UnsignedGreaterEquals) -> expr::Not {
    unsafe{ expr::UnsignedLessThan::new_unchecked(uge.childs_bitvec_ty, uge.childs) }.wrap_with_not()
}

/// Reduces this `UnsignedLessThan` to using less-than as only comparison.
fn reduce_ugt_to_ult(ugt: expr::UnsignedGreaterThan) -> expr::UnsignedLessThan {
    let mut ugt = ugt;
    ugt.childs.swap_childs();
    unsafe{ expr::UnsignedLessThan::new_unchecked(ugt.childs_bitvec_ty, ugt.childs) }
}

/// Creates a new `UnsignedLessEquals` expression from the given `SignedGreaterThan`.
fn reduce_ule_to_ult(ule: expr::UnsignedLessEquals) -> expr::Not {
    let mut ule = ule;
    ule.childs.swap_childs();
    unsafe{ expr::UnsignedLessThan::new_unchecked(ule.childs_bitvec_ty, ule.childs).wrap_with_not() }
}

/// Reduces comparison expressions to less-than forms.
/// 
/// # Examples
/// 
/// - `a > b` is simplified to `b < a`
/// - `a >= b` is simplified to `not(a < b)`
/// - `a <= b` is simplified to `not(b < a)`
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ComparisonReducer;

impl AutoImplAnyTransformer for ComparisonReducer {}

impl Transformer for ComparisonReducer {
    fn transform_sge(&self, sge: expr::SignedGreaterEquals) -> TransformOutcome {
        TransformOutcome::transformed(reduce_sge_to_slt(sge))
    }

    fn transform_sgt(&self, sgt: expr::SignedGreaterThan) -> TransformOutcome {
        TransformOutcome::transformed(reduce_sgt_to_slt(sgt))
    }

    fn transform_sle(&self, sle: expr::SignedLessEquals) -> TransformOutcome {
        TransformOutcome::transformed(reduce_sle_to_slt(sle))
    }

    fn transform_uge(&self, uge: expr::UnsignedGreaterEquals) -> TransformOutcome {
        TransformOutcome::transformed(reduce_uge_to_ult(uge))
    }

    fn transform_ugt(&self, ugt: expr::UnsignedGreaterThan) -> TransformOutcome {
        TransformOutcome::transformed(reduce_ugt_to_ult(ugt))
    }

    fn transform_ule(&self, ule: expr::UnsignedLessEquals) -> TransformOutcome {
        TransformOutcome::transformed(reduce_ule_to_ult(ule))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sge() {
        let b = PlainExprTreeBuilder::default();
        let mut input = b.bitvec_sge(
            b.bitvec_var(BitvecTy::w32(), "x"),
            b.bitvec_var(BitvecTy::w32(), "y")
        ).unwrap();
        let expect = b.not(
            b.bitvec_slt(
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_var(BitvecTy::w32(), "y")
            )
        ).unwrap();
        Simplifier::default().simplify(&mut input);
        assert_eq!(input, expect);
    }

    #[test]
    fn uge() {
        let b = PlainExprTreeBuilder::default();
        let mut input = b.bitvec_uge(
            b.bitvec_var(BitvecTy::w32(), "x"),
            b.bitvec_var(BitvecTy::w32(), "y")
        ).unwrap();
        let expect = b.not(
            b.bitvec_ult(
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_var(BitvecTy::w32(), "y")
            )
        ).unwrap();
        Simplifier::default().simplify(&mut input);
        assert_eq!(input, expect);
    }

    #[test]
    fn sgt() {
        let b = PlainExprTreeBuilder::default();
        let mut input = b.bitvec_sgt(
            b.bitvec_var(BitvecTy::w32(), "x"),
            b.bitvec_var(BitvecTy::w32(), "y")
        ).unwrap();
        let expect = b.bitvec_slt(
            b.bitvec_var(BitvecTy::w32(), "y"),
            b.bitvec_var(BitvecTy::w32(), "x")
        ).unwrap();
        Simplifier::default().simplify(&mut input);
        assert_eq!(input, expect);
    }

    #[test]
    fn ugt() {
        let b = PlainExprTreeBuilder::default();
        let mut input = b.bitvec_ugt(
            b.bitvec_var(BitvecTy::w32(), "x"),
            b.bitvec_var(BitvecTy::w32(), "y")
        ).unwrap();
        let expect = b.bitvec_ult(
            b.bitvec_var(BitvecTy::w32(), "y"),
            b.bitvec_var(BitvecTy::w32(), "x")
        ).unwrap();
        Simplifier::default().simplify(&mut input);
        assert_eq!(input, expect);
    }

    #[test]
    fn sle() {
        let b = PlainExprTreeBuilder::default();
        let mut input = b.bitvec_sle(
            b.bitvec_var(BitvecTy::w32(), "x"),
            b.bitvec_var(BitvecTy::w32(), "y")
        ).unwrap();
        let expect = b.not(
            b.bitvec_slt(
                b.bitvec_var(BitvecTy::w32(), "y"),
                b.bitvec_var(BitvecTy::w32(), "x")
            )
        ).unwrap();
        Simplifier::default().simplify(&mut input);
        assert_eq!(input, expect);
    }

    #[test]
    fn ule() {
        let b = PlainExprTreeBuilder::default();
        let mut input = b.bitvec_ule(
            b.bitvec_var(BitvecTy::w32(), "x"),
            b.bitvec_var(BitvecTy::w32(), "y")
        ).unwrap();
        let expect = b.not(
            b.bitvec_ult(
                b.bitvec_var(BitvecTy::w32(), "y"),
                b.bitvec_var(BitvecTy::w32(), "x")
            )
        ).unwrap();
        Simplifier::default().simplify(&mut input);
        assert_eq!(input, expect);
    }

}
