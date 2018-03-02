use ast::prelude::*;

use either::Either;

pub mod prelude {
    pub use super::TermConstPropagator;
}

/// This simplification procedure propagates constant values through boolean expressions.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct TermConstPropagator;

impl AutoImplAnyTransformer for TermConstPropagator {}

fn simplify_neg(neg: expr::Neg) -> TransformOutcome {
    // If the child expression is a constant value, simply negate it.
    if let box AnyExpr::BitvecConst(mut bv_const) = neg.child {
        bv_const.val.negate();
        return TransformOutcome::transformed(bv_const)
    }
    TransformOutcome::identity(neg)
}

fn simplify_bitnot(bitnot: expr::BitNot) -> TransformOutcome {
    // If the child expression is a constant value, simply bit-negate it.
    if let box AnyExpr::BitvecConst(mut bv_const) = bitnot.child {
        bv_const.val.bitnot();
        return TransformOutcome::transformed(bv_const)
    }
    TransformOutcome::identity(bitnot)
}

fn simplify_add(add: expr::Add) -> TransformOutcome {
    // We need to mutate add perhaps.
    let mut add = add;
    // Remove all zeros from this add as their are the additive neutral element and have
    // no effect besides wasting memory.
    if add.childs().filter_map(|c| c.get_if_bitvec_const()).filter(|c| c.is_zero()).count() > 0 {
        add.retain_children(|c| c.get_if_bitvec_const().map_or(true, |c| !c.is_zero()));
        match add.arity() {
            0 => return TransformOutcome::transformed(expr::BitvecConst::zero(add.bitvec_ty)),
            1 => return TransformOutcome::transformed(add.into_childs().next().unwrap()),
            _ => ()
        }
    }
    // If there exist at least two constant child expressions within this and expression
    // we can evaluate their sum and replace the constant child expressions with it.
    if add.childs().filter(|c| c.get_if_bitvec_const().is_some()).count() >= 2 {
        // Split const and non-const child expressions.
        let (consts, mut rest): (Vec<_>, Vec<_>) = add.into_childs().partition_map(|c| {
            match c {
                AnyExpr::BitvecConst(c) => Either::Left(c.val),
                other                   => Either::Right(other)
            }
        });
        assert!(consts.len() > 0);
        use itertools::Itertools;
        // Evalute the sum of all constant expressions.
        let sum = consts.into_iter().fold1(|mut lhs, rhs| { lhs += &rhs; lhs }).unwrap();
        // If the rest is empty and thus the sum is the only child expression remaining
        // we can replace the entire and with the sum. Otherwise we just reconstruct the
        // and expression with the new sum.
        let result = if rest.is_empty() {
            AnyExpr::from(expr::BitvecConst::from(sum))
        }
        else {
            rest.push(AnyExpr::from(expr::BitvecConst::from(sum)));
            AnyExpr::from(expr::Add::nary(rest).unwrap())
        };
        return TransformOutcome::transformed(result)
    }
    TransformOutcome::identity(add)
}

fn simplify_sub(sub: expr::Sub) -> TransformOutcome {
    // If both child expressions are const bitvectors we can simplify this to
    // the result of their subtraction.
    if let box BinExprChilds{ lhs: AnyExpr::BitvecConst(lhs), rhs: AnyExpr::BitvecConst(rhs) } = sub.childs {
        let result_udiv = lhs.val.into_checked_sub(&rhs.val).unwrap();
        return TransformOutcome::transformed(expr::BitvecConst::from(result_udiv))
    }
    // If the left-hand side is constant zero we can simplify this subtraction
    // to the negated right-hand side.
    if let Some(lval) = sub.childs.lhs.get_if_bitvec_const() {
        if lval.is_zero() {
            let negated_rhs = expr::Neg::new(sub.childs.rhs).unwrap();
            return TransformOutcome::transformed(negated_rhs)
        }
    }
    // If the right-hand side is constant zero we can simplify this subtraction
    // to the left-hand side.
    if let Some(rval) = sub.childs.rhs.get_if_bitvec_const() {
        if rval.is_zero() {
            return TransformOutcome::transformed(sub.childs.lhs)
        }
    }
    TransformOutcome::identity(sub)
}

fn simplify_mul(mul: expr::Mul) -> TransformOutcome {
    // If there exist a const zero child expression the entire multiplication is zero.
    if mul.childs().filter_map(|c| c.get_if_bitvec_const()).filter(|c| c.is_zero()).count() > 0 {
        return TransformOutcome::transformed(expr::BitvecConst::zero(mul.bitvec_ty))
    }
    // We need to mutate mul perhaps.
    let mut mul = mul;
    // Remove all ones from this mul as they are the multiplicative neutral element and have
    // no effect besides wasting memory.
    if mul.childs().filter_map(|c| c.get_if_bitvec_const()).filter(|c| c.is_one()).count() > 0 {
        mul.retain_children(|c| c.get_if_bitvec_const().map_or(true, |c| !c.is_one()));
        match mul.arity() {
            0 => return TransformOutcome::transformed(expr::BitvecConst::one(mul.bitvec_ty)),
            1 => return TransformOutcome::transformed(mul.into_childs().next().unwrap()),
            _ => ()
        }
    }
    // If there exist at least two constant child expressions within this and expression
    // we can evaluate their product and replace the constant child expressions with it.
    if mul.childs().filter(|c| c.get_if_bitvec_const().is_some()).count() >= 2 {
        // Split const and non-const child expressions.
        let (consts, mut rest): (Vec<_>, Vec<_>) = mul.into_childs().partition_map(|c| {
            match c {
                AnyExpr::BitvecConst(c) => Either::Left(c.val),
                other                   => Either::Right(other)
            }
        });
        assert!(consts.len() > 0);
        use itertools::Itertools;
        // Evalute the product of all constant expressions.
        let product = consts.into_iter().fold1(|mut lhs, rhs| { lhs *= &rhs; lhs }).unwrap();
        // If the rest is empty and thus the sum is the only child expression remaining
        // we can replace the entire and with the sum. Otherwise we just reconstruct the
        // and expression with the new sum.
        let result = if rest.is_empty() {
            AnyExpr::from(expr::BitvecConst::from(product))
        }
        else {
            rest.push(AnyExpr::from(expr::BitvecConst::from(product)));
            AnyExpr::from(expr::Mul::nary(rest).unwrap())
        };
        return TransformOutcome::transformed(result)
    }
    TransformOutcome::identity(mul)
}

macro_rules! transform_div_impl {
    ($varname:ident, $into_checked:ident) => {{
        // If both child expressions are constant bitvectors we can evaluate the division
        // and replace this division expression by the result.
        if let box BinExprChilds{ lhs: AnyExpr::BitvecConst(lhs), rhs: AnyExpr::BitvecConst(rhs) } = $varname.childs {
            let result = lhs.val.$into_checked(&rhs.val).unwrap();
            return TransformOutcome::transformed(expr::BitvecConst::from(result))
        }
        if let Some(rhs) = $varname.childs.rhs.get_if_bitvec_const() {
            // Encountered a division by zero. Stevia simply returns the left-hand side in this case.
            if rhs.is_zero() {
                warn!("Encountered a division by zero with: {:?}. \
                       Stevia simply returns the left-hand side in this case.", $varname);
                return TransformOutcome::transformed($varname.childs.lhs)
            }
            // Division by one can be replace by the left-hand side expression.
            if rhs.is_one() {
                return TransformOutcome::transformed($varname.childs.lhs)
            }
        }
        // If the left-hand side is zero the entire division can only result to zero.
        if let Some(lhs) = $varname.childs.lhs.get_if_bitvec_const() {
            // Since the left-hand side is already a zero constant we can simply take it.
            if lhs.is_zero() {
                return TransformOutcome::transformed($varname.childs.lhs)
            }
        }
    }};
}

fn simplify_udiv(udiv: expr::UnsignedDiv) -> TransformOutcome {
    transform_div_impl!(udiv, into_checked_udiv);
    TransformOutcome::identity(udiv)
}

fn simplify_sdiv(sdiv: expr::SignedDiv) -> TransformOutcome {
    transform_div_impl!(sdiv, into_checked_sdiv);
    TransformOutcome::identity(sdiv)
}

fn simplify_bitand(bitand: expr::BitAnd) -> TransformOutcome {
    // TODO: implement
    TransformOutcome::identity(bitand)
}

fn simplify_bitor(bitor: expr::BitOr) -> TransformOutcome {
    // TODO: implement
    TransformOutcome::identity(bitor)
}

fn simplify_bitxor(bitxor: expr::BitXor) -> TransformOutcome {
    // TODO: implement
    TransformOutcome::identity(bitxor)
}

fn simplify_shl(shl: expr::ShiftLeft) -> TransformOutcome {
    // TODO: implement
    TransformOutcome::identity(shl)
}

fn simplify_lshr(lshr: expr::LogicalShiftRight) -> TransformOutcome {
    // TODO: implement
    TransformOutcome::identity(lshr)
}

fn simplify_ashr(ashr: expr::ArithmeticShiftRight) -> TransformOutcome {
    // TODO: implement
    TransformOutcome::identity(ashr)
}

fn simplify_slt(slt: expr::SignedLessThan) -> TransformOutcome {
    // If both child expressions are constant we can compute the result.
    if let box BinExprChilds{ lhs: AnyExpr::BitvecConst(lhs), rhs: AnyExpr::BitvecConst(rhs) } = slt.childs {
        let result = lhs.val.checked_slt(&rhs.val).unwrap();
        return TransformOutcome::transformed(expr::BoolConst::from(result))
    }
    TransformOutcome::identity(slt)
}

fn simplify_ult(ult: expr::UnsignedLessThan) -> TransformOutcome {
    // If both child expressions are constant we can compute the result.
    if let box BinExprChilds{ lhs: AnyExpr::BitvecConst(lhs), rhs: AnyExpr::BitvecConst(rhs) } = ult.childs {
        let result = lhs.val.checked_ult(&rhs.val).unwrap();
        return TransformOutcome::transformed(expr::BoolConst::from(result))
    }
    TransformOutcome::identity(ult)
}

impl Transformer for TermConstPropagator {
    fn transform_neg(&self, neg: expr::Neg) -> TransformOutcome {
        simplify_neg(neg)
    }

    fn transform_bitnot(&self, bitnot: expr::BitNot) -> TransformOutcome {
        simplify_bitnot(bitnot)
    }

    fn transform_add(&self, add: expr::Add) -> TransformOutcome {
        simplify_add(add)
    }

    fn transform_sub(&self, sub: expr::Sub) -> TransformOutcome {
        simplify_sub(sub)
    }

    fn transform_mul(&self, mul: expr::Mul) -> TransformOutcome {
        simplify_mul(mul)
    }

    fn transform_udiv(&self, udiv: expr::UnsignedDiv) -> TransformOutcome {
        simplify_udiv(udiv)
    }

    fn transform_sdiv(&self, sdiv: expr::SignedDiv) -> TransformOutcome {
        simplify_sdiv(sdiv)
    }

    fn transform_bitand(&self, bitand: expr::BitAnd) -> TransformOutcome {
        simplify_bitand(bitand)
    }

    fn transform_bitor(&self, bitor: expr::BitOr) -> TransformOutcome {
        simplify_bitor(bitor)
    }

    fn transform_bitxor(&self, bitxor: expr::BitXor) -> TransformOutcome {
        simplify_bitxor(bitxor)
    }

    fn transform_shl(&self, shl: expr::ShiftLeft) -> TransformOutcome {
        simplify_shl(shl)
    }

    fn transform_lshr(&self, lshr: expr::LogicalShiftRight) -> TransformOutcome {
        simplify_lshr(lshr)
    }

    fn transform_ashr(&self, ashr: expr::ArithmeticShiftRight) -> TransformOutcome {
        simplify_ashr(ashr)
    }

    fn transform_slt(&self, slt: expr::SignedLessThan) -> TransformOutcome {
        simplify_slt(slt)
    }

    fn transform_ult(&self, ult: expr::UnsignedLessThan) -> TransformOutcome {
        simplify_ult(ult)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simplifier::prelude::*;

    create_modular_ast_transformer! {
        struct TermConstPropagatorTransformer;
        (_0, TermConstPropagator)
    }
    type TermConstPropagatorSimplifier = BaseSimplifier<TermConstPropagatorTransformer>;

    fn create_simplifier() -> TermConstPropagatorSimplifier {
        TermConstPropagatorSimplifier::default()
    }

    fn simplify(expr: &mut AnyExpr) -> TransformEffect {
        create_simplifier().simplify(expr)
    }

    mod neg {
        use super::*;

        #[test]
        fn simple() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_neg(b.bitvec_const(BitvecTy::w32(), 42)).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_const(BitvecTy::w32(), -42).unwrap();
            assert_eq!(expr, expected);
        }
    }

    mod bitnot {
        use super::*;

        #[test]
        fn simple() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_not(b.bitvec_const(BitvecTy::w8(), 0b0110_1100_u8)).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_const(BitvecTy::w8(), 0b1001_0011_u8).unwrap();
            assert_eq!(expr, expected);
        }
    }

    mod add {
        use super::*;

        #[test]
        fn all_const() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_add_n(vec![
                b.bitvec_const(BitvecTy::w32(), 5),
                b.bitvec_const(BitvecTy::w32(), 7),
                b.bitvec_const(BitvecTy::w32(), 3)
            ]).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_const(BitvecTy::w32(), 15).unwrap();
            assert_eq!(expr, expected);
        }

        #[test]
        fn some_const() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_add_n(vec![
                b.bitvec_const(BitvecTy::w32(), 1337),
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_const(BitvecTy::w32(), 42)
            ]).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_add(
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_const(BitvecTy::w32(), 1379) // swapped since pushed back
            ).unwrap();
            assert_eq!(expr, expected);
        }

        #[test]
        fn some_const_with_zero() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_add_n(vec![
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_const(BitvecTy::w32(), 0),
                b.bitvec_var(BitvecTy::w32(), "y"),
                b.bitvec_const(BitvecTy::w32(), 42)
            ]).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_add_n(vec![
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_var(BitvecTy::w32(), "y"),
                b.bitvec_const(BitvecTy::w32(), 42)
            ]).unwrap();
            assert_eq!(expr, expected);
        }

        #[test]
        fn binary_with_zero() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_add_n(vec![
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_const(BitvecTy::w32(), 0),
            ]).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_var(BitvecTy::w32(), "x").unwrap();
            assert_eq!(expr, expected);
        }

        #[test]
        fn eliminate_zeros() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_add_n(vec![
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_const(BitvecTy::w32(), 0),
                b.bitvec_var(BitvecTy::w32(), "y"),
                b.bitvec_const(BitvecTy::w32(), 0)
            ]).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_add(
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_var(BitvecTy::w32(), "y"),
            ).unwrap();
            assert_eq!(expr, expected);
        }
    }

    mod sub {
        use super::*;

        #[test]
        fn both_const() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_sub(
                b.bitvec_const(BitvecTy::w32(), 12),
                b.bitvec_const(BitvecTy::w32(), 5)
            ).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_const(BitvecTy::w32(), 7).unwrap();
            assert_eq!(expr, expected);
        }

        #[test]
        fn lhs_zero() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_sub(
                b.bitvec_const(BitvecTy::w32(), 0),
                b.bitvec_var(BitvecTy::w32(), "x")
            ).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_neg(b.bitvec_var(BitvecTy::w32(), "x")).unwrap();
            assert_eq!(expr, expected);
        }

        #[test]
        fn rhs_zero() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_sub(
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_const(BitvecTy::w32(), 0)
            ).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_var(BitvecTy::w32(), "x").unwrap();
            assert_eq!(expr, expected);
        }
    }

    mod mul {
        use super::*;

        #[test]
        fn identify_zero() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_mul_n(vec![
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_const(BitvecTy::w32(), 0),
                b.bitvec_var(BitvecTy::w32(), "y")
            ]).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_const(BitvecTy::w32(), 0).unwrap();
            assert_eq!(expr, expected);
        }

        #[test]
        fn identify_zero_with_const() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_mul_n(vec![
                b.bitvec_const(BitvecTy::w32(), 42),
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_const(BitvecTy::w32(), 0)
            ]).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_const(BitvecTy::w32(), 0).unwrap();
            assert_eq!(expr, expected);
        }

        #[test]
        fn binary_with_one() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_mul_n(vec![
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_const(BitvecTy::w32(), 1),
            ]).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_var(BitvecTy::w32(), "x").unwrap();
            assert_eq!(expr, expected);
        }

        #[test]
        fn eliminate_ones() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_mul_n(vec![
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_const(BitvecTy::w32(), 1),
                b.bitvec_var(BitvecTy::w32(), "y"),
                b.bitvec_const(BitvecTy::w32(), 1)
            ]).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_mul(
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_var(BitvecTy::w32(), "y"),
            ).unwrap();
            assert_eq!(expr, expected);
        }

        #[test]
        fn all_const() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_mul_n(vec![
                b.bitvec_const(BitvecTy::w32(), 5),
                b.bitvec_const(BitvecTy::w32(), 7),
                b.bitvec_const(BitvecTy::w32(), 3)
            ]).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_const(BitvecTy::w32(), 105).unwrap();
            assert_eq!(expr, expected);
        }

        #[test]
        fn some_const() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_mul_n(vec![
                b.bitvec_const(BitvecTy::w32(), 11),
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_const(BitvecTy::w32(), 7)
            ]).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_mul(
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_const(BitvecTy::w32(), 77) // swapped since pushed back
            ).unwrap();
            assert_eq!(expr, expected);
        }

        #[test]
        fn some_const_with_one() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_mul_n(vec![
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_const(BitvecTy::w32(), 1),
                b.bitvec_var(BitvecTy::w32(), "y"),
                b.bitvec_const(BitvecTy::w32(), 42)
            ]).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_mul_n(vec![
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_var(BitvecTy::w32(), "y"),
                b.bitvec_const(BitvecTy::w32(), 42)
            ]).unwrap();
            assert_eq!(expr, expected);
        }
    }

    macro_rules! div_test_impls {
        ($name:ident, $builder:ident) => {
            #[test]
            fn division_by_zero() {
                let b = PlainExprTreeBuilder::default();
                let mut expr = b.bitvec_udiv(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0)
                ).unwrap();
                simplify(&mut expr);
                let expected = b.bitvec_var(BitvecTy::w32(), "x").unwrap();
                assert_eq!(expr, expected);
            }

            #[test]
            fn division_by_one() {
                let b = PlainExprTreeBuilder::default();
                let mut expr = b.bitvec_udiv(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 1)
                ).unwrap();
                simplify(&mut expr);
                let expected = b.bitvec_var(BitvecTy::w32(), "x").unwrap();
                assert_eq!(expr, expected);
            }

            #[test]
            fn lhs_is_zero() {
                let b = PlainExprTreeBuilder::default();
                let mut expr = b.bitvec_udiv(
                    b.bitvec_const(BitvecTy::w32(), 0),
                    b.bitvec_var(BitvecTy::w32(), "x")
                ).unwrap();
                simplify(&mut expr);
                let expected = b.bitvec_const(BitvecTy::w32(), 0).unwrap();
                assert_eq!(expr, expected);
            }

            #[test]
            fn both_const() {
                fn test_for(lhs: u32, rhs: u32, result: u32) {
                    let b = PlainExprTreeBuilder::default();
                    let mut expr = b.bitvec_udiv(
                        b.bitvec_const(BitvecTy::w32(), lhs),
                        b.bitvec_const(BitvecTy::w32(), rhs)
                    ).unwrap();
                    simplify(&mut expr);
                    let expected = b.bitvec_const(BitvecTy::w32(), result).unwrap();
                    assert_eq!(expr, expected);
                }
                test_for(35, 7, 5);
                test_for(41, 3, 13);
            }
        };
    }

    mod udiv {
        use super::*;

        div_test_impls!(udiv, bitvec_udiv);
    }

    mod sdiv {
        use super::*;

        div_test_impls!(sdiv, bitvec_sdiv);
    }

    mod slt {
        use super::*;

        #[test]
        fn both_const() {
            fn test_for(lhs: i32, rhs: i32) {
                let b = PlainExprTreeBuilder::default();
                let mut expr = b.bitvec_slt(
                    b.bitvec_const(BitvecTy::w32(), lhs),
                    b.bitvec_const(BitvecTy::w32(), rhs),
                ).unwrap();
                simplify(&mut expr);
                let expected = b.bool_const(lhs < rhs).unwrap();
                assert_eq!(expr, expected);
            }
            test_for(0, 1337);
            test_for(15, 16);
            test_for(15, -16);
            test_for(42, 41);
            test_for(7, 7);
            test_for(-1, 0);
            test_for(10, -10);
        }
    }

    mod ult {
        use super::*;

        #[test]
        fn both_const() {
            fn test_for(lhs: u32, rhs: u32) {
                let b = PlainExprTreeBuilder::default();
                let mut expr = b.bitvec_ult(
                    b.bitvec_const(BitvecTy::w32(), lhs),
                    b.bitvec_const(BitvecTy::w32(), rhs),
                ).unwrap();
                simplify(&mut expr);
                let expected = b.bool_const(lhs < rhs).unwrap();
                assert_eq!(expr, expected);
            }
            test_for(0, 1337);
            test_for(15, 16);
            test_for(42, 41);
            test_for(7, 7);
        }
    }
}
