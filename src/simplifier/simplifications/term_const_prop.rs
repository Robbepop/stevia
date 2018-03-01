use ast::prelude::*;

use either::Either;

pub mod prelude {
    pub use super::TermConstPropagator;
}

/// This simplification procedure propagates constant values through boolean expressions.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct TermConstPropagator;

impl AutoImplAnyTransformer for TermConstPropagator {}

impl Transformer for TermConstPropagator {
    fn transform_neg(&self, neg: expr::Neg) -> TransformOutcome {
        // If the child expression is a constant value, simply negate it.
        if let box AnyExpr::BitvecConst(mut bv_const) = neg.child {
            bv_const.val.negate();
            return TransformOutcome::transformed(bv_const)
        }
        TransformOutcome::identity(neg)
    }

    fn transform_add(&self, add: expr::Add) -> TransformOutcome {
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

    fn transform_mul(&self, mul: expr::Mul) -> TransformOutcome {
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
}
