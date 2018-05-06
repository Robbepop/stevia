use ast::prelude::*;

use either::Either;
use itertools::Itertools;

/// Flattens some distributive expressions such as
/// `And`, `Or`, `BitAnd`, `BitOr`, `Add`, `Mul`.
/// 
/// Flattening merges multiple sub expressions into
/// a single n-ary expression. This widens the expression's
/// context and thus enables more optimization opportunities.
/// 
/// # Examples
/// 
/// - `(and (and a b) (and c d))` is simplified to `(and a b c d)`
/// - `(or (or a b) (or c d))` is simplified to `(or a b c d)`
/// - `(add (add a b) (add c d))` is simplified to `(add a b c d)`
/// - `(mul (mul a b) (add c d))` is simplified to `(mul a b c d)`
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Flattener;

impl<'ctx> From<&'ctx Context> for Flattener {
    fn from(_: &'ctx Context) -> Self {
        Self::default()
    }
}

impl AutoImplAnyExprTransformer for Flattener {}

macro_rules! flattening_impl_for {
    ($varname:ident: $typename:ident) => {{
        // Do nothing if there exists no child expression with equal kind.
        if $varname.children().all(|c| c.kind() != ExprKind::$typename) {
            return TransformOutcome::identity($varname);
        }
        // There exist at least one child that can be flattened.
        let (sames, mut rest): (Vec<_>, Vec<_>) = $varname.into_children().partition_map(|c| {
            match c {
                AnyExpr::$typename(same) => Either::Left(same),
                other                    => Either::Right(other)
            }
        });
        assert!(sames.len() > 0);
        for same in sames {
            rest.extend(same.into_children());
        }
        let result = expr::$typename::nary(rest).unwrap();
        TransformOutcome::transformed(result)
    }};
}

impl Transformer for Flattener {
    fn transform_and(&self, and: expr::And) -> TransformOutcome {
        flattening_impl_for!(and: And)
    }

    fn transform_or(&self, or: expr::Or) -> TransformOutcome {
        flattening_impl_for!(or: Or)
    }

    fn transform_bitand(&self, bitand: expr::BitAnd) -> TransformOutcome {
        flattening_impl_for!(bitand: BitAnd)
    }

    fn transform_bitor(&self, bitor: expr::BitOr) -> TransformOutcome {
        flattening_impl_for!(bitor: BitOr)
    }

    fn transform_add(&self, add: expr::Add) -> TransformOutcome {
        flattening_impl_for!(add: Add)
    }

    fn transform_mul(&self, mul: expr::Mul) -> TransformOutcome {
        flattening_impl_for!(mul: Mul)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simplifier::prelude::*;

    type FlatteningTransformerSimplifier = BaseSimplifier<Flattener>;

    fn create_simplifier() -> FlatteningTransformerSimplifier {
        FlatteningTransformerSimplifier::default()
    }

    fn simplify(expr: &mut AnyExpr) -> TransformEffect {
        create_simplifier().simplify(expr)
    }

    fn new_builder() -> PlainExprTreeBuilder {
        PlainExprTreeBuilder::default()
    }

    macro_rules! impl_bool_flattening_test {
        ($build:ident, $build_n:ident) => {{
            let b = new_builder();
            let mut input = b.$build(
                b.$build(
                    b.bool_var("a"),
                    b.bool_var("b")
                ),
                b.$build(
                    b.bool_var("c"),
                    b.bool_var("d")
                )
            ).unwrap();
            let expected = b.$build_n(vec![
                b.bool_var("a"),
                b.bool_var("b"),
                b.bool_var("c"),
                b.bool_var("d")
            ]).unwrap();
            simplify(&mut input);
            assert_eq!(input, expected);
        }};
    }

    mod and {
        use super::*;

        #[test]
        fn simple() {
            impl_bool_flattening_test!(and, and_n);
        }
    }

    mod or {
        use super::*;

        #[test]
        fn simple() {
            impl_bool_flattening_test!(or, or_n);
        }
    }

    macro_rules! impl_term_flattening_test {
        ($build:ident, $build_n:ident) => {{
            let b = new_builder();
            let mut input = b.$build(
                b.$build(
                    b.bitvec_var(BitvecTy::w32(), "v"),
                    b.bitvec_var(BitvecTy::w32(), "w")
                ),
                b.$build(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "y")
                )
            ).unwrap();
            let expected = b.$build_n(vec![
                b.bitvec_var(BitvecTy::w32(), "v"),
                b.bitvec_var(BitvecTy::w32(), "w"),
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_var(BitvecTy::w32(), "y")
            ]).unwrap();
            simplify(&mut input);
            assert_eq!(input, expected);
        }};
    }

    mod add {
        use super::*;

        #[test]
        fn simple() {
            impl_term_flattening_test!(bitvec_add, bitvec_add_n);
        }
    }

    mod mul {
        use super::*;

        #[test]
        fn simple() {
            impl_term_flattening_test!(bitvec_mul, bitvec_mul_n);
        }
    }

    mod bitand {
        use super::*;

        #[test]
        fn simple() {
            impl_term_flattening_test!(bitvec_and, bitvec_and_n);
        }
    }

    mod bitor {
        use super::*;

        #[test]
        fn simple() {
            impl_term_flattening_test!(bitvec_or, bitvec_or_n);
        }
    }
}
