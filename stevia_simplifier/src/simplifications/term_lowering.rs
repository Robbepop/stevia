use ast::prelude::*;

/// This simplification procedure propagates constant values through term expressions.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct TermReducer;

impl<'ctx> From<&'ctx Context> for TermReducer {
    fn from(_: &'ctx Context) -> Self {
        Self::default()
    }
}

impl AutoImplAnyExprTransformer for TermReducer {}

impl Transformer for TermReducer {
    fn transform_sub(&self, sub: expr::Sub) -> TransformOutcome {
        let (lhs, rhs) = sub.children.into_children_pair();
        TransformOutcome::transformed(
            expr::Add::binary(lhs, expr::Neg::new(rhs).unwrap()).unwrap()
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prelude::*;

    type TermReducerSimplifier = BaseSimplifier<TermReducer>;

    fn create_simplifier() -> TermReducerSimplifier {
        TermReducerSimplifier::default()
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

    mod sub {
        use super::*;

        #[test]
        fn simple() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_sub(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "y")
                ),
                b.bitvec_add(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_neg(
                        b.bitvec_var(BitvecTy::w32(), "y")
                    )
                )
            )
        }
    }
}
