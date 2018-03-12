use ast::prelude::*;

pub mod prelude {
    pub use super::BoolReducer;
}

/// This simplification procedure propagates constant values through boolean expressions.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BoolReducer;

impl AutoImplAnyTransformer for BoolReducer {}

impl Transformer for BoolReducer {
    fn transform_implies(&self, implies: expr::Implies) -> TransformOutcome {
        let (lhs, rhs) = implies.children.into_children_pair();
        TransformOutcome::transformed(
            expr::Or::binary(expr::Not::new(lhs).unwrap(), rhs).unwrap()
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simplifier::prelude::*;

    modular_ast_transformer! {
        struct BoolReducerTransformer {
            _0: BoolReducer
        }
    }
    type BoolReducerSimplifier = BaseSimplifier<BoolReducerTransformer>;

    fn create_simplifier() -> BoolReducerSimplifier {
        BoolReducerSimplifier::default()
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

    mod implies {
        use super::*;

        #[test]
        fn simple() {
            let b = new_builder();
            assert_simplified(
                b.implies(
                    b.bool_var("a"),
                    b.bool_var("b")
                ),
                b.or(
                    b.not(
                        b.bool_var("a")
                    ),
                    b.bool_var("b")
                )
            )
        }
    }
}