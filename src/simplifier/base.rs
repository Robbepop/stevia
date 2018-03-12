use ast::prelude::*;
use simplifier::simplifications;

pub mod prelude {
    pub use super::{
        Simplifier,
        BaseSimplifier
    };
}

pub type Simplifier = BaseSimplifier<SimplifierTransformer>;

create_modular_ast_transformer! {
    struct SimplifierTransformer;

    (_0, simplifications::InvolutionSimplifier),
    (_1, simplifications::ComparisonReducer),
    (_2, simplifications::BoolConstPropagator),
    (_3, simplifications::BoolSymbolicSolver),
    (_4, simplifications::BoolReducer),
    (_5, simplifications::Normalizer),
    (_6, simplifications::Flattener),
    (_7, simplifications::TermConstPropagator),
    (_8, simplifications::TermReducer),
    (_9, simplifications::LikeTermJoiner)
}

/// Simplifies expressions using the underlying base transformer.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BaseSimplifier<Transformer>
    where Transformer: AnyTransformer
{
    /// The base transformer for expressions used by this simplifier.
    transformer: Transformer
}

impl<Transformer> BaseSimplifier<Transformer>
    where Transformer: AnyTransformer
{
    /// Simplifies the given expression for a single step.
    pub fn simplify(&self, expr: &mut AnyExpr) -> TransformEffect {
        self.transformer.transform_any_expr(expr)
    }

    /// Simplifies the given expression until no more simplification can
    /// be applied to it.
    /// 
    /// # Note
    /// 
    /// This might be a slow operation but always results in the best simplification.
    pub fn exhaustive_simplify(&self, expr: &mut AnyExpr) {
        while self.transformer.transform_any_expr(expr) == TransformEffect::Transformed {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_simplifier() -> Simplifier {
        Simplifier::default()
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
    fn integration_01() {
        let b = new_builder();
        assert_simplified(
            b.bitvec_add_n(vec![
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_const(BitvecTy::w32(), 42_i32),
                b.bitvec_sub(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "y")
                ),
                b.bitvec_mul(
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_neg(
                        b.bitvec_const(BitvecTy::w32(), 5_i32)
                    )
                ),
                b.bitvec_neg(
                    b.bitvec_add_n(vec![
                        b.bitvec_var(BitvecTy::w32(), "x"),
                        b.bitvec_const(BitvecTy::w32(), 10_u32),
                        b.bitvec_var(BitvecTy::w32(), "y")
                    ])
                )
            ]),
            b.bitvec_add_n(vec![
                b.bitvec_const(BitvecTy::w32(), 32_u32),
                b.bitvec_mul(
                    b.bitvec_const(BitvecTy::w32(), -7_i32),
                    b.bitvec_var(BitvecTy::w32(), "y")
                ),
                b.bitvec_var(BitvecTy::w32(), "x")
            ])
        )
    }
}
