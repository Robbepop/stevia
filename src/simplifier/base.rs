use ast::prelude::*;
use simplifier::simplifications;

pub mod prelude {
    pub use super::{
        Simplifier,
        BaseSimplifier,
        simplify
    };
}

pub type Simplifier = BaseSimplifier<SimplifierTransformer>;

/// Simplifies the given expression until no further simplification can be applied.
pub fn simplify<'e, E>(expr: E)
    where E: Into<&'e mut AnyExpr>
{
    Simplifier::default().exhaustive_simplify(expr.into())
}

modular_ast_transformer! {
    struct SimplifierTransformer {
        _00: simplifications::InvolutionSimplifier,
        _01: simplifications::ComparisonReducer,
        _02: simplifications::BoolConstPropagator,
        _03: simplifications::BoolSymbolicSolver,
        _04: simplifications::BoolReducer,
        _05: simplifications::Normalizer,
        _06: simplifications::Flattener,
        _07: simplifications::TermConstPropagator,
        _08: simplifications::TermReducer,
        _09: simplifications::LikeTermJoiner,
        _10: simplifications::IfConstraintPropagator
    }
}

/// Simplifies expressions using the underlying base transformer.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BaseSimplifier<T>
    where T: AnyExprTransformer
{
    /// The AST traverse transformer that traverses and transforms expressions.
    traverser: TraverseTransformer<T>
}

impl<T> From<ArcContext> for BaseSimplifier<T>
where
    T: AnyExprTransformer + From<ArcContext>
{
    fn from(ctx: ArcContext) -> Self {
        Self{ traverser: TraverseTransformer::from(ctx) }
    }
}

impl<T> BaseSimplifier<T>
    where T: AnyExprTransformer
{
    /// Simplifies the given expression for a single step.
    pub fn simplify(&self, expr: &mut AnyExpr) -> TransformEffect {
        self.traverser.traverse_transform(expr)
    }

    /// Simplifies the given expression until no more simplification can
    /// be applied to it.
    /// 
    /// # Note
    /// 
    /// This might be a slow operation but always results in the best simplification.
    pub fn exhaustive_simplify(&self, expr: &mut AnyExpr) {
        while self.traverser.traverse_transform(expr) == TransformEffect::Transformed {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    modular_ast_transformer! {
        struct TestableSimplifierTransformer {
            _0: SimplifierTransformer,
            _1: simplifications::Normalizer
        }
    }
    type TestableSimplifier = BaseSimplifier<TestableSimplifierTransformer>;

    fn create_simplifier() -> TestableSimplifier {
        TestableSimplifier::default()
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
