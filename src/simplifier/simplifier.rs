use ast2::prelude::*;
use simplifier::prelude::*;
use simplifier::simplifications;

pub mod prelude {
    pub use super::{
        Simplifier
    };
}

pub type Simplifier = BaseSimplifier<SimplifierTransformer>;

create_modular_ast_transformer! {
    struct SimplifierTransformer;

    (_0, simplifications::InvolutionSimplifier),
    (_1, simplifications::ComparisonReducer),
    (_2, simplifications::BoolConstPropagator),
    (_3, simplifications::BoolSymbolicSolver),
    (_4, simplifications::Normalizer)
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
