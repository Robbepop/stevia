use ast2::prelude::*;
use simplifier::prelude::*;

pub mod prelude {
    pub use super::{
        Simplifier
    };
}

/// Simplifies expressions using the underlying base transformer.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Simplifier {
    /// The base transformer for expressions used by this simplifier.
    transformer: BaseTransformer
}

impl Default for Simplifier {
    fn default() -> Simplifier {
        Simplifier{
            transformer: BaseTransformer::default()
        }
    }
}

impl Simplifier {
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
