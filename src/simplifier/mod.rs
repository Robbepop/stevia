#[macro_use]
mod base;
mod simplifier;
mod simplifications;

pub mod prelude {
    pub use super::{
        TransformEffect,
        Transformer,
        AnyTransformer,
        TransformOutcome,
        AutoImplAnyTransformer,
        BaseTransformer,
        Simplifier
    };
}

pub use self::base::prelude::*;
pub use self::simplifier::prelude::*;

use ast2::prelude::*;

create_base_transformer!{
    struct BaseTransformer;

    (_0, simplifications::InvolutionSimplifier),
    (_1, simplifications::ComparisonReducer),
    (_2, simplifications::BoolConstPropagator),
    (_3, simplifications::BoolSymbolicSolver),
    (_4, simplifications::Normalizer)
}

impl Default for BaseTransformer {
    fn default() -> BaseTransformer {
        BaseTransformer{
            _0: simplifications::InvolutionSimplifier,
            _1: simplifications::ComparisonReducer,
            _2: simplifications::BoolConstPropagator,
            _3: simplifications::BoolSymbolicSolver,
            _4: simplifications::Normalizer
        }
    }
}
