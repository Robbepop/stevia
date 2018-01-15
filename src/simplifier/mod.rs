mod base;
mod simplifier;

pub mod prelude {
    pub use super::{
        TransformResult,
        Transformer,
        AnyTransformer,
        AnyExprAndTransformResult,
        BaseTransformer,
        Simplifier
    };
}

pub use self::base::prelude::*;
pub use self::simplifier::prelude::*;

use ast2::prelude::*;

create_base_transformer!{
    struct BaseTransformer;

    (_0, simplifications::InvolutionSimplifier)
}

impl Default for BaseTransformer {
    fn default() -> BaseTransformer {
        BaseTransformer{
            _0: simplifications::InvolutionSimplifier
        }
    }
}
