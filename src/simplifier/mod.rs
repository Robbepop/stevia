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
        Simplifier
    };
}

pub use self::base::prelude::*;
pub use self::simplifier::prelude::*;
