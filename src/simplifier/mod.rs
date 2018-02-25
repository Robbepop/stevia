#[macro_use]
mod simplifier;
mod simplifications;

pub mod prelude {
    pub use super::{
        Simplifier,
        BaseSimplifier
    };
}

pub use self::simplifier::prelude::*;
