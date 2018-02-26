#[macro_use]
mod base;
mod simplifications;

pub mod prelude {
    pub use super::{
        Simplifier,
        BaseSimplifier
    };
}

pub use self::base::prelude::*;
