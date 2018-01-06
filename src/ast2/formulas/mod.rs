mod bool_const;
mod xor;

pub mod prelude {
    pub use super::{
        BoolConst,
        Xor
    };
}

pub use self::bool_const::prelude::*;
pub use self::xor::prelude::*;
