mod bit_width;
mod bitvec_const;

pub mod prelude {
    pub use super::{
        BitWidth,
        BitvecConst
    };
}

pub use self::bit_width::prelude::*;
pub use self::bitvec_const::prelude::*;
