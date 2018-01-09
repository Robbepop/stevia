#[macro_use] mod mac;

mod checks;
mod bit_width;
mod arithmetic;

pub mod prelude {
    pub use super::{
        BitWidth,
        BitvecConst,
        Neg,
        Add,
        Mul,
        Sub,
        Udiv,
        Sdiv,
        Smod,
        Urem,
        Srem
    };
}

pub use self::bit_width::prelude::*;
pub use self::arithmetic::prelude::*;
