#[macro_use] mod mac;

mod checks;
mod bit_width;
mod arithmetic;
mod bitwise;
mod comparison;
mod shift;
mod cast;
mod array;

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
        Srem,

        BitNot,
        BitAnd,
        BitOr,
        BitXor,

        SignedGreaterEquals,
        SignedGreaterThan,
        SignedLessEquals,
        SignedLessThan,
        UnsignedGreaterEquals,
        UnsignedGreaterThan,
        UnsignedLessEquals,
        UnsignedLessThan,

        ShiftLeft,
        LogicalShiftRight,
        ArithmeticShiftRight,

        Concat,
        Extract,
        SignExtend,
        ZeroExtend,

        ArrayRead,
        ArrayWrite
    };
}

pub use self::bit_width::prelude::*;
pub use self::arithmetic::prelude::*;
pub use self::bitwise::prelude::*;
pub use self::comparison::prelude::*;
pub use self::shift::prelude::*;
pub use self::cast::prelude::*;
pub use self::array::prelude::*;
