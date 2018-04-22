mod binexpr;
mod nary_expr;
mod bit_width;
mod arithmetic;
mod bitwise;
mod cmp_expr;
mod bitvec_equals;
mod shift;
mod cast;
mod array;
mod bitvec;

pub use self::bitvec::{
    Bitvec,
    BitvecError,
    BitvecResult
};

pub mod prelude {
    pub use super::{
        CastError,
        CastErrorKind,
        CastResult,

        BinTermExpr,
        NaryTermExpr,
        ArrayReadChildren,
        AnyExtendExpr,

        BitWidth,
        BitvecConst,
        Neg,
        Add,
        Mul,
        Sub,
        UnsignedDiv,
        SignedDiv,
        SignedModulo,
        UnsignedRemainder,
        SignedRemainder,

        BitNot,
        BitAnd,
        BitOr,
        BitXor,

        ComparisonExpr,
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

pub use self::binexpr::prelude::*;
pub use self::nary_expr::prelude::*;
pub use self::bit_width::prelude::*;
pub use self::arithmetic::prelude::*;
pub use self::bitwise::prelude::*;
pub use self::cmp_expr::prelude::*;
pub use self::bitvec_equals::prelude::*;
pub use self::shift::prelude::*;
pub use self::cast::prelude::*;
pub use self::array::prelude::*;
