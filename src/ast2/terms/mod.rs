#[macro_use] mod mac;

mod binexpr;
mod nary_expr;
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
        BinTermExpr,
        NaryTermExpr,

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
pub use self::comparison::prelude::*;
pub use self::shift::prelude::*;
pub use self::cast::prelude::*;
pub use self::array::prelude::*;

use ast2::prelude::*;

pub trait ExprMarker {
    /// The static kind of the expression.
    const EXPR_KIND: ExprKind;
}
