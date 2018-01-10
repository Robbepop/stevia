/// Reexports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        ExprKind,
        HasKind,
        Priority,
        HasPriority
    };
}

/// Represents kind of an expression.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ExprKind {
    /// The if-then-else expression kind.
    IfThenElse,
    /// The symbol expression kind
    Symbol,
    /// The equality expression kind
    Equals,

    /// The constant boolean expression kind
    BoolConst,
    /// The not boolean expression kind
    Not,
    /// The and boolean expression kind
    And,
    /// The or boolean expression kind
    Or,
    /// The implies boolean expression kind
    Implies,
    /// The xor (either-or) expression kind
    Xor,
    /// The iff (if-and-only-if) expression kind
    Iff,

    /// The constant bitvec term expression kind
    BitvecConst,
    /// The bitvec negation term expression kind
    Neg,
    /// The bitvec add term expression kind
    Add,
    /// The bitvec mul term expression kind
    Mul,
    /// The bitvec sub term expression kind
    Sub,
    /// The bitvec udiv (unsigned division) term expression kind
    UnsignedDiv,
    /// The bitvec sdiv (signed division) term expression kind
    SignedDiv,
    /// The bitvec smod (signed remainder + sign match) term expression kind
    SignedModulo,
    /// The bitvec urem (unsigned remainder) term expression kind
    UnsignedRemainder,
    /// The bitvec srem (signed remainder) term expression kind
    SignedRemainder,

    /// The bitwise-not term expression kind
    BitNot,
    /// The bitwise-and term expression kind
    BitAnd,
    /// The bitwise-or term expression kind
    BitOr,
    /// The bitwise-xor term expression kind
    BitXor,

    /// The signed greater-than-or-equals term expression kind
    SignedGreaterEquals,
    /// The signed greater-than term expression kind
    SignedGreaterThan,
    /// The signed less-than-or-equals term expression kind
    SignedLessEquals,
    /// The signed less-than term expression kind
    SignedLessThan,
    /// The unsigned greater-than-or-equals term expression kind
    UnsignedGreaterEquals,
    /// The unsigned greater-than term expression kind
    UnsignedGreaterThan,
    /// The unsigned less-than-or-equals term expression kind
    UnsignedLessEquals,
    /// The unsigned less-than term expression kind
    UnsignedLessThan,

    /// The shift-left term expression kind
    ShiftLeft,
    /// The logical shift-right term expression kind
    LogicalShiftRight,
    /// The arithmetic shift-right term expression kind
    ArithmeticShiftRight,

    /// The bitvec concatenate term expression kind
    Concat,
    /// The bitvec extraction term expression kind
    Extract,
    /// The bitvec sign-extension term expression kind
    SignExtend,
    /// The bitvec zero-extension term expression kind
    ZeroExtend,

    /// The array-read expression kind
    ArrayRead,
    /// The array-write expression kind
    ArrayWrite
}

/// This trait should be implemented by all expressions and structures that
/// represent an expression kind.
/// 
/// This is obviously true for `ExprKind` itself but also for all concrete expression types.
pub trait HasKind {
    /// Returns the kind of `self`.
    fn kind(&self) -> ExprKind;
}

impl HasKind for ExprKind {
    fn kind(&self) -> ExprKind {
        *self
    }
}

/// The priority of an expression kind.
/// 
/// This is used in order to improve normalization of symmetric
/// expression by sorting their child expressions in a static ordering.
/// 
/// The priority of an expression kind decides this ordering.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Priority(u32);

/// Expression kinds do need to implement this trait in order
/// to improve expression normalization.
pub trait HasPriority {
    /// Returns the priority of `self`.
    fn priority(&self) -> Priority;
}

const BASE_PRIORITY_FORMULA: u32    = 100;
const BASE_PRIORITY_ARITHMETIC: u32 = 200;
const BASE_PRIORITY_BITWISE: u32    = 300;
const BASE_PRIORITY_COMPARISON: u32 = 400;
const BASE_PRIORITY_SHIFT: u32      = 500;
const BASE_PRIORITY_CAST: u32       = 600;
const BASE_PRIORITY_ARRAY: u32      = 700;
const BASE_PRIORITY_GENERIC: u32    = 800;

impl HasPriority for ExprKind {
    fn priority(&self) -> Priority {
        use self::ExprKind::*;
        let prio_val = match *self {
            IfThenElse => BASE_PRIORITY_GENERIC,
            Symbol     => BASE_PRIORITY_GENERIC + 1,
            Equals     => BASE_PRIORITY_GENERIC + 2,

            BoolConst => BASE_PRIORITY_FORMULA,
            Not       => BASE_PRIORITY_FORMULA + 1,
            And       => BASE_PRIORITY_FORMULA + 2,
            Or        => BASE_PRIORITY_FORMULA + 3,
            Implies   => BASE_PRIORITY_FORMULA + 4,
            Xor       => BASE_PRIORITY_FORMULA + 5,
            Iff       => BASE_PRIORITY_FORMULA + 6,

            BitvecConst       => BASE_PRIORITY_ARITHMETIC,
            Neg               => BASE_PRIORITY_ARITHMETIC + 1,
            Add               => BASE_PRIORITY_ARITHMETIC + 2,
            Mul               => BASE_PRIORITY_ARITHMETIC + 3,
            Sub               => BASE_PRIORITY_ARITHMETIC + 4,
            UnsignedDiv       => BASE_PRIORITY_ARITHMETIC + 5,
            SignedDiv         => BASE_PRIORITY_ARITHMETIC + 6,
            SignedModulo      => BASE_PRIORITY_ARITHMETIC + 7,
            UnsignedRemainder => BASE_PRIORITY_ARITHMETIC + 8,
            SignedRemainder   => BASE_PRIORITY_ARITHMETIC + 9,

            BitNot => BASE_PRIORITY_BITWISE,
            BitAnd => BASE_PRIORITY_BITWISE + 1,
            BitOr  => BASE_PRIORITY_BITWISE + 2,
            BitXor => BASE_PRIORITY_BITWISE + 3,

            // Equals                => BASE_PRIORITY_COMPARISON, // TODO: Replace generic Equals with Bitvec Equals.
            SignedGreaterEquals   => BASE_PRIORITY_COMPARISON + 1,
            SignedGreaterThan     => BASE_PRIORITY_COMPARISON + 1,
            SignedLessEquals      => BASE_PRIORITY_COMPARISON + 2,
            SignedLessThan        => BASE_PRIORITY_COMPARISON + 3,
            UnsignedGreaterEquals => BASE_PRIORITY_COMPARISON + 4,
            UnsignedGreaterThan   => BASE_PRIORITY_COMPARISON + 5,
            UnsignedLessEquals    => BASE_PRIORITY_COMPARISON + 6,
            UnsignedLessThan      => BASE_PRIORITY_COMPARISON + 7,

            ShiftLeft            => BASE_PRIORITY_SHIFT,
            LogicalShiftRight    => BASE_PRIORITY_SHIFT + 1,
            ArithmeticShiftRight => BASE_PRIORITY_SHIFT + 2,

            Concat     => BASE_PRIORITY_CAST,
            Extract    => BASE_PRIORITY_CAST + 1,
            SignExtend => BASE_PRIORITY_CAST + 2,
            ZeroExtend => BASE_PRIORITY_CAST + 3,

            ArrayRead  => BASE_PRIORITY_ARRAY,
            ArrayWrite => BASE_PRIORITY_ARRAY + 1
        };
        Priority(prio_val)
    }
}
