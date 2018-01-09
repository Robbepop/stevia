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
    Ite,
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
    Udiv,
    /// The bitvec sdiv (signed division) term expression kind
    Sdiv,
    /// The bitvec smod (signed remainder + sign match) term expression kind
    Smod,
    /// The bitvec urem (unsigned remainder) term expression kind
    Urem,
    /// The bitvec srem (signed remainder) term expression kind
    Srem
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
// const BASE_PRIORITY_BITWISE: u32    = 300;
// const BASE_PRIORITY_COMPARISON: u32 = 400;
// const BASE_PRIORITY_SHIFT: u32      = 500;
// const BASE_PRIORITY_EXT_TRUNC: u32  = 600;
// const BASE_PRIORITY_ARRAY: u32      = 700;
const BASE_PRIORITY_GENERIC: u32    = 800;

impl HasPriority for ExprKind {
    fn priority(&self) -> Priority {
        use self::ExprKind::*;
        let prio_val = match *self {
            Ite       => BASE_PRIORITY_GENERIC,
            Symbol    => BASE_PRIORITY_GENERIC + 1,
            Equals    => BASE_PRIORITY_GENERIC + 2,

            BoolConst => BASE_PRIORITY_FORMULA,
            Not       => BASE_PRIORITY_FORMULA + 1,
            And       => BASE_PRIORITY_FORMULA + 2,
            Or        => BASE_PRIORITY_FORMULA + 3,
            Implies   => BASE_PRIORITY_FORMULA + 4,
            Xor       => BASE_PRIORITY_FORMULA + 5,

            BitvecConst => BASE_PRIORITY_ARITHMETIC,
            Neg         => BASE_PRIORITY_ARITHMETIC + 1,
            Add         => BASE_PRIORITY_ARITHMETIC + 2,
            Mul         => BASE_PRIORITY_ARITHMETIC + 3,
            Sub         => BASE_PRIORITY_ARITHMETIC + 4,
            Udiv        => BASE_PRIORITY_ARITHMETIC + 5,
            Sdiv        => BASE_PRIORITY_ARITHMETIC + 6,
            Smod        => BASE_PRIORITY_ARITHMETIC + 7,
            Urem        => BASE_PRIORITY_ARITHMETIC + 8,
            Srem        => BASE_PRIORITY_ARITHMETIC + 9
        };
        Priority(prio_val)
    }
}
