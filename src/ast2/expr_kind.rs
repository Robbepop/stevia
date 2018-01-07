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
    BitvecConst
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
            Ite       => 0 + BASE_PRIORITY_GENERIC,
            Symbol    => 1 + BASE_PRIORITY_GENERIC,
            Equals    => 2 + BASE_PRIORITY_GENERIC,

            BoolConst => 0 + BASE_PRIORITY_FORMULA,
            Not       => 1 + BASE_PRIORITY_FORMULA,
            And       => 2 + BASE_PRIORITY_FORMULA,
            Or        => 3 + BASE_PRIORITY_FORMULA,
            Implies   => 4 + BASE_PRIORITY_FORMULA,
            Xor       => 5 + BASE_PRIORITY_FORMULA,

            BitvecConst => 0 + BASE_PRIORITY_ARITHMETIC
        };
        Priority(prio_val)
    }
}
