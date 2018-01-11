mod arity;
mod child_iters;
mod binexpr_childs;
mod ty;
mod expr_kind;
mod any_expr;
mod formulas;
mod terms;
mod ite;
mod symbol;

/// An abstraction over an indirection to an entitiy `T`.
pub type P<T> = Box<T>;

pub use self::ty::{
    ArrayTy,
    BitvecTy,
    Type,
    TypeKind,
    HasType,

    common_ty,
    have_common_ty,
};
pub use self::binexpr_childs::{
    BinExprChilds
};
pub use self::child_iters::{
    ChildsIter,
    ChildsIterMut,
    IntoChildsIter,
    Childs,
    ChildsMut,
    IntoChilds
};
pub use self::terms::{
    BitWidth
};
pub use self::any_expr::{
    AnyExpr,
    IntoBoxedAnyExpr
};
pub use self::expr_kind::{
    ExprKind,
    HasKind,
    HasPriority
};
pub use self::arity::{
    HasArity
};

/// Re-exports all expression types.
pub mod expr {
    pub use super::ite::{
        IfThenElse
    };
    pub use super::symbol::{
        Symbol
    };
    pub use super::formulas::{
        BoolConst,
        BoolEquals,
        Not,
        And,
        Or,
        Xor,
        Implies
    };
    pub use super::terms::{
        BitvecConst,
        BitvecEquals,
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

        ArrayEquals,
        ArrayRead,
        ArrayWrite
    };
}

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::*;
}
