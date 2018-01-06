use ast2::prelude::*;

/// Reexports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        Expr,
        ExprKind,
        HasKind,
        HasArity
    };
}

/// Any expression.
/// 
/// There are different kinds of expressions and `Expr`
/// represents any one of them.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Ite(IfThenElse),
    Symbol(Symbol),
    Equals(Equals),

    BoolConst(BoolConst),
    Implies(Implies),
    Xor(Xor)
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
    /// The implies boolean expression kind
    Implies,
    /// The xor (either-or) expression kind
    Xor
}

/// This trait should be implemented by all expressions and structures that
/// represent an expression kind.
/// 
/// This is obviously true for `ExprKind` itself but also for all concrete expression types.
pub trait HasKind {
    /// Returns the kind of `self`.
    fn kind(&self) -> ExprKind;
}

/// Types that implement this trait can be queried for their arity.
/// 
/// The arity of an expression is equal to the number of its child expressions.
pub trait HasArity {
    /// Returns the arity of `self`.
    /// 
    /// This is equal to the number of child expressions of `self`.
    fn arity(&self) -> usize;

    /// Returns `true` if `self` has no child expressions.
    #[inline]
    fn is_leaf(&self) -> bool {
        self.arity() == 0
    }

    /// Returns `true` if `self` has child expressions.
    #[inline]
    fn has_childs(&self) -> bool {
        self.arity() > 0
    }
}

impl HasKind for ExprKind {
    fn kind(&self) -> ExprKind {
        *self
    }
}

impl HasType for Expr {
    fn ty(&self) -> Type {
        use self::Expr::*;
        match *self {
            Ite(ref ite) => ite.ty(),
            Symbol(ref symbol) => symbol.ty(),
            Equals(ref equals) => equals.ty(),

            BoolConst(ref bool_const) => bool_const.ty(),
            Implies(ref implies) => implies.ty(),
            Xor(ref xor) => xor.ty()
        }
    }
}

impl HasArity for Expr {
    fn arity(&self) -> usize {
        use self::Expr::*;
        match *self {
            Ite(ref ite) => ite.arity(),
            Symbol(ref symbol) => symbol.arity(),
            Equals(ref equals) => equals.arity(),

            BoolConst(ref bool_const) => bool_const.arity(),
            Implies(ref implies) => implies.arity(),
            Xor(ref xor) => xor.arity()
        }
    }
}

impl HasKind for Expr {
    fn kind(&self) -> ExprKind {
        use self::Expr::*;
        match *self {
            Ite(ref ite) => ite.kind(),
            Symbol(ref symbol) => symbol.kind(),
            Equals(ref equals) => equals.kind(),

            BoolConst(ref bool_const) => bool_const.kind(),
            Implies(ref implies) => implies.kind(),
            Xor(ref xor) => xor.kind()
        }
    }
}

impl Childs for Expr {
    fn childs(&self) -> ChildsIter {
        use self::Expr::*;
        match *self {
            Ite(ref ite) => ite.childs(),
            Symbol(ref symbol) => symbol.childs(),
            Equals(ref equals) => equals.childs(),

            BoolConst(ref bool_const) => bool_const.childs(),
            Implies(ref implies) => implies.childs(),
            Xor(ref xor) => xor.childs()
        }
    }
}

impl ChildsMut for Expr {
    fn childs_mut(&mut self) -> ChildsIterMut {
        use self::Expr::*;
        match *self {
            Ite(ref mut ite) => ite.childs_mut(),
            Symbol(ref mut symbol) => symbol.childs_mut(),
            Equals(ref mut equals) => equals.childs_mut(),

            BoolConst(ref mut bool_const) => bool_const.childs_mut(),
            Implies(ref mut implies) => implies.childs_mut(),
            Xor(ref mut xor) => xor.childs_mut()
        }
    }
}

impl IntoChilds for Expr {
    fn into_childs(self) -> IntoChildsIter {
        use self::Expr::*;
        match self {
            Ite(ite) => ite.into_childs(),
            Symbol(symbol) => symbol.into_childs(),
            Equals(equals) => equals.into_childs(),

            BoolConst(bool_const) => bool_const.into_childs(),
            Implies(implies) => implies.into_childs(),
            Xor(xor) => xor.into_childs()
        }
    }
}
