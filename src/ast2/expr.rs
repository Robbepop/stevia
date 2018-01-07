use ast2::prelude::*;

/// Reexports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        Expr,
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
    Not(Not),
    And(And),
    Or(Or),
    Implies(Implies),
    Xor(Xor),

    BitvecConst(BitvecConst),
    Neg(Neg),
    Add(Add),
    Mul(Mul)
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

impl HasType for Expr {
    fn ty(&self) -> Type {
        use self::Expr::*;
        match *self {
            Ite(ref ite) => ite.ty(),
            Symbol(ref symbol) => symbol.ty(),
            Equals(ref equals) => equals.ty(),

            BoolConst(ref bool_const) => bool_const.ty(),
            Not(ref not) => not.ty(),
            And(ref and) => and.ty(),
            Or(ref or) => or.ty(),
            Implies(ref implies) => implies.ty(),
            Xor(ref xor) => xor.ty(),

            BitvecConst(ref bitvec_const) => bitvec_const.ty(),
            Neg(ref neg) => neg.ty(),
            Add(ref add) => add.ty(),
            Mul(ref mul) => mul.ty()
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
            Not(ref not) => not.arity(),
            And(ref and) => and.arity(),
            Or(ref or) => or.arity(),
            Implies(ref implies) => implies.arity(),
            Xor(ref xor) => xor.arity(),

            BitvecConst(ref bitvec_const) => bitvec_const.arity(),
            Neg(ref neg) => neg.arity(),
            Add(ref add) => add.arity(),
            Mul(ref mul) => mul.arity()
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
            Not(ref not) => not.kind(),
            And(ref and) => and.kind(),
            Or(ref or) => or.kind(),
            Implies(ref implies) => implies.kind(),
            Xor(ref xor) => xor.kind(),

            BitvecConst(ref bitvec_const) => bitvec_const.kind(),
            Neg(ref neg) => neg.kind(),
            Add(ref add) => add.kind(),
            Mul(ref mul) => mul.kind()
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
            Not(ref not) => not.childs(),
            And(ref and) => and.childs(),
            Or(ref or) => or.childs(),
            Implies(ref implies) => implies.childs(),
            Xor(ref xor) => xor.childs(),

            BitvecConst(ref bitvec_const) => bitvec_const.childs(),
            Neg(ref neg) => neg.childs(),
            Add(ref add) => add.childs(),
            Mul(ref mul) => mul.childs()
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
            Not(ref mut not) => not.childs_mut(),
            And(ref mut and) => and.childs_mut(),
            Or(ref mut or) => or.childs_mut(),
            Implies(ref mut implies) => implies.childs_mut(),
            Xor(ref mut xor) => xor.childs_mut(),

            BitvecConst(ref mut bitvec_const) => bitvec_const.childs_mut(),
            Neg(ref mut neg) => neg.childs_mut(),
            Add(ref mut add) => add.childs_mut(),
            Mul(ref mut mul) => mul.childs_mut()
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
            Not(not) => not.into_childs(),
            And(and) => and.into_childs(),
            Or(or) => or.into_childs(),
            Implies(implies) => implies.into_childs(),
            Xor(xor) => xor.into_childs(),

            BitvecConst(bitvec_const) => bitvec_const.into_childs(),
            Neg(neg) => neg.into_childs(),
            Add(add) => add.into_childs(),
            Mul(mul) => mul.into_childs()
        }
    }
}
