use ast::{P, Type};
use ast::traits::ExprTrait;
use ast::variants::{Expr, ExprKind};
use ast::iterators::{Childs, ChildsMut, IntoChilds};

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct BoolConst{pub value: bool}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Not{pub inner: P<Expr>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct And{pub formulas: Vec<Expr>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Or{pub formulas: Vec<Expr>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Xor{pub left: P<Expr>, pub right: P<Expr>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Iff{pub left: P<Expr>, pub right: P<Expr>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Implies{pub assumption: P<Expr>, pub implication: P<Expr>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct ParamBool{pub bool_var: P<Expr>, pub param: P<Expr>}
