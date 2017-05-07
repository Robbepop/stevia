
use ast::traits::ExprTrait;
use ast::variants::ExprVariant;
use ast::kinds::ExprKind;
use ast::iterators::{Childs, ChildsMut, IntoChilds};
use ast::{P, Type};

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct BoolConst{pub value: bool}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Not{pub inner: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct And{pub formulas: Vec<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Or{pub formulas: Vec<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Xor{pub left: P<ExprVariant>, pub right: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Iff{pub left: P<ExprVariant>, pub right: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Implies{pub assumption: P<ExprVariant>, pub implication: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct ParamBool{pub bool_var: P<ExprVariant>, pub param: P<ExprVariant>}
