mod formulas;
mod terms;

use ast::SymName;

pub use self::formulas::*;
pub use self::terms::*;

use ast::prelude::*;
use ast::P;

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Equals{pub exprs: Vec<Expr>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct IfThenElse{
	pub cond: P<Expr>,
	pub then_case: P<Expr>,
	pub else_case: P<Expr>,
	pub ty: Type
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Symbol{pub name: SymName, pub ty: Type}
