
mod formulas;
mod terms;
mod variants;
mod traits;
mod iterators;
mod factory;
mod visitor;
mod pretty_printer;
pub mod prelude;

pub use self::terms::*;
pub use self::formulas::*;
pub use self::variants::{Expr, ExprKind};
pub use self::traits::ExprTrait;
pub use self::iterators::{Childs, ChildsMut, IntoChilds};

pub use self::pretty_printer::pretty_print_expr;

/// An abstraction over an indirection to an entitiy `T`.
pub type P<T> = Box<T>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Type {
	/// Boolean type.
	Boolean,
	/// Bitvector type with the given bit-width.
	BitVec(usize),
	/// Array type with the given index-width and value-width.
	Array(usize, usize)
}

impl Type {
	pub fn is_formula(self) -> bool {
		use self::Type::*;
		match self {
			Boolean => true,
			_       => false
		}
	}

	pub fn is_term(self) -> bool {
		use self::Type::*;
		match self {
			BitVec(_) => true,
			_         => false
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Equals{pub exprs: Vec<Expr>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct IfThenElse{
	pub cond: P<Expr>,
	pub then_case: P<Expr>,
	pub else_case: P<Expr>,
	pub ty: Type
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SymName(usize);

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Symbol{pub name: SymName, pub ty: Type}
