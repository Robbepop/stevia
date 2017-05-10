
mod errors;
mod formulas;
mod terms;
mod variants;
mod traits;
mod iterators;
mod factory;

#[allow(unused_variables)]
mod naive_factory;
mod visitor;
mod pretty_printer;
pub mod prelude;

pub use self::terms::*;
pub use self::formulas::*;
pub use self::variants::{Expr, ExprKind};
pub use self::traits::ExprTrait;
pub use self::iterators::{Childs, ChildsMut, IntoChilds};
pub use self::errors::{Result, AstError, ErrorKind};
pub use self::naive_factory::NaiveExprFactory;

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
	/// Returns the kind of the given type.
	/// 
	/// Type kinds abstract away internals and parameters of the given type.
	pub fn kind(self) -> TypeKind {
		use self::Type::*;
		match self {
			Boolean   => TypeKind::Boolean,
			BitVec(_) => TypeKind::BitVec,
			Array(..) => TypeKind::Array
		}
	}

	pub fn expect(self, expected: Type) -> Result<Type> {
		use self::TypeKind::*;
		use self::ErrorKind::*;
		if self == expected {
			Ok(self)
		}
		else {
			match expected.kind() {
				Boolean => Err(AstError(ExpectedBooleanType{found_type: self})),
				BitVec  => Err(AstError(ExpectedBitVecType{found_type: self})),
				Array   => Err(AstError(ExpectedArrayType{found_type: self}))
			}
		}
	}

	/// Returns the common type of two types if possible.
	/// 
	/// This in particular is useful for computing the type an if-expression
	/// infers from its child expressions that are representing the then-case
	/// and else-case respectively.
	pub fn common_of(fst: Type, snd: Type) -> Result<Type> {
		use self::Type::*;
		use self::ErrorKind::*;
		match (fst, snd) {
			(Boolean, Boolean) => Ok(Boolean),
			(BitVec(n), BitVec(m)) if n == m => Ok(BitVec(n)),
			(BitVec(n), BitVec(m)) if n != m => Err(AstError(IncompatibleBitWidth(n, m))),
			(Array(i1,v1), Array(i2,v2)) if i1 == i2 && v1 == v2 => Ok(Array(i1,v1)),
			(Array(i1,v1), Array(i2,v2)) if i1 != i2 && v1 == v2 => Err(AstError(IncompatibleIndexBitWidth(i1, i2))),
			(Array(i1,v1), Array(i2,v2)) if i1 == i2 && v1 != v2 => Err(AstError(IncompatibleValueBitWidth(v1, v2))),
			(Array(i1,v1), Array(i2,v2)) if i1 != i2 && v1 != v2 => Err(AstError(IncompatibleArrayTypes((i1,v1),(i2,v2)))),
			_ => Err(AstError(TypeKindError{given: fst.kind(), expected: fst.kind()}))
		}
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TypeKind {
	Boolean,
	BitVec,
	Array
}

impl TypeKind {
	pub fn expect(self, expected: TypeKind) -> Result<TypeKind> {
		use self::TypeKind::*;
		use self::ErrorKind::*;
		if self == expected {
			Ok(self)
		}
		else {
			match expected {
				Boolean => Err(AstError(ExpectedBooleanTypeKind{found_kind: self})),
				BitVec  => Err(AstError(ExpectedBitVecTypeKind{found_kind: self})),
				Array   => Err(AstError(ExpectedArrayTypeKind{found_kind: self}))
			}
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
