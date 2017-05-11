
mod errors;
pub mod expr;
mod variants;
mod traits;
mod iterators;
mod factory;

#[allow(unused_variables)]
mod naive_factory;
mod visitor;
mod pretty_printer;
pub mod prelude;

pub use self::variants::{Expr, ExprKind};
pub use self::traits::ExprTrait;
pub use self::iterators::{Childs, ChildsMut, IntoChilds};
pub use self::errors::{Result, AstError, ErrorKind};
pub use self::factory::ExprFactory;
pub use self::naive_factory::NaiveExprFactory;

pub use self::pretty_printer::pretty_print_expr;

impl From<Expr> for Result<Expr> {
	fn from(expr: Expr) -> Result<Expr> {
		Ok(expr)
	}
}

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

	/// Returns the bitwidths of the given type if it is a bitvector type.
	/// Returns an appropriate error, otherwise.
	pub fn bitwidth(self) -> Result<usize> {
		use self::Type::*;
		match self {
			BitVec(bits) => Ok(bits),
			wrong_ty     => {
				Err(AstError(ErrorKind::ExpectedBitVecType{found_type: wrong_ty}))
			}
		}
	}

	/// Returns the common bitwidth of both given types if they are bitvec types.
	/// Returns an appropriate error, otherwise.
	pub fn common_bitwidth(fst: Type, snd: Type) -> Result<usize> {
		use self::Type::*;
		use self::ErrorKind::*;
		match (fst, snd) {
			(BitVec(n), BitVec(m)) if n == m => Ok(n),
			(BitVec(n), BitVec(m)) if n != m => Err(AstError(IncompatibleBitWidth(n, m))),
			(BitVec(_), wrong_ty ) |
			(wrong_ty , _        ) => Err(AstError(ExpectedBitVecType{found_type: wrong_ty}))
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SymName(usize);

// #[cfg(test)]
// mod tests {
	// use super::*;

	// #[test]
	// fn simple_macro() {
		// use ast::factory::ExprFactory;
		// let fab = NaiveExprFactory::new();

		// let expr1 = fab.eq(
		// 	fab.bvmul(
		// 		fab.bitvec("x", 32),
		// 		fab.bvconst(2)
		// 	),
		// 	fab.bvadd(
		// 		fab.bitvec("x", 32),
		// 		fab.bitvec("x", 32)
		// 	)
		// ).unwrap();

		// pretty_print_expr(&mut ::std::io::stdout(), &expr1);

		// let expr2 = expr_tree!(fab, expr!{
		// 	(=
		// 		(bvmul
		// 			(bitvec "x")
		// 		    (bvconst 2)
		// 	    )
		// 		(bvadd
		// 			(bitvec "x")
		// 			(bitvec "x")
		// 		)
		// 	)
		// });

		// assert_eq!(expr1, expr2);
	// }
// }
