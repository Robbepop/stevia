use ast::prelude::*;
use ast::AstError;
use ast::ErrorKind::*;

/// Acts as documentation and thin abstraction over bits 
/// that are given as argument to functions like `bvconst`
/// to construct bitvec and array types out of it.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Bits(pub usize);

impl From<Bits> for Type {
	fn from(bits: Bits) -> Type {
		let Bits(bits) = bits;
		Type::BitVec(bits)
	}
}

impl From<(Bits, Bits)> for Type {
	fn from(bits_pair: (Bits, Bits)) -> Type {
		let (Bits(idx_bits), Bits(val_bits)) = bits_pair;
		Type::Array(idx_bits, val_bits)
	}
}

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

	pub fn expect<E>(self, expected: E) -> Result<Type>
		where E: Typed
	{
		use self::TypeKind::*;
		use ast::ErrorKind::*;
		if self == expected.ty() {
			Ok(self)
		}
		else {
			match expected.ty().kind() {
				Boolean => Err(AstError(ExpectedBooleanType{found_type: self})),
				BitVec  => Err(AstError(ExpectedBitVecType{found_type: self})),
				Array   => Err(AstError(ExpectedArrayType{found_type: self}))
			}
		}
	}

	/// Returns the bitwidth of the given type encapsulated within the `Bits` wrapper.
	/// Returns an appropriate error, otherwise.
	pub fn bits(self) -> Result<Bits> {
		self.bitwidth().map(Bits)
	}

	/// Returns the bitwidths of the given type if it is a bitvector type.
	/// Returns an appropriate error, otherwise.
	pub fn bitwidth(self) -> Result<usize> {
		use self::Type::*;
		match self {
			BitVec(bits) => Ok(bits),
			wrong_ty     => {
				Err(AstError(ExpectedBitVecType{found_type: wrong_ty}))
			}
		}
	}

	/// Returns the common bitwidth of both given types if they are bitvec types.
	/// Returns an appropriate error, otherwise.
	pub fn common_bitwidth<E1, E2>(fst: E1, snd: E2) -> Result<usize>
		where E1: Typed,
		      E2: Typed
	{
		use self::Type::*;
		use ast::ErrorKind::*;
		match (fst.ty(), snd.ty()) {
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
	pub fn common_of<E1, E2>(fst: E1, snd: E2) -> Result<Type>
		where E1: Typed,
		      E2: Typed
	{
		use self::Type::*;
		use ast::ErrorKind::*;
		match (fst.ty(), snd.ty()) {
			(Boolean, Boolean) => Ok(Boolean),
			(BitVec(n), BitVec(m)) if n == m => Ok(BitVec(n)),
			(BitVec(n), BitVec(m)) if n != m => Err(AstError(IncompatibleBitWidth(n, m))),
			(Array(i1,v1), Array(i2,v2)) if i1 == i2 && v1 == v2 => Ok(Array(i1,v1)),
			(Array(i1,v1), Array(i2,v2)) if i1 != i2 && v1 == v2 => Err(AstError(IncompatibleIndexBitWidth(i1, i2))),
			(Array(i1,v1), Array(i2,v2)) if i1 == i2 && v1 != v2 => Err(AstError(IncompatibleValueBitWidth(v1, v2))),
			(Array(i1,v1), Array(i2,v2)) if i1 != i2 && v1 != v2 => Err(AstError(IncompatibleArrayTypes((i1,v1),(i2,v2)))),
			(fst, snd) => Err(AstError(TypeKindError{given: snd.kind(), expected: fst.kind()}))
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
		use ast::ErrorKind::*;
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

pub trait Typed {
	fn ty(&self) -> Type;
}

impl Typed for Type {
	fn ty(&self) -> Type {
		*self
	}
}

impl<E> Typed for E where E: ExprTrait {
	fn ty(&self) -> Type {
		<Self as ExprTrait>::ty(self)
	}
}

pub trait CommonBitwidth<T> {
	fn common_bitwidth(self) -> Result<usize>;
}

pub trait CommonBitVec<T> {
	fn common_bitvec(self) -> Result<Type>;
}

impl<T, E> CommonBitwidth<T> for T
	where T: Iterator<Item=E>,
	      E: Typed
{
	fn common_bitwidth(mut self) -> Result<usize> {
		if let Some(first) = self.next() {
			let mut current   = first.ty();
			let     common_bw = first.ty().bitwidth()?;
			for ty in self {
				Type::common_bitwidth(current, ty.ty())?;
				current = ty.ty();
			}
			Ok(common_bw)
		}
		else {
			// Cannot know the target bitwidth so this should fail!
			Err(AstError(TooFewChildren{given: 0, expected_min: 1}))
		}
	}
}

impl<T> CommonBitVec<T> for T where T: CommonBitwidth<T> {
	fn common_bitvec(self) -> Result<Type> {
		Ok(Type::BitVec(self.common_bitwidth()?))
	}
}
