use ast::expr;
use ast::{Bits, Type};
use ast::traits::ExprTrait;
use ast::iterators::{Childs, ChildsMut, IntoChilds};

macro_rules! forall_expr_kinds {
	( $mac:ident ) => {
		$mac!{

			// TERM EXPRESSIONS

			BitVecConst,
			Neg,
			Add,
			Mul,
			Sub,
			Div,
			Mod,
			SignedDiv,
			SignedMod,
			SignedRem,

			BitNot,
			BitAnd,
			BitOr,
			BitXor,
			BitNand,
			BitNor,
			BitXnor,

			Lt,
			Le,
			Gt,
			Ge,
			SignedLt,
			SignedLe,
			SignedGt,
			SignedGe,

			Shl,
			Shr,
			SignedShr,

			Concat,
			Extract,
			Extend,
			SignedExtend,

			Read,
			Write,

			// FORMULA EXPRESSIONS

			BoolConst,

			Not,

			And,
			Or,
			Xor,
			Iff,
			Implies,

			ParamBool,

			// GENERIC EXPRESSIONS

			Equals,
			IfThenElse,
			Symbol
		}
	}
}

//=============================================================================
// Implementation of base methods for all expression kinds.
//=============================================================================

macro_rules! impl_expr_kinds {
	( $($names:ident),* ) => {
		#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
		pub enum ExprKind {
			$($names),*
		}

		#[derive(Debug, Clone, PartialEq, Eq, Hash)]
		pub enum Expr {
			$($names(expr::$names)),*
		}

		impl Expr {
			pub fn as_trait(&self) -> &ExprTrait {
				use self::Expr::*;
				match *self {
					$($names(ref expr) => expr),*
				}
			}

			pub fn as_trait_mut(&mut self) -> &mut ExprTrait {
				use self::Expr::*;
				match *self {
					$($names(ref mut expr) => expr),*
				}
			}
		}
	}
}

forall_expr_kinds!(impl_expr_kinds);

//=============================================================================
// Prototype implementation of ordering of expression kinds.
//=============================================================================

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Priority(u32);

impl ExprKind {
	/// Returns a value that indicates the priority of this expression kind compared to
	/// other expression kinds.
	/// This is mainly used to sort expressions in n-ary expression node for some optimizations.
	fn priority(self) -> Priority {
		use self::ExprKind::*;
		match self {

			// ARITHMETIC EXPRESSIONS

			BitVecConst => Priority(10),
			Neg         => Priority(11),
			Add         => Priority(12),
			Mul         => Priority(13),
			Sub         => Priority(14),
			Div         => Priority(15),
			Mod         => Priority(16),
			SignedDiv   => Priority(17),
			SignedMod   => Priority(18),
			SignedRem   => Priority(19),

			// BITWISE EXPRESSIONS

			BitNot  => Priority(100),
			BitAnd  => Priority(101),
			BitOr   => Priority(102),
			BitXor  => Priority(103),
			BitNand => Priority(104),
			BitNor  => Priority(105),
			BitXnor => Priority(106),

			// COMPARISON EXPRESSIONS

			Lt       => Priority(200),
			Le       => Priority(201),
			Gt       => Priority(202),
			Ge       => Priority(203),
			SignedLt => Priority(204),
			SignedLe => Priority(205),
			SignedGt => Priority(206),
			SignedGe => Priority(207),

			// SHIFT EXPRESSIONS

			Shl       => Priority(300),
			Shr       => Priority(301),
			SignedShr => Priority(302),

			// EXTEND & TRUNCATE EXPRESSIONS

			Concat       => Priority(400),
			Extract      => Priority(401),
			Extend       => Priority(402),
			SignedExtend => Priority(403),

			// ARRAY EXPRESSIONS

			Read  => Priority(500),
			Write => Priority(501),

			// FORMULA EXPRESSIONS

			BoolConst => Priority(600),
			Not       => Priority(601),
			And       => Priority(602),
			Or        => Priority(603),
			Xor       => Priority(604),
			Iff       => Priority(605),
			Implies   => Priority(606),
			ParamBool => Priority(607),

			// GENERIC EXPRESSIONS

			Equals     => Priority(700),
			IfThenElse => Priority(701),
			Symbol     => Priority(702)
		}
	}
}

use ::std::cmp::Ordering;

impl PartialOrd for Expr {
	fn partial_cmp(&self, other: &Expr) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl Ord for Expr {
	fn cmp(&self, other: &Expr) -> Ordering {
		self.kind().priority().cmp(&other.kind().priority())
	}
}

//=============================================================================
// Implementation of expression trait methods for all expression kinds.
//=============================================================================

macro_rules! impl_into_childs {
    ( $($names:ident),* ) => {
		fn into_childs(self) -> IntoChilds {
			use self::Expr::*;
			match self {
				$( $names(expr) => expr.into_childs() ),*
			}
		}
    }
}

impl ExprTrait for Expr {
	#[inline]
	fn childs(&self) -> Childs {
		self.as_trait().childs()
	}

	#[inline]
	fn childs_mut(&mut self) -> ChildsMut {
		self.as_trait_mut().childs_mut()
	}

	forall_expr_kinds!(impl_into_childs);

	#[inline]
	fn kind(&self) -> ExprKind {
		self.as_trait().kind()
	}

	#[inline]
	fn ty(&self) -> Type {
		self.as_trait().ty()
	}

	#[inline]
	fn into_variant(self) -> Expr {
		self
	}
}

impl Expr {
	pub fn boolconst(flag: bool) -> Expr {
		Expr::BoolConst(expr::BoolConst{value: flag})
	}

	pub fn bvconst<T: Into<::BitVec>>(bits: Bits, value: T) -> Expr {
		Expr::BitVecConst(expr::BitVecConst{
			value: value.into(),
			ty   : bits.into()
		})
	}

	pub fn is_bvconst_with_value<T>(&self, expected: T) -> bool
		where T: Into<::BitVec>
	{
		if let Expr::BitVecConst(ref bvconst) = *self {
			bvconst.value == expected.into()
		}
		else {
			false
		}
	}
}
