
use ast::Type;
use ast::formulas::*;
use ast::terms::*;
use ast::traits::ExprTrait;
use ast::iterators::{Childs, ChildsMut, IntoChilds};
use ast::{Equals, IfThenElse, Symbol};

macro_rules! gen_kinds_and_variant {
	( $($names:ident),* ) => {
		#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
		pub enum ExprKind {
			$($names),*
		}

		#[derive(Debug, Clone, PartialEq, Eq, Hash)]
		pub enum ExprVariant {
			$($names($names)),*
		}

		impl ExprVariant {
			pub fn as_trait(&self) -> &ExprTrait {
				use self::ExprVariant::*;
				match *self {
					$($names(ref expr) => expr),*
				}
			}

			pub fn as_trait_mut(&mut self) -> &mut ExprTrait {
				use self::ExprVariant::*;
				match *self {
					$($names(ref mut expr) => expr),*
				}
			}
		}
	}
}

gen_kinds_and_variant! {
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

impl ExprTrait for ExprVariant {
	#[inline]
	fn childs(&self) -> Childs {
		self.as_trait().childs()
	}

	#[inline]
	fn childs_mut(&mut self) -> ChildsMut {
		self.as_trait_mut().childs_mut()
	}

	fn into_childs(self) -> IntoChilds {
		use self::ExprVariant::*;
		match self {

			// TERM EXPRESSIONS

			BitVecConst(expr) => expr.into_childs(),

			Neg(expr) => expr.into_childs(),

			Add(expr) => expr.into_childs(),
			Mul(expr) => expr.into_childs(),

			Sub(expr) => expr.into_childs(),

			Div(expr) => expr.into_childs(),
			Mod(expr) => expr.into_childs(),
			SignedDiv(expr) => expr.into_childs(),
			SignedMod(expr) => expr.into_childs(),
			SignedRem(expr) => expr.into_childs(),

			BitNot(expr) => expr.into_childs(),
			BitAnd(expr) => expr.into_childs(),
			BitOr(expr) => expr.into_childs(),
			BitXor(expr) => expr.into_childs(),
			BitNand(expr) => expr.into_childs(),
			BitNor(expr) => expr.into_childs(),
			BitXnor(expr) => expr.into_childs(),

			Lt(expr) => expr.into_childs(),
			Le(expr) => expr.into_childs(),
			Gt(expr) => expr.into_childs(),
			Ge(expr) => expr.into_childs(),
			SignedLt(expr) => expr.into_childs(),
			SignedLe(expr) => expr.into_childs(),
			SignedGt(expr) => expr.into_childs(),
			SignedGe(expr) => expr.into_childs(),

			Shl(expr) => expr.into_childs(),
			Shr(expr) => expr.into_childs(),
			SignedShr(expr) => expr.into_childs(),

			Concat(expr) => expr.into_childs(),
			Extract(expr) => expr.into_childs(),
			Extend(expr) => expr.into_childs(),
			SignedExtend(expr) => expr.into_childs(),

			Read(expr) => expr.into_childs(),
			Write(expr) => expr.into_childs(),

			// FORMULA EXPRESSIONS

			BoolConst(expr) => expr.into_childs(),

			Not(expr) => expr.into_childs(),

			And(expr) => expr.into_childs(),
			Or(expr) => expr.into_childs(),
			Xor(expr) => expr.into_childs(),
			Iff(expr) => expr.into_childs(),
			Implies(expr) => expr.into_childs(),

			ParamBool(expr) => expr.into_childs(),

			// GENERIC EXPRESSIONS

			Equals(expr) => expr.into_childs(),
			IfThenElse(expr) => expr.into_childs(),
			Symbol(expr) => expr.into_childs(),
		}
	}

	#[inline]
	fn kind(&self) -> ExprKind {
		self.as_trait().kind()
	}

	#[inline]
	fn ty(&self) -> Type {
		self.as_trait().ty()
	}

	#[inline(always)]
	fn into_variant(self) -> ExprVariant {
		self
	}
}
