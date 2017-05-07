
use ast::Type;
use ast::formulas::*;
use ast::terms::*;
use ast::kinds::ExprKind;
use ast::traits::ExprTrait;
use ast::iterators::{Childs, ChildsMut, IntoChilds};
use ast::{Equals, IfThenElse, Symbol};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprVariant {

	// TERM EXPRESSIONS

	BitVecConst(BitVecConst),

	Neg(Neg),

	Add(Add),
	Mul(Mul),

	Sub(Sub),

	Div(Div),
	Mod(Mod),
	SignedDiv(SignedDiv),
	SignedMod(SignedMod),
	SignedRem(SignedRem),

	BitNot(BitNot),
	BitAnd(BitAnd),
	BitOr(BitOr),
	BitXor(BitXor),
	BitNand(BitNand),
	BitNor(BitNor),
	BitXnor(BitXnor),

	Lt(Lt),
	Le(Le),
	Gt(Gt),
	Ge(Ge),
	SignedLt(SignedLt),
	SignedLe(SignedLe),
	SignedGt(SignedGt),
	SignedGe(SignedGe),

	Shl(Shl),
	Shr(Shr),
	SignedShr(SignedShr),

	Concat(Concat),
	Extract(Extract),
	Extend(Extend),
	SignedExtend(SignedExtend),

	Read(Read),
	Write(Write),

	// FORMULA EXPRESSIONS

	BoolConst(BoolConst),

	Not(Not),

	And(And),
	Or(Or),
	Xor(Xor),
	Iff(Iff),
	Implies(Implies),

	ParamBool(ParamBool),

	// GENERIC EXPRESSIONS

	Equals(Equals),
	IfThenElse(IfThenElse),
	Symbol(Symbol),

}

impl ExprVariant {
	pub fn as_trait(&self) -> &ExprTrait {
		use self::ExprVariant::*;
		match *self {

			// TERM EXPRESSIONS

			BitVecConst(ref expr) => expr,

			Neg(ref expr) => expr,

			Add(ref expr) => expr,
			Mul(ref expr) => expr,

			Sub(ref expr) => expr,

			Div(ref expr) => expr,
			Mod(ref expr) => expr,
			SignedDiv(ref expr) => expr,
			SignedMod(ref expr) => expr,
			SignedRem(ref expr) => expr,

			BitNot(ref expr) => expr,
			BitAnd(ref expr) => expr,
			BitOr(ref expr) => expr,
			BitXor(ref expr) => expr,
			BitNand(ref expr) => expr,
			BitNor(ref expr) => expr,
			BitXnor(ref expr) => expr,

			Lt(ref expr) => expr,
			Le(ref expr) => expr,
			Gt(ref expr) => expr,
			Ge(ref expr) => expr,
			SignedLt(ref expr) => expr,
			SignedLe(ref expr) => expr,
			SignedGt(ref expr) => expr,
			SignedGe(ref expr) => expr,

			Shl(ref expr) => expr,
			Shr(ref expr) => expr,
			SignedShr(ref expr) => expr,

			Concat(ref expr) => expr,
			Extract(ref expr) => expr,
			Extend(ref expr) => expr,
			SignedExtend(ref expr) => expr,

			Read(ref expr) => expr,
			Write(ref expr) => expr,

			// FORMULA EXPRESSIONS

			BoolConst(ref expr) => expr,

			Not(ref expr) => expr,

			And(ref expr) => expr,
			Or(ref expr) => expr,
			Xor(ref expr) => expr,
			Iff(ref expr) => expr,
			Implies(ref expr) => expr,

			ParamBool(ref expr) => expr,

			// GENERIC EXPRESSIONS

			Equals(ref expr) => expr,
			IfThenElse(ref expr) => expr,
			Symbol(ref expr) => expr,
		}
	}

	pub fn as_trait_mut(&mut self) -> &mut ExprTrait {
		use self::ExprVariant::*;
		match *self {

			// TERM EXPRESSIONS

			BitVecConst(ref mut expr) => expr,

			Neg(ref mut expr) => expr,

			Add(ref mut expr) => expr,
			Mul(ref mut expr) => expr,

			Sub(ref mut expr) => expr,

			Div(ref mut expr) => expr,
			Mod(ref mut expr) => expr,
			SignedDiv(ref mut expr) => expr,
			SignedMod(ref mut expr) => expr,
			SignedRem(ref mut expr) => expr,

			BitNot(ref mut expr) => expr,
			BitAnd(ref mut expr) => expr,
			BitOr(ref mut expr) => expr,
			BitXor(ref mut expr) => expr,
			BitNand(ref mut expr) => expr,
			BitNor(ref mut expr) => expr,
			BitXnor(ref mut expr) => expr,

			Lt(ref mut expr) => expr,
			Le(ref mut expr) => expr,
			Gt(ref mut expr) => expr,
			Ge(ref mut expr) => expr,
			SignedLt(ref mut expr) => expr,
			SignedLe(ref mut expr) => expr,
			SignedGt(ref mut expr) => expr,
			SignedGe(ref mut expr) => expr,

			Shl(ref mut expr) => expr,
			Shr(ref mut expr) => expr,
			SignedShr(ref mut expr) => expr,

			Concat(ref mut expr) => expr,
			Extract(ref mut expr) => expr,
			Extend(ref mut expr) => expr,
			SignedExtend(ref mut expr) => expr,

			Read(ref mut expr) => expr,
			Write(ref mut expr) => expr,

			// FORMULA EXPRESSIONS

			BoolConst(ref mut expr) => expr,

			Not(ref mut expr) => expr,

			And(ref mut expr) => expr,
			Or(ref mut expr) => expr,
			Xor(ref mut expr) => expr,
			Iff(ref mut expr) => expr,
			Implies(ref mut expr) => expr,

			ParamBool(ref mut expr) => expr,

			// GENERIC EXPRESSIONS

			Equals(ref mut expr) => expr,
			IfThenElse(ref mut expr) => expr,
			Symbol(ref mut expr) => expr,
		}
	}
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
