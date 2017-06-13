use std::ops::Range;

use ast::expr;
use ast::{SymName, P, Bits, Type};
use ast::traits::{
	ChildsIter,
	Kinded,
	Typed,
	IntoExpr,
	GenericExpr
};
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
			pub fn as_generic(&self) -> &GenericExpr {
				use self::Expr::*;
				match *self {
					$($names(ref expr) => expr),*
				}
			}

			pub fn as_generic_mut(&mut self) -> &mut GenericExpr {
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
		use self::Expr::*;
		match (self, other) {
			// sort symbols by their name identifier
			(&Symbol(ref left), &Symbol(ref right))
				=> left.name.cmp(&right.name),

			// sort bool constants by bool comparison
			(&BoolConst(ref left), &BoolConst(ref right))
				=> left.value.cmp(&right.value),

			// sort bitvec constants by comparing their value
			(&BitVecConst(ref left), &BitVecConst(ref right))
				=> left.value.cmp(&right.value),

			// sort not by forwarding to inner
			(&Not(ref left), &Not(ref right))
				=> left.inner.cmp(&right.inner),

			// sort neg by forwarding to inner
			(&Neg(ref left), &Neg(ref right))
				=> left.inner.cmp(&right.inner),

			// sort bitnot by forwarding to inner
			(&BitNot(ref left), &BitNot(ref right))
				=> left.inner.cmp(&right.inner),

			// sort expressions of the same kind generically
			(left, right) if left.kind() == right.kind() => {
				use std::cmp::Ordering;
				match left.arity().cmp(&right.arity()) {
					Ordering::Less    => Ordering::Less,
					Ordering::Greater => Ordering::Greater,
					Ordering::Equal   => {
						for (lchild, rchild) in left.childs().zip(right.childs()) {
							match lchild.cmp(rchild) {
								Ordering::Less    => return Ordering::Less,
								Ordering::Greater => return Ordering::Greater,
								Ordering::Equal   => continue
							}
						}
						Ordering::Equal
					}
				}
			}

			// different expression kinds are sorted by their kind based priority
			_ => self.kind().priority().cmp(&other.kind().priority())
		}
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

impl ChildsIter for Expr {
	#[inline]
	fn childs(&self) -> Childs {
		self.as_generic().childs()
	}

	#[inline]
	fn childs_mut(&mut self) -> ChildsMut {
		self.as_generic_mut().childs_mut()
	}

	forall_expr_kinds!(impl_into_childs);
}

impl Kinded for Expr {
	#[inline]
	fn kind(&self) -> ExprKind {
		self.as_generic().kind()
	}
}

impl Typed for Expr {
	#[inline]
	fn ty(&self) -> Type {
		self.as_generic().ty()
	}
}

impl IntoExpr for Expr {
	#[inline]
	fn into_expr(self) -> Expr {
		self
	}
}

impl GenericExpr for Expr {
	#[inline]
	fn arity(&self) -> usize {
		self.as_generic().arity()
	}
}

impl Expr {
	/// Returns true if self is a constant boolean expression 
	/// with the given `expected` boolean representation.
	/// 
	/// Note: This is a convenience method.
	pub fn is_boolconst_with_value(&self, expected: bool) -> bool {
		if let Expr::BoolConst(ref val) = *self {
			val.value == expected
		}
		else {
			false
		}
	}

	/// Returns true if self is a constant bitvector expression
	/// with the given `expected` bitvector representation.
	/// 
	/// Note: This is a convenience method.
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

	/// Returns true if the given `other` boolean expression contradicts
	/// self as boolean expression symbolically.
	/// 
	/// I.e. for `a` and `(not a)`
	pub fn is_bool_contradiction(&self, other: &Expr) -> bool {
		if self.ty() != Type::Boolean || other.ty() != Type::Boolean { return false }
		match (self, other) {
			(a, &Expr::Not(ref not_a)) if &*not_a.inner == a => true,
			(&Expr::Not(ref not_a), a) if &*not_a.inner == a => true,
			_ => false
		}
	}

	/// Returns true if the given `other` boolean expression contradicts
	/// self as boolean expression symbolically.
	/// 
	/// I.e. for `a` and `(not a)`
	pub fn is_bitvec_contradiction(&self, other: &Expr) -> bool {
		if Type::common_bitwidth(self.ty(), other.ty()).is_err() { return false }
		match (self, other) {
			(a, &Expr::Neg(ref neg_a)) if &*neg_a.inner == a => true,
			(&Expr::Neg(ref neg_a), a) if &*neg_a.inner == a => true,
			_ => false
		}
	}

	// Wraps the given `Expr` within a `Neg` expression.
	// 
	// Does some minor simplification to avoid involution allocations.
	pub fn wrap_with_neg(self) -> Expr {
		match self {
			Expr::Neg(neg) => *neg.inner,
			_ => Expr::bvneg(Box::new(self))
		}
	}

	// Unwraps the given `Neg` expression.
	// 
	// Does nothing if the given expression is not a `Neg` expression.
	pub fn unwrap_neg(self) -> Expr {
		match self {
			Expr::Neg(neg) => *neg.inner,
			f => f
		}
	}

	// Wraps the given `Expr` within a `Not` expression.
	// 
	// Does some minor simplification to avoid involution allocations.
	pub fn wrap_with_not(self) -> Expr {
		match self {
			Expr::Not(not) => *not.inner,
			_ => Expr::not(Box::new(self))
		}
	}

	// Unwraps the given `Not` expression.
	// 
	// Does nothing if the given expression is not a `Not` expression.
	pub fn unwrap_not(self) -> Expr {
		match self {
			Expr::Not(not) => *not.inner,
			f => f
		}
	}

	// Generic convenience function applying the given by-value receiver
	// to the given expression, operating inplace and self-assign the result.
	// 
	// This allows usage of all consuming functions by references to mutables.
	pub fn assign_fn<F>(&mut self, f: F)
		where F: FnOnce(Expr) -> Expr
	{
		use std::mem;
		let extracted = mem::replace(self, Expr::boolconst(false));
		let morphed   = f(extracted);
		mem::replace(self, morphed);
	}
}

impl Expr {
	//=========================================================================
	// TERM EXPRESSIONS
	//=========================================================================

	// ARITHMETHIC EXPRESSIONS
	//-------------------------------------------------------------------------

	pub fn bvconst<T: Into<::BitVec>>(bits: Bits, value: T) -> Expr {
		Expr::BitVecConst(expr::BitVecConst{
			value: value.into(),
			ty   : bits.into()
		})
	}

	pub fn bvneg(inner: P<Expr>) -> Expr {
		Expr::Neg(expr::Neg{ty: inner.ty(), inner})
	}

	pub fn bvsum(ty: Type, terms: Vec<Expr>) -> Expr {
		Expr::Add(expr::Add{ty, terms})
	}

	pub fn bvprod(ty: Type, factors: Vec<Expr>) -> Expr {
		Expr::Mul(expr::Mul{ty, factors})
	}

	pub fn bvsub(ty: Type, minuend: P<Expr>, subtrahend: P<Expr>) -> Expr {
		Expr::Sub(expr::Sub{ty, minuend, subtrahend})
	}

	pub fn bvudiv(ty: Type, dividend: P<Expr>, divisor: P<Expr>) -> Expr {
		Expr::Div(expr::Div{ty, dividend, divisor})
	}

	pub fn bvumod(ty: Type, dividend: P<Expr>, divisor: P<Expr>) -> Expr {
		Expr::Mod(expr::Mod{ty, dividend, divisor})
	}

	pub fn bvsdiv(ty: Type, dividend: P<Expr>, divisor: P<Expr>) -> Expr {
		Expr::SignedDiv(expr::SignedDiv{ty, dividend, divisor})
	}

	pub fn bvsmod(ty: Type, dividend: P<Expr>, divisor: P<Expr>) -> Expr {
		Expr::SignedMod(expr::SignedMod{ty, dividend, divisor})
	}

	pub fn bvsrem(ty: Type, dividend: P<Expr>, divisor: P<Expr>) -> Expr {
		Expr::SignedRem(expr::SignedRem{ty, dividend, divisor})
	}

	// BITWISE EXPRESSIONS
	//-------------------------------------------------------------------------

	pub fn bvnot(ty: Type, inner: P<Expr>) -> Expr {
		Expr::BitNot(expr::BitNot{ty, inner})
	}

	pub fn bvand(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr {
		Expr::BitAnd(expr::BitAnd{ty, left, right})
	}

	pub fn bvor(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr {
		Expr::BitOr(expr::BitOr{ty, left, right})
	}

	pub fn bvxor(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr {
		Expr::BitXor(expr::BitXor{ty, left, right})
	}

	pub fn bvnand(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr {
		Expr::BitNand(expr::BitNand{ty, left, right})
	}

	pub fn bvnor(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr {
		Expr::BitNor(expr::BitNor{ty, left, right})
	}

	pub fn bvxnor(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr {
		Expr::BitXnor(expr::BitXnor{ty, left, right})
	}

	// ORDER COMPARE EXPRESSIONS
	//-------------------------------------------------------------------------

	pub fn bvult(inner_ty: Type, left: P<Expr>, right: P<Expr>) -> Expr {
		Expr::Lt(expr::Lt{inner_ty, left, right})
	}

	pub fn bvule(inner_ty: Type, left: P<Expr>, right: P<Expr>) -> Expr {
		Expr::Le(expr::Le{inner_ty, left, right})
	}

	pub fn bvugt(inner_ty: Type, left: P<Expr>, right: P<Expr>) -> Expr {
		Expr::Gt(expr::Gt{inner_ty, left, right})
	}

	pub fn bvuge(inner_ty: Type, left: P<Expr>, right: P<Expr>) -> Expr {
		Expr::Ge(expr::Ge{inner_ty, left, right})
	}

	pub fn bvslt(inner_ty: Type, left: P<Expr>, right: P<Expr>) -> Expr {
		Expr::SignedLt(expr::SignedLt{inner_ty, left, right})
	}

	pub fn bvsle(inner_ty: Type, left: P<Expr>, right: P<Expr>) -> Expr {
		Expr::SignedLe(expr::SignedLe{inner_ty, left, right})
	}

	pub fn bvsgt(inner_ty: Type, left: P<Expr>, right: P<Expr>) -> Expr {
		Expr::SignedGt(expr::SignedGt{inner_ty, left, right})
	}

	pub fn bvsge(inner_ty: Type, left: P<Expr>, right: P<Expr>) -> Expr {
		Expr::SignedGe(expr::SignedGe{inner_ty, left, right})
	}

	// SHIFT EXPRESSIONS
	//-------------------------------------------------------------------------

	pub fn bvushl(ty: Type, shifted: P<Expr>, shift_amount: P<Expr>) -> Expr {
		Expr::Shl(expr::Shl{ty, shifted, shift_amount})
	}

	pub fn bvushr(ty: Type, shifted: P<Expr>, shift_amount: P<Expr>) -> Expr {
		Expr::Shr(expr::Shr{ty, shifted, shift_amount})
	}

	pub fn bvsshr(ty: Type, shifted: P<Expr>, shift_amount: P<Expr>) -> Expr {
		Expr::SignedShr(expr::SignedShr{ty, shifted, shift_amount})
	}

	// EXTEND & TRUNCATE EXPRESSIONS
	//-------------------------------------------------------------------------

	pub fn concat(hi: P<Expr>, lo: P<Expr>) -> Expr {
		let hi_bits = Type::bitwidth(hi.ty()).unwrap();
		let lo_bits = Type::bitwidth(hi.ty()).unwrap();
		Expr::Concat(expr::Concat{
			ty: Type::BitVec(hi_bits + lo_bits), hi, lo})
	}

	pub fn extract(source: P<Expr>, range: Range<usize>) -> Expr {
		Expr::Extract(expr::Extract{
			ty: Type::BitVec(range.end - range.start), source, range})
	}

	pub fn uextend(source: P<Expr>, extension: usize) -> Expr {
		Expr::Extend(expr::Extend{
			ty: Type::BitVec(extension), source, extension})
	}

	pub fn sextend(source: P<Expr>, extension: usize) -> Expr {
		Expr::SignedExtend(expr::SignedExtend{
			ty: Type::BitVec(extension), source, extension})
	}

	// ARRAY EXPRESSIONS
	//-------------------------------------------------------------------------

	pub fn read(ty: Type, array: P<Expr>, index: P<Expr>) -> Expr {
		Expr::Read(expr::Read{ty, array, index})
	}

	pub fn write(ty: Type, array: P<Expr>, index: P<Expr>, new_val: P<Expr>) -> Expr {
		Expr::Write(expr::Write{ty, array, index, new_val})
	}

	//=========================================================================
	// FORMULA EXPRESSIONS
	//=========================================================================
	pub fn boolconst(flag: bool) -> Expr {
		Expr::BoolConst(expr::BoolConst{value: flag})
	}

	pub fn not(inner: P<Expr>) -> Expr {
		Expr::Not(expr::Not{inner})
	}

	pub fn conjunction(formulas: Vec<Expr>) -> Expr {
		Expr::And(expr::And{formulas})
	}

	pub fn disjunction(formulas: Vec<Expr>) -> Expr {
		Expr::Or(expr::Or{formulas})
	}

	pub fn xor(left: P<Expr>, right: P<Expr>) -> Expr {
		Expr::Xor(expr::Xor{left, right})
	}

	pub fn iff(left: P<Expr>, right: P<Expr>) -> Expr {
		Expr::Iff(expr::Iff{left, right})
	}

	pub fn implies(assumption: P<Expr>, implication: P<Expr>) -> Expr {
		Expr::Implies(expr::Implies{assumption, implication})
	}

	pub fn parambool(bool_var: P<Expr>, param: P<Expr>) -> Expr {
		Expr::ParamBool(expr::ParamBool{bool_var, param})
	}

	//=========================================================================
	// GENERIC EXPRESSIONS
	//=========================================================================

	pub fn equality(inner_ty: Type, exprs: Vec<Expr>) -> Expr {
		Expr::Equals(expr::Equals{inner_ty, exprs})
	}

	pub fn ite(ty: Type, cond: P<Expr>, then_case: P<Expr>, else_case: P<Expr>) -> Expr {
		Expr::IfThenElse(expr::IfThenElse{ty, cond, then_case, else_case})
	}

	pub fn symbol(name: SymName, ty: Type) -> Expr {
		Expr::Symbol(expr::Symbol{ty, name})
	}

	pub fn boolean(name: SymName) -> Expr {
		Expr::Symbol(expr::Symbol{ty: Type::Boolean, name})
	}

	pub fn bitvec(name: SymName, bitwidth: Bits) -> Expr {
		Expr::Symbol(expr::Symbol{ty: Type::BitVec(bitwidth.0), name})
	}

	pub fn array(name: SymName, idx_width: Bits, val_width: Bits) -> Expr {
		Expr::Symbol(expr::Symbol{ty: Type::Array(idx_width.0, val_width.0), name})
	}
}
