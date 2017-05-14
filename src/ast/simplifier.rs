use ast::prelude::*;
use ast::expr::*;

use ast::{Transformer, TransformerImpl};

/// Simplifies the given expression.
/// 
/// The given expression is being consumed by this function.
/// This makes it possible to reuse some internals for better efficiency.
/// 
/// Note to self: Do not call this from inside the `Simplifier` since this would 
/// lead to distinct evaluation contexts and thus worsen optimizations.
pub fn simplify(expr: Expr) -> Expr {
	Simplifier::new().transform(expr)
}

struct Simplifier {
	// TODO: Add evaluation context for evaluated expressions.
	//       This may require expressions to implement `Hash`.
}

impl Simplifier {
	fn new() -> Simplifier {
		Simplifier{}
	}
}

// impl Expr {
// 	/// Unpacks an expression given by mutable reference with a dummy expression.
// 	/// 
// 	/// This is used as a semi-hack to avoid dynamic heap allocations when working
// 	/// with boxed expressions during the simplification procedure.
// 	fn unpack(&mut self) -> Expr {
// 		::std::mem::replace(self, Expr::BoolConst(BoolConst{value: false}))
// 	}
// }

impl TransformerImpl for Simplifier {
	fn transform_bvconst(&mut self, expr: BitVecConst) -> Expr {
		expr.into_variant()
	}

	//=========================================================================
	// BITVEC ARITHMETIC
	//=========================================================================

	fn transform_bvneg(&mut self, expr: Neg) -> Expr {
		match *expr.inner {
			Expr::Neg(negneg) => self.transform(*negneg.inner),
			_ => expr.into_variant()
		}
	}

	fn transform_bvadd(&mut self, expr: Add) -> Expr {
		expr.into_variant()
	}

	fn transform_bvmul(&mut self, expr: Mul) -> Expr {
		expr.into_variant()
	}

	fn transform_bvsub(&mut self, expr: Sub) -> Expr {
		expr.into_variant()
	}

	fn transform_bvudiv(&mut self, expr: Div) -> Expr {
		expr.into_variant()
	}

	fn transform_bvumod(&mut self, expr: Mod) -> Expr {
		expr.into_variant()
	}

	fn transform_bvsdiv(&mut self, expr: SignedDiv) -> Expr {
		expr.into_variant()
	}

	fn transform_bvsmod(&mut self, expr: SignedMod) -> Expr {
		expr.into_variant()
	}

	fn transform_bvsrem(&mut self, expr: SignedRem) -> Expr {
		expr.into_variant()
	}

	//=========================================================================
	// BITVEC BITWISE OPERATIONS
	//=========================================================================

	fn transform_bvnot(&mut self, expr: BitNot) -> Expr {
		expr.into_variant()
	}

	fn transform_bvand(&mut self, expr: BitAnd) -> Expr {
		expr.into_variant()
	}

	fn transform_bvor(&mut self, expr: BitOr) -> Expr {
		expr.into_variant()
	}

	fn transform_bvxor(&mut self, expr: BitXor) -> Expr {
		expr.into_variant()
	}

	fn transform_bvnand(&mut self, expr: BitNand) -> Expr {
		expr.into_variant()
	}

	fn transform_bvnor(&mut self, expr: BitNor) -> Expr {
		expr.into_variant()
	}

	fn transform_bvxnor(&mut self, expr: BitXnor) -> Expr {
		expr.into_variant()
	}

	//=========================================================================
	// BITVEC COMPARISONS
	//=========================================================================

	fn transform_bvult(&mut self, expr: Lt) -> Expr {
		// TODO: `x < y where x < y and x,y consteval => true`
		// TODO: `x < y where not(x < y) and x,y consteval => false`
		expr.into_variant()
	}

	fn transform_bvule(&mut self, expr: Le) -> Expr {
		// TODO: Convert `left =< right` to `not(left > right)` to `not(right < left)`
		//       Lower to `not` and `lt` only.
		expr.into_variant()
	}

	fn transform_bvugt(&mut self, expr: Gt) -> Expr {
		self.transform_bvult(
			Lt{left: expr.right, right: expr.left, ty: expr.ty})
	}

	fn transform_bvuge(&mut self, expr: Ge) -> Expr {
		self.transform_bvule(
			Le{left: expr.right, right: expr.left, ty: expr.ty})
	}

	fn transform_bvslt(&mut self, expr: SignedLt) -> Expr {
		expr.into_variant()
	}

	fn transform_bvsle(&mut self, expr: SignedLe) -> Expr {
		expr.into_variant()
	}

	fn transform_bvsgt(&mut self, expr: SignedGt) -> Expr {
		self.transform_bvslt(
			SignedLt{left: expr.right, right: expr.left, ty: expr.ty})
	}

	fn transform_bvsge(&mut self, expr: SignedGe) -> Expr {
		self.transform_bvsle(
			SignedLe{left: expr.right, right: expr.left, ty: expr.ty})
	}

	//=========================================================================
	// BITVEC SHIFT
	//=========================================================================

	fn transform_bvushl(&mut self, expr: Shl) -> Expr {
		expr.into_variant()
	}

	fn transform_bvushr(&mut self, expr: Shr) -> Expr {
		expr.into_variant()
	}

	fn transform_bvsshr(&mut self, expr: SignedShr) -> Expr {
		expr.into_variant()
	}

	//=========================================================================
	// BITVEC EXTEND & EXTRACT
	//=========================================================================

	fn transform_concat(&mut self, expr: Concat) -> Expr {
		expr.into_variant()
	}

	fn transform_extract(&mut self, expr: Extract) -> Expr {
		expr.into_variant()
	}

	fn transform_uextend(&mut self, expr: Extend) -> Expr {
		expr.into_variant()
	}

	fn transform_sextend(&mut self, expr: SignedExtend) -> Expr {
		expr.into_variant()
	}

	fn transform_read(&mut self, expr: Read) -> Expr {
		expr.into_variant()
	}

	fn transform_write(&mut self, expr: Write) -> Expr {
		expr.into_variant()
	}

	fn transform_boolconst(&mut self, expr: BoolConst) -> Expr {
		expr.into_variant()
	}

	fn transform_not(&mut self, expr: Not) -> Expr {
		match *expr.inner {
			Expr::Not(notnot) => self.transform(*notnot.inner),
			Expr::BoolConst(BoolConst{value: true}) => BoolConst{value: false}.into_variant(),
			Expr::BoolConst(BoolConst{value: false}) => BoolConst{value: true}.into_variant(),
			_ => expr.into_variant()
		}
	}

	fn transform_and(&mut self, expr: And) -> Expr {
		// TODO: flatten-nested ands
		// TODO: evalute to false if detecting const false expression
		// TODO: sort expression list (needed for some other optimizations that require normalization)
		expr.into_variant()
	}

	fn transform_or(&mut self, expr: Or) -> Expr {
		// TODO: see `transform_and`
		expr.into_variant()
	}

	fn transform_xor(&mut self, expr: Xor) -> Expr {
		expr.into_variant()
	}

	fn transform_iff(&mut self, expr: Iff) -> Expr {
		expr.into_variant()
	}

	fn transform_implies(&mut self, expr: Implies) -> Expr {
		expr.into_variant()
	}

	fn transform_param_bool(&mut self, expr: ParamBool) -> Expr {
		expr.into_variant()
	}

	fn transform_equals(&mut self, expr: Equals) -> Expr {
		// TODO: `a == a => true`
		// TODO: `a == not(a)` => false`
		// TODO: `not(a) == a` => false`
		expr.into_variant()
	}

	fn transform_ite(&mut self, expr: IfThenElse) -> Expr {
		match *expr.cond {
			Expr::BoolConst(BoolConst{value: true}) => {
				self.transform(*expr.then_case)
			},
			Expr::BoolConst(BoolConst{value: false}) => {
				self.transform(*expr.else_case)
			},
			_ => {
				expr.into_variant()
			}
		}
		// TODO: `if (cond) {foo} else {foo} => foo`

		// expr.cond = self.boxed_transform(expr.cond);
		// expr.then_case = self.boxed_transform(expr.then_case);
		// expr.else_case = self.boxed_transform(expr.else_case);
		// expr.into_variant()
	}

	fn transform_symbol(&mut self, expr: Symbol) -> Expr {
		expr.into_variant()
	}

}

#[cfg(test)]
mod tests {
	use super::*;
	use ast::NaiveExprFactory;

	#[test]
	fn simplify_negneg_even() {
		let f    = NaiveExprFactory::new();
		let expr = f.bvneg(
			f.bvneg(
				f.bvneg(
					f.bvneg(
						f.bvconst(Bits(32), 42)
					)
				)
			)
		).unwrap();
		let simplified = simplify(expr);
		let expected   = f.bvconst(Bits(32), 42).unwrap();
		assert_eq!(simplified, expected);
	}

	#[test]
	fn simplify_negneg_odd() {
		let f    = NaiveExprFactory::new();
		let expr = f.bvneg(
			f.bvneg(
				f.bvneg(
					f.bvneg(
						f.bvneg(
							f.bvconst(Bits(32), 42)
						)
					)
				)
			)
		).unwrap();
		let simplified = simplify(expr);
		let expected   = f.bvneg(f.bvconst(Bits(32), 42)).unwrap();
		assert_eq!(simplified, expected);
	}

	#[test]
	fn simplify_notnot_even() {
		let f    = NaiveExprFactory::new();
		let expr = f.not(
			f.not(
				f.not(
					f.not(
						f.boolconst(false)
					)
				)
			)
		).unwrap();
		let simplified = simplify(expr);
		let expected   = f.boolconst(false).unwrap();
		assert_eq!(simplified, expected);
	}

	#[test]
	fn simplify_notnot_odd() {
		let f    = NaiveExprFactory::new();
		let expr = f.not(
			f.not(
				f.not(
					f.not(
						f.not(
							f.boolconst(false)
						)
					)
				)
			)
		).unwrap();
		let simplified = simplify(expr);
		let expected   = f.boolconst(true).unwrap();
		assert_eq!(simplified, expected);
	}

	#[test]
	fn simplify_not_true() {
		let f = NaiveExprFactory::new();
		let e = f.not(f.boolconst(true)).unwrap();
		let simplified = simplify(e);
		let expected   = f.boolconst(false).unwrap();
		assert_eq!(simplified, expected);
	}

	#[test]
	fn simplify_not_false() {
		let f = NaiveExprFactory::new();
		let e = f.not(f.boolconst(false)).unwrap();
		let simplified = simplify(e);
		let expected   = f.boolconst(true).unwrap();
		assert_eq!(simplified, expected);
	}

	#[test]
	fn simplify_ite_const_true_cond() {
		let f  = NaiveExprFactory::new();
		let expr = f.ite(
			f.boolconst(true),
			f.bvconst(Bits(32), 42),
			f.bvconst(Bits(32), 1337)
		).unwrap();
		let simplified = simplify(expr);
		let expected   = f.bvconst(Bits(32), 42).unwrap();
		assert_eq!(simplified, expected);
	}

	#[test]
	fn simplify_ite_const_false_cond() {
		let f  = NaiveExprFactory::new();
		let expr = f.ite(
			f.boolconst(false),
			f.bvconst(Bits(32), 42),
			f.bvconst(Bits(32), 1337)
		).unwrap();
		let simplified = simplify(expr);
		let expected   = f.bvconst(Bits(32), 1337).unwrap();
		assert_eq!(simplified, expected);
	}
}
