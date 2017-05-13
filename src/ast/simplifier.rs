use ast::prelude::*;
use ast::expr::*;

#[macro_use]
use ast::transformer;

use ast::{Transformer, TransformerImpl};

pub fn simplify(expr: Expr) -> Expr {
	Simplifier::new().transform(expr)
}

struct Simplifier {
	// TODO
}

impl Simplifier {
	fn new() -> Simplifier {
		Simplifier{}
	}
}

impl Expr {
	/// Unpacks an expression given by mutable reference with a dummy expression.
	/// 
	/// This is used as a semi-hack to avoid dynamic heap allocations when working
	/// with boxed expressions during the simplification procedure.
	fn unpack(&mut self) -> Expr {
		::std::mem::replace(self, Expr::BoolConst(BoolConst{value: false}))
	}
}

impl TransformerImpl for Simplifier {
	fn transform_bvconst(&mut self, mut expr: BitVecConst) -> Expr {
		expr.into_variant()
	}

	fn transform_bvneg(&mut self, mut expr: Neg) -> Expr {
		match *expr.inner {
			Expr::Neg(negneg) => self.transform(*negneg.inner),
			_ => expr.into_variant()
		}
	}

	fn transform_bvadd(&mut self, mut expr: Add) -> Expr {
		expr.into_variant()
	}

	fn transform_bvmul(&mut self, mut expr: Mul) -> Expr {
		expr.into_variant()
	}

	fn transform_bvsub(&mut self, mut expr: Sub) -> Expr {
		expr.into_variant()
	}

	fn transform_bvudiv(&mut self, mut expr: Div) -> Expr {
		expr.into_variant()
	}

	fn transform_bvumod(&mut self, mut expr: Mod) -> Expr {
		expr.into_variant()
	}

	fn transform_bvsdiv(&mut self, mut expr: SignedDiv) -> Expr {
		expr.into_variant()
	}

	fn transform_bvsmod(&mut self, mut expr: SignedMod) -> Expr {
		expr.into_variant()
	}

	fn transform_bvsrem(&mut self, mut expr: SignedRem) -> Expr {
		expr.into_variant()
	}

	fn transform_bvnot(&mut self, mut expr: BitNot) -> Expr {
		expr.into_variant()
	}

	fn transform_bvand(&mut self, mut expr: BitAnd) -> Expr {
		expr.into_variant()
	}

	fn transform_bvor(&mut self, mut expr: BitOr) -> Expr {
		expr.into_variant()
	}

	fn transform_bvxor(&mut self, mut expr: BitXor) -> Expr {
		expr.into_variant()
	}

	fn transform_bvnand(&mut self, mut expr: BitNand) -> Expr {
		expr.into_variant()
	}

	fn transform_bvnor(&mut self, mut expr: BitNor) -> Expr {
		expr.into_variant()
	}

	fn transform_bvxnor(&mut self, mut expr: BitXnor) -> Expr {
		expr.into_variant()
	}

	fn transform_bvult(&mut self, mut expr: Lt) -> Expr {
		expr.into_variant()
	}

	fn transform_bvule(&mut self, mut expr: Le) -> Expr {
		expr.into_variant()
	}

	fn transform_bvugt(&mut self, mut expr: Gt) -> Expr {
		expr.into_variant()
	}

	fn transform_bvuge(&mut self, mut expr: Ge) -> Expr {
		expr.into_variant()
	}

	fn transform_bvslt(&mut self, mut expr: SignedLt) -> Expr {
		expr.into_variant()
	}

	fn transform_bvsle(&mut self, mut expr: SignedLe) -> Expr {
		expr.into_variant()
	}

	fn transform_bvsgt(&mut self, mut expr: SignedGt) -> Expr {
		expr.into_variant()
	}

	fn transform_bvsge(&mut self, mut expr: SignedGe) -> Expr {
		expr.into_variant()
	}

	fn transform_bvushl(&mut self, mut expr: Shl) -> Expr {
		expr.into_variant()
	}

	fn transform_bvushr(&mut self, mut expr: Shr) -> Expr {
		expr.into_variant()
	}

	fn transform_bvsshr(&mut self, mut expr: SignedShr) -> Expr {
		expr.into_variant()
	}

	fn transform_concat(&mut self, mut expr: Concat) -> Expr {
		expr.into_variant()
	}

	fn transform_extract(&mut self, mut expr: Extract) -> Expr {
		expr.into_variant()
	}

	fn transform_uextend(&mut self, mut expr: Extend) -> Expr {
		expr.into_variant()
	}

	fn transform_sextend(&mut self, mut expr: SignedExtend) -> Expr {
		expr.into_variant()
	}

	fn transform_read(&mut self, mut expr: Read) -> Expr {
		expr.into_variant()
	}

	fn transform_write(&mut self, mut expr: Write) -> Expr {
		expr.into_variant()
	}

	fn transform_boolconst(&mut self, mut expr: BoolConst) -> Expr {
		expr.into_variant()
	}

	fn transform_not(&mut self, mut expr: Not) -> Expr {
		match *expr.inner {
			Expr::Not(notnot) => self.transform(*notnot.inner),
			_ => expr.into_variant()
		}
	}

	fn transform_and(&mut self, mut expr: And) -> Expr {
		expr.into_variant()
	}

	fn transform_or(&mut self, mut expr: Or) -> Expr {
		expr.into_variant()
	}

	fn transform_xor(&mut self, mut expr: Xor) -> Expr {
		expr.into_variant()
	}

	fn transform_iff(&mut self, mut expr: Iff) -> Expr {
		expr.into_variant()
	}

	fn transform_implies(&mut self, mut expr: Implies) -> Expr {
		expr.into_variant()
	}

	fn transform_param_bool(&mut self, mut expr: ParamBool) -> Expr {
		expr.into_variant()
	}

	fn transform_equals(&mut self, mut expr: Equals) -> Expr {
		expr.into_variant()
	}

	fn transform_ite(&mut self, expr: IfThenElse) -> Expr {
		match *expr.cond {
			Expr::BoolConst(BoolConst{value: true}) => {
				simplify(*expr.then_case)
			},
			Expr::BoolConst(BoolConst{value: false}) => {
				simplify(*expr.else_case)
			},
			_ => {
				expr.into_variant()
			}
		}
		// expr.cond = self.boxed_transform(expr.cond);
		// expr.then_case = self.boxed_transform(expr.then_case);
		// expr.else_case = self.boxed_transform(expr.else_case);
		// expr.into_variant()
	}

	fn transform_symbol(&mut self, mut expr: Symbol) -> Expr {
		expr.into_variant()
	}

}

#[cfg(test)]
mod tests {
	use super::*;
	use ast::NaiveExprFactory;

	#[test]
	fn simplify_negneg_even() {
		let fab  = NaiveExprFactory::new();
		let expr = fab.bvneg(
			fab.bvneg(
				fab.bvneg(
					fab.bvneg(
						fab.bvconst(Bits(32), 42)
					)
				)
			)
		).unwrap();
		let simplified = simplify(expr);
		let expected   = fab.bvconst(Bits(32), 42).unwrap();
		assert_eq!(simplified, expected);
	}

	#[test]
	fn simplify_negneg_odd() {
		let fab  = NaiveExprFactory::new();
		let expr = fab.bvneg(
			fab.bvneg(
				fab.bvneg(
					fab.bvneg(
						fab.bvneg(
							fab.bvconst(Bits(32), 42)
						)
					)
				)
			)
		).unwrap();
		let simplified = simplify(expr);
		let expected   = fab.bvneg(fab.bvconst(Bits(32), 42)).unwrap();
		assert_eq!(simplified, expected);
	}

	#[test]
	fn simplify_notnot_even() {
		let fab  = NaiveExprFactory::new();
		let expr = fab.not(
			fab.not(
				fab.not(
					fab.not(
						fab.boolconst(false)
					)
				)
			)
		).unwrap();
		let simplified = simplify(expr);
		let expected   = fab.boolconst(false).unwrap();
		assert_eq!(simplified, expected);
	}

	#[test]
	fn simplify_notnot_odd() {
		let fab  = NaiveExprFactory::new();
		let expr = fab.not(
			fab.not(
				fab.not(
					fab.not(
						fab.not(
							fab.boolconst(false)
						)
					)
				)
			)
		).unwrap();
		let simplified = simplify(expr);
		let expected   = fab.not(fab.boolconst(false)).unwrap();
		assert_eq!(simplified, expected);
	}

	#[test]
	fn simplify_ite_const_true_cond() {
		let fab  = NaiveExprFactory::new();
		let expr = fab.ite(
			fab.boolconst(true),
			fab.bvconst(Bits(32), 42),
			fab.bvneg(
				fab.bvconst(Bits(32), 1337)
			)
		).unwrap();
		let simplified = simplify(expr);
		let expected   = fab.bvconst(Bits(32), 42).unwrap();
		assert_eq!(simplified, expected);
	}

	#[test]
	fn simplify_ite_const_false_cond() {
		let fab  = NaiveExprFactory::new();
		let expr = fab.ite(
			fab.boolconst(false),
			fab.bvconst(Bits(32), 42),
			fab.bvneg(
				fab.bvneg(
					fab.bvconst(Bits(32), 1337)
				)
			)
		).unwrap();
		let simplified = simplify(expr);
		let expected   = fab.bvconst(Bits(32), 1337).unwrap();
		assert_eq!(simplified, expected);
	}
}
