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

	fn transform_bvneg(&mut self, mut expr: Neg) -> Expr {
		match *expr.inner {
			Expr::Neg(negneg) => {
				self.transform(*negneg.inner)
			}
			Expr::BitVecConst(BitVecConst{ref value, ty}) if value.is_zero() => {
				Expr::bvconst(ty.bits().unwrap(), 0)
			}
			_ => {
				self.transform_assign(&mut expr.inner);
				expr.into_variant()
			}
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

	fn transform_not(&mut self, mut expr: Not) -> Expr {
		expr.inner = self.boxed_transform(expr.inner);
		match *expr.inner {
			Expr::Not(notnot) => self.transform(*notnot.inner),
			Expr::BoolConst(BoolConst{value}) => Expr::boolconst(!value),
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

	fn transform_xor(&mut self, mut expr: Xor) -> Expr {
		expr.left  = self.boxed_transform(expr.left);
		expr.right = self.boxed_transform(expr.right);
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

	fn transform_equals(&mut self, mut expr: Equals) -> Expr {
		assert!(expr.exprs.len() >= 2,
			"Internal Solver Error: Simplifier::transform_equals: Equality requires at minimum 2 child expressions!");

		// // Flattens equality child expressions -> this strengthens the following unique-elemination procedure.
		// fn flattening(child: Expr, eq: &mut Equals) {
		// 	if let Expr::Equals(subeq) = child {
		// 		if subeq.inner_ty == eq.inner_ty {
		// 			for subchild in subeq.exprs {
		// 				flattening(subchild, eq)
		// 			}
		// 		}
		// 		else {
		// 			eq.exprs.push(subeq.into_variant())
		// 		}
		// 	}
		// 	else {
		// 		eq.exprs.push(child)
		// 	}
		// };
		// use std::mem;
		// for child in mem::replace(&mut expr.exprs, vec![]) {
		// 	flattening(child, &mut expr)
		// }

		// Simplify child expressions.
		for child in expr.childs_mut() {
			self.transform_assign(child);
		}

		// Normalize child expressions and eleminate duplicates `a = b = a` => `a = b`
		expr.exprs.sort();
		expr.exprs.dedup();

		// After deduplication: Find equal childs tautology:
		//  - `(= a ... a) => true`
		if expr.exprs.len() == 1 {
			return Expr::boolconst(true)
		}

		// Find const constradiction pairs:
		//  - `(= 42 1337)    => false`
		//  - `(= false true) => false`
		use itertools::Itertools;
		// TODO: Optimization: Filter for `BitVecConst` and `BoolConst`.
		{
			let has_const_contradicting_pair = expr.exprs.iter().cartesian_product(&expr.exprs).any(|(l,r)| {
				match (l, r) {
					(&Expr::BitVecConst(BitVecConst{value: ref v1, ..}),
					 &Expr::BitVecConst(BitVecConst{value: ref v2, ..})) => {
						v1 != v2
					},
					(&Expr::BoolConst(BoolConst{value: ref v1, ..}),
					 &Expr::BoolConst(BoolConst{value: ref v2, ..})) => {
						v1 != v2
					},
					_ => false
				}
			});
			if has_const_contradicting_pair {
				return Expr::boolconst(false)
			}
		}

		// Find contradiction pairs:
		//  - `(= a not(a)) => false`
		//  - `(= x (-x))   => false`
		{
			let has_symbolic_contradicting_pair = expr.exprs.iter().cartesian_product(&expr.exprs).any(|(l, r)| {
				match (l, r) {
					(non_negated, &Expr::Not(Not{inner: ref negated    })) |
					(non_negated, &Expr::Neg(Neg{inner: ref negated, ..})) => {
						&**negated == non_negated
					},
					_ => false
				}
			});
			if has_symbolic_contradicting_pair {
				return Expr::boolconst(false)
			}
		}

		// // Simplify child expressions.
		// for child in expr.childs_mut() {
		// 	self.transform_assign(child);
		// }

		// Finally check for constant tautology evaluation.
		//  - `= 42 42 42 => true`
		// 
		// Note: This should be equal to the above dedup + len check.
		if let Some((head, tail)) = expr.exprs.split_first() {
			if tail.iter().all(|child| head == child) {
				return Expr::boolconst(true)
			}
		}

		expr.into_variant()
	}

	fn transform_ite(&mut self, mut expr: IfThenElse) -> Expr {
		self.transform_assign(&mut expr.cond);

		if let Expr::BoolConst(BoolConst{value}) = *expr.cond {
			if value {
				return self.transform(*expr.then_case)
			}
			else {
				return self.transform(*expr.else_case)
			}
		}

		self.transform_assign(&mut expr.then_case);
		self.transform_assign(&mut expr.else_case);

		// Lower to then-case when both branches are equal.
		//  - `ite c a a => a`
		// 
		// Note: This could also be checked before traversing through 
		//       through the branches but was downstreamed in order to
		//       profit from possible simplifications.
		if expr.then_case == expr.else_case {
			return expr.then_case.into_variant()
		}

		expr.into_variant()
	}

	fn transform_symbol(&mut self, expr: Symbol) -> Expr {
		expr.into_variant()
	}

}

#[cfg(test)]
mod tests {
	use super::*;
	use ast::NaiveExprFactory;

	/// Takes expression results to shift all the unwraps into this single function
	/// so that boilerplate code is significantly reduced.
	fn assert_simplified(input: Result<Expr>, expected: Result<Expr>) {
		let input      = input.unwrap();
		let expected   = expected.unwrap();
		let simplified = simplify(input);
		assert_eq!(simplified, expected);
	}

	#[derive(Debug, Copy, Clone, PartialEq, Eq)]
	enum Sign {
		Signed,
		Unsigned
	}
	use self::Sign::{Signed, Unsigned};

	impl NaiveExprFactory {
		/// Dispatches to either `bvudiv` or `bvsdiv` based on the given `sign`.
		/// 
		/// This is mainly used to improve test code for the simplifier.
		fn bvdiv<X, Y>(&self, sign: Sign, dividend: X, divisor: Y) -> Result<Expr>
			where X: Into<Result<Expr>>,
			      Y: Into<Result<Expr>>
		{
			match sign {
				Signed   => self.bvsdiv(dividend, divisor),
				Unsigned => self.bvudiv(dividend, divisor)
			}
		}
	}

	mod neg {
		use super::*;

		#[test]
		fn involution_even() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.bvneg(
					f.bvneg(
						f.bitvec("x", Bits(32))
					)
				),
				f.bitvec("x", Bits(32))
			);
		}

		#[test]
		fn involution_odd() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.bvneg(
					f.bvneg(
						f.bvneg(
							f.bitvec("x", Bits(32))
						)
					)
				),
				f.bvneg(f.bitvec("x", Bits(32)))
			);
		}

		#[test]
		fn neutral_element() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.bvneg(f.bvconst(Bits(32), 0)),
				f.bvconst(Bits(32), 0)
			);
		}
	}

	mod not {
		use super::*;

		#[test]
		fn involution_even() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.not(f.not(f.boolean("a"))),
				f.boolean("a")
			);
		}

		#[test]
		fn involution_odd() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.not(
					f.not(
						f.not(
							f.boolean("a")
						)
					)
				),
				f.not(f.boolean("a")));
		}

		#[test]
		fn const_eval() {
			fn simplify_not_const_impl(flag: bool) {
				let f = NaiveExprFactory::new();
				assert_simplified(
					f.not(f.boolconst(flag)),
					f.boolconst(!flag)
				);
			}
			simplify_not_const_impl(true);
			simplify_not_const_impl(false);
		}
	}

	mod ite {
		use super::*;

		#[test]
		fn const_eval() {
			fn simplify_ite_const_impl(flag: bool) {
				fn simplify_ite_const_impl_gen(
					flag: bool,
					then_expr: Result<Expr>,
					else_expr: Result<Expr>,
					f: NaiveExprFactory,
				){
					let ite = f.ite(
						f.boolconst(flag),
						then_expr.clone(),
						else_expr.clone()
					);
					assert_simplified(
						ite.clone(),
						if flag {
							then_expr.clone()
						}
						else {
							else_expr.clone()
						}
					);
				}

				let f = NaiveExprFactory::new();

				simplify_ite_const_impl_gen(
					flag,
					f.bitvec("x", Bits(32)),
					f.bitvec("y", Bits(32)),
					f.clone()
				);
				simplify_ite_const_impl_gen(
					flag,
					f.boolean("a"),
					f.boolean("b"),
					f.clone()
				);
			}
			simplify_ite_const_impl(true);
			simplify_ite_const_impl(false);
		}

		#[test]
		fn equal_branches() {
			let f  = NaiveExprFactory::new();
			assert_simplified(
				f.ite(
					f.boolean("a"),
					f.boolean("b"),
					f.boolean("b"),
				),
				f.boolean("b")
			);
			assert_simplified(
				f.ite(
					f.boolean("a"),
					f.bitvec("x", Bits(32)),
					f.bitvec("x", Bits(32)),
				),
				f.bitvec("x", Bits(32))
			);
		}
	}

	mod equals {
		use super::*;

		#[test]
		fn symbolic_tautology() {
			let f = NaiveExprFactory::new();

			assert_simplified(
				f.eq(
					f.boolean("a"),
					f.boolean("a")
				),
				f.boolconst(true)
			);

			assert_simplified(
				f.eq(
					f.bitvec("x", Bits(32)),
					f.bitvec("x", Bits(32))
				),
				f.boolconst(true)
			);
		}

		#[test]
		fn symbolic_contradictions() {
			let f  = NaiveExprFactory::new();

			assert_simplified(
				f.eq(
					f.boolean("a"),
					f.not(f.boolean("a"))
				),
				f.boolconst(false)
			);

			assert_simplified(
				f.eq(
					f.bitvec("x", Bits(32)),
					f.bvneg(f.bitvec("x", Bits(32)))
				),
				f.boolconst(false)
			);
		}

		#[test]
		fn const_contradiction() {
			let f = NaiveExprFactory::new();

			assert_simplified(
				f.eq(
					f.boolconst(true),
					f.boolconst(false)
				),
				f.boolconst(false)
			);

			assert_simplified(
				f.eq(
					f.bvconst(Bits(32),   42),
					f.bvconst(Bits(32), 1337)
				),
				f.boolconst(false)
			);
		}

		#[test]
		fn symbolic_tautology_diff_type() {
			let f = NaiveExprFactory::new();

			assert_simplified(
				f.eq(
					f.eq(
						f.boolean("a"),
						f.boolean("a")
					),
					f.eq(
						f.bitvec("x", Bits(32)),
						f.bitvec("x", Bits(32))
					)
				),
				f.boolconst(true)
			);
		}

		#[test]
		fn const_tautology_diff_type() {
			let f  = NaiveExprFactory::new();

			assert_simplified(
				f.eq(
					f.eq(
						f.boolconst(false),
						f.boolconst(false)
					),
					f.eq(
						f.bvconst(Bits(32), 42),
						f.bvconst(Bits(32), 42)
					)
				),
				f.boolconst(true)
			);
		}

		#[test]
		fn const_eval() {
			fn const_eval_bool(f1: bool, f2: bool) {
				let f = NaiveExprFactory::new();
				assert_simplified(
					f.eq(
						f.boolconst(f1),
						f.boolconst(f2)
					),
					f.boolconst(f1 == f2)
				);
			}

			const_eval_bool(false, false);
			const_eval_bool(false,  true);
			const_eval_bool( true, false);
			const_eval_bool( true,  true);

			fn const_eval_bv(v1: u64, v2: u64) {
				let f = NaiveExprFactory::new();
				assert_simplified(
					f.eq(
						f.bvconst(Bits(32), v1),
						f.bvconst(Bits(32), v2)
					),
					f.boolconst(v1 == v2)
				);
			}

			const_eval_bv( 0,    1);
			const_eval_bv(42, 1337);
			const_eval_bv( 0,    0);
			const_eval_bv(10,   10);
		}

		/// This test is maybe misplaced and could be moved to a future
		/// lowering pass that is used for equisatisfiability conserving
		/// structural transformations between expression types that reduces
		/// the number of different expression types and comprehends
		/// expressions via flattening.
		#[test]
		#[ignore]
		fn flattening() {
			let f = NaiveExprFactory::new();

			assert_simplified(
				f.and(
					f.and(
						f.eq(
							f.boolean("a"),
							f.boolean("b")
						),
						f.eq(
							f.boolean("b"),
							f.boolean("c")
						)
					),
					f.and(
						f.eq(
							f.boolean("c"),
							f.boolean("d")
						),
						f.eq(
							f.boolean("d"),
							f.boolean("e")
						)
					)
				),

				Ok(
					Equals{
						exprs: vec![
							Expr::Symbol(Symbol{ name: SymName(0), ty: Type::Boolean }),
							Expr::Symbol(Symbol{ name: SymName(1), ty: Type::Boolean }),
							Expr::Symbol(Symbol{ name: SymName(2), ty: Type::Boolean }),
							Expr::Symbol(Symbol{ name: SymName(3), ty: Type::Boolean }),
						],
						inner_ty: Type::Boolean
					}.into_variant()
				)
			);
		}
	}

	mod add {
		use super::*;

		#[test]
		#[ignore]
		fn neutral_element() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.bvadd(
					f.bitvec("x", Bits(32)),
					f.bvconst(Bits(32), 0)
				),
				f.bitvec("x", Bits(32))
			);
			assert_simplified(
				f.bvadd(
					f.bvconst(Bits(32), 0),
					f.bitvec("x", Bits(32))
				),
				f.bitvec("x", Bits(32))
			);
		}

		#[test]
		#[ignore]
		fn inserse_elimination() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.bvadd(
					f.bitvec("x", Bits(32)),
					f.bvneg(f.bitvec("x", Bits(32)))
				),
				f.bvconst(Bits(32), 0)
			);
			assert_simplified(
				f.bvadd(
					f.bvneg(f.bitvec("x", Bits(32))),
					f.bitvec("x", Bits(32))
				),
				f.bvconst(Bits(32), 0)
			);
		}

		#[test]
		#[ignore]
		fn negation_pulling() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.bvadd(
					f.bvneg(f.bitvec("x", Bits(32))),
					f.bvneg(f.bitvec("y", Bits(32)))
				),
				f.bvneg(
					f.bvadd(
						f.bitvec("x", Bits(32)),
						f.bitvec("y", Bits(32))
					)
				)
			);
		}

		#[test]
		#[ignore]
		fn flattening() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.bvadd(
					f.bvadd(
						f.bitvec("x1", Bits(32)),
						f.bitvec("y1", Bits(32))
					),
					f.bvadd(
						f.bitvec("x2", Bits(32)),
						f.bitvec("y2", Bits(32))
					)
				),

				Ok(Add{
					terms: vec![
						Expr::Symbol(Symbol{ name: SymName(0), ty: Type::BitVec(32) }),
						Expr::Symbol(Symbol{ name: SymName(1), ty: Type::BitVec(32) }),
						Expr::Symbol(Symbol{ name: SymName(2), ty: Type::BitVec(32) }),
						Expr::Symbol(Symbol{ name: SymName(3), ty: Type::BitVec(32) }),
					],
					ty: Type::BitVec(32)
				}.into_variant())
			);
		}
	}

	mod mul {
		use super::*;

		#[test]
		#[ignore]
		fn neutral_element() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.bvmul(
					f.bitvec("x", Bits(32)),
					f.bvconst(Bits(32), 1)
				),
				f.bitvec("x", Bits(32))
			);
			assert_simplified(
				f.bvmul(
					f.bvconst(Bits(32), 1),
					f.bitvec("x", Bits(32))
				),
				f.bitvec("x", Bits(32))
			);
		}

		#[test]
		#[ignore]
		fn null_element() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.bvmul(
					f.bitvec("x", Bits(32)),
					f.bvconst(Bits(32), 0)
				),
				f.bvconst(Bits(32), 0)
			);
			assert_simplified(
				f.bvmul(
					f.bvconst(Bits(32), 0),
					f.bitvec("x", Bits(32))
				),
				f.bvconst(Bits(32), 0)
			);
		}

		#[test]
		#[ignore]
		fn negation_pulling() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.bvmul(
					f.bvneg(f.bitvec("x", Bits(32))),
					f.bitvec("y", Bits(32))
				),
				f.bvneg(
					f.bvmul(
						f.bitvec("x", Bits(32)),
						f.bitvec("y", Bits(32))
					)
				)
			);
			assert_simplified(
				f.bvmul(
					f.bitvec("x", Bits(32)),
					f.bvneg(f.bitvec("y", Bits(32)))
				),
				f.bvneg(
					f.bvmul(
						f.bitvec("x", Bits(32)),
						f.bitvec("y", Bits(32))
					)
				)
			);
			assert_simplified(
				f.bvmul(
					f.bvneg(f.bitvec("x", Bits(32))),
					f.bvneg(f.bitvec("y", Bits(32)))
				),
				f.bvmul(
					f.bitvec("x", Bits(32)),
					f.bitvec("y", Bits(32))
				)
			);
		}

		#[test]
		#[ignore]
		fn inverse_elimination() {
			fn inverse_elimination_impl(sign: Sign) {
				let f = NaiveExprFactory::new();
				assert_simplified(
					f.bvmul(
						f.bitvec("x", Bits(32)),
						f.bvdiv(sign,
							f.bvconst(Bits(32), 1),
							f.bitvec("x", Bits(32))
						)
					),
					f.bvconst(Bits(32), 1)
				);
				assert_simplified(
					f.bvmul(
						f.bvdiv(sign,
							f.bvconst(Bits(32), 1),
							f.bitvec("x", Bits(32))
						),
						f.bitvec("x", Bits(32))
					),
					f.bvconst(Bits(32), 1)
				);
			}
			inverse_elimination_impl(Signed);
			inverse_elimination_impl(Unsigned);
		}

		#[test]
		#[ignore]
		fn flattening() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.bvmul(
					f.bvmul(
						f.bitvec("x1", Bits(32)),
						f.bitvec("y1", Bits(32))
					),
					f.bvmul(
						f.bitvec("x2", Bits(32)),
						f.bitvec("y2", Bits(32))
					)
				),

				// f.bvprod(vec![
				// 	f.bitvec("x1", Bits(32)),
				// 	f.bitvec("y1", Bits(32)),
				// 	f.bitvec("x2", Bits(32)),
				// 	f.bitvec("y2", Bits(32))
				// ])

				Ok(Mul{
					factors: vec![
						Expr::Symbol(Symbol{ name: SymName(0), ty: Type::BitVec(32) }),
						Expr::Symbol(Symbol{ name: SymName(1), ty: Type::BitVec(32) }),
						Expr::Symbol(Symbol{ name: SymName(2), ty: Type::BitVec(32) }),
						Expr::Symbol(Symbol{ name: SymName(3), ty: Type::BitVec(32) }),
					],
					ty: Type::BitVec(32)
				}.into_variant())
			);
		}
	}

	mod div {
		use super::*;

		#[test]
		#[ignore]
		fn neutral_element() {
			fn neutral_element_impl(sign: Sign) {
				let f = NaiveExprFactory::new();
				assert_simplified(
					f.bvdiv(sign,
						f.bitvec("x", Bits(32)),
						f.bvconst(Bits(32), 1)
					),
					f.bitvec("x", Bits(32))
				);
			}
			neutral_element_impl(Signed);
			neutral_element_impl(Unsigned);
		}

		#[test]
		#[ignore]
		fn div_by_self() {
			fn div_by_self_impl(sign: Sign) {
				let f = NaiveExprFactory::new();
				assert_simplified(
					f.bvdiv(sign,
						f.bitvec("x", Bits(32)),
						f.bitvec("x", Bits(32))
					),
					f.bvconst(Bits(32), 1)
				);
			}
			div_by_self_impl(Signed);
			div_by_self_impl(Unsigned);
		}

		// TODO: What to do if divisor is maybe zero?
		#[test]
		#[ignore]
		fn division_of_zero() {
			fn division_of_zero_impl(sign: Sign) {
				let f = NaiveExprFactory::new();
				assert_simplified(
					f.bvdiv(sign,
						f.bvconst(Bits(32), 0),
						f.bitvec("x", Bits(32))
					),
					f.bvconst(Bits(32), 0)
				);
			}
			division_of_zero_impl(Signed);
			division_of_zero_impl(Unsigned);
		}

		#[test]
		#[ignore]
		fn negation_pulling() {
			fn negation_pulling_impl(sign: Sign) {
				let f = NaiveExprFactory::new();
				// Unsigned
				assert_simplified(
					f.bvdiv(sign,
						f.bvneg(f.bitvec("x", Bits(32))),
						f.bitvec("y", Bits(32))
					),
					f.bvneg(
						f.bvdiv(sign,
							f.bitvec("x", Bits(32)),
							f.bitvec("y", Bits(32))
						)
					)
				);
				assert_simplified(
					f.bvdiv(sign,
						f.bitvec("x", Bits(32)),
						f.bvneg(f.bitvec("y", Bits(32)))
					),
					f.bvneg(
						f.bvdiv(sign,
							f.bitvec("x", Bits(32)),
							f.bitvec("y", Bits(32))
						)
					)
				);
				assert_simplified(
					f.bvdiv(sign,
						f.bvneg(f.bitvec("x", Bits(32))),
						f.bvneg(f.bitvec("y", Bits(32)))
					),
					f.bvdiv(sign,
						f.bitvec("x", Bits(32)),
						f.bitvec("y", Bits(32))
					)
				);
			}
			negation_pulling_impl(Signed);
			negation_pulling_impl(Unsigned);
		}

		/// The reason why an undefined expression is undefined.
		/// 
		/// This may be deprecated in future versions and should be
		/// seen as a stub implementation as long as this feature is not implemented.
		#[derive(Debug, Copy, Clone, PartialEq, Eq)]
		enum ReasonUndefined {
			DivisionByZero
		}
		use self::ReasonUndefined::DivisionByZero;

		impl NaiveExprFactory {
			/// It has yet to be decided if an expression factory should support creation of
			/// expressions that represent an undefined state.
			/// 
			/// This is useful to model scenarios such as division by zero.
			/// However, there is currently no solution as to how such scenarios
			/// should be handled within the solver.
			/// 
			/// This may be deprecated in future versions and should be
			/// seen as a stub implementation as long as this feature is not implemented.
			fn undefined(&self, reason: ReasonUndefined) -> Result<Expr> {
				match reason {
					DivisionByZero => Err(::ast::errors::AstError(::ast::errors::ErrorKind::DivisionByZero))
				}
			}
		}

		#[test]
		#[ignore]
		fn division_by_zero() {
			fn division_by_zero_impl(sign: Sign) {
				let f = NaiveExprFactory::new();
				assert_simplified(
					f.bvdiv(sign,
						f.bitvec("x", Bits(32)),
						f.bvconst(Bits(32), 0)
					),
					f.undefined(DivisionByZero)
				);
			}
			division_by_zero_impl(Signed);
			division_by_zero_impl(Unsigned);
		}

		#[test]
		#[ignore]
		fn trivial_const_eval() {
			fn trivial_const_eval_impl(sign: Sign, dividend: u64, divisor: u64) {
				let f = NaiveExprFactory::new();
				assert_simplified(
					f.bvdiv(sign,
						f.bvconst(Bits(32), dividend), // this is smaller
						f.bvconst(Bits(32), divisor)  // than this
					),
					if dividend < divisor {
						f.bvconst(Bits(32), 0) // so it can be easily lowered to zero
					}
					else if dividend == divisor {
						f.bvconst(Bits(32), 1) // or 1 if both are equal
					}
					else { // nothing happenes: Handled by `ConstEvaluator`
						f.bvdiv(sign,
							f.bvconst(Bits(32), dividend),
							f.bvconst(Bits(32), divisor)
						)
					}
				);
			}
			let candidates: [u64; 6] = [1, 2, 42, 100, 420, 1337];
			use itertools::Itertools;
			for (&dividend, &divisor) in candidates.iter().cartesian_product(candidates.iter()) {
				trivial_const_eval_impl(Signed, dividend, divisor);
				trivial_const_eval_impl(Unsigned, dividend, divisor);
			}
		}

		// TODO:
		//  - lower_to_mul
		//  - lower_to_shift
	}

	#[test]
	fn integration_01() {
		let f = NaiveExprFactory::new();

		let expr = f.eq(
			f.eq(
				f.eq(
					f.boolconst(true),
					f.boolconst(true)
				),
				f.eq(
					f.bvconst(Bits(32), 42),
					f.bvconst(Bits(32), 42)
				)
			),
			f.eq(
				f.eq(
					f.boolconst(true),
					f.boolconst(true)
				),
				f.eq(
					f.eq(
						f.boolconst(true),
						f.boolconst(true)
					),
					f.eq(
						f.boolconst(true),
						f.eq(
							f.boolconst(true),
							f.boolconst(false)
						)
					)
				)
			)
		).unwrap();

		let simplified = simplify(expr);
		let expected   = f.boolconst(false).unwrap();
		assert_eq!(simplified, expected);
	}

	#[test]
	fn integration_02() {
		let f = NaiveExprFactory::new();

		let expr = f.eq(
			f.eq(
				f.eq(
					f.boolconst(false),
					f.eq(
						f.bvconst(Bits(32), 42),
						f.bvconst(Bits(32), 1337)
					)
				),
				f.eq(
					f.bvconst(Bits(32), 42),
					f.bvconst(Bits(32), 42)
				)
			),
			f.eq(
				f.eq(
					f.not(f.boolconst(true)),
					f.eq(
						f.boolconst(true),
						f.not(f.boolconst(true))
					)
				),
				f.eq(
					f.eq(
						f.boolconst(true),
						f.boolconst(true)
					),
					f.eq(
						f.bvconst(Bits(64), 100),
						f.bvneg(f.bvneg(f.bvconst(Bits(64), 100)))
					)
				)
			)
		).unwrap();

		let simplified = simplify(expr);
		let expected   = f.boolconst(true).unwrap();
		assert_eq!(simplified, expected);
	}
}
