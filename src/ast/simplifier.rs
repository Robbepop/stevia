use num::Integer;
use itertools::Itertools;

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
/// 
/// TODO: Currently we do three iterations since we do not track if something
///       got simplified to detect a fix-point. This is bad and should be changed
///       in a future version!
pub fn simplify(mut expr: Expr) -> Expr {
	let mut simplifier = Simplifier::new();
	for _ in 0..5 { simplifier.transform_assign(&mut expr) }
	expr
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

	fn transform_bvneg(&mut self, mut neg: Neg) -> Expr {
		match *neg.inner {
			// Involution
			Expr::Neg(negneg) => {
				self.transform(*negneg.inner)
			}

			// Distribute negates through summands.
			Expr::Add(mut add) => {
				add.terms = add.terms
					.into_iter()
					.map(|t| Expr::bvneg(Box::new(t)))
					.collect();
				self.transform_bvadd(add)
			}

			// Distribute negates though factors.
			Expr::Mul(mut mul) => {
				mul.childs_mut().foreach(|f| f.assign_fn(Expr::unwrap_neg));
				mul.factors.last_mut().map(|f| f.assign_fn(Expr::wrap_with_neg));
				self.transform_bvmul(mul)
			}

			// Neutral element
			Expr::BitVecConst(BitVecConst{ref value, ty}) if value.is_zero() => {
				Expr::bvconst(ty.bits().unwrap(), 0)
			}

			// No rule was applicable
			_ => {
				self.transform_assign(&mut neg.inner);
				neg.into_variant()
			}
		}
	}

	fn transform_bvadd(&mut self, mut add: Add) -> Expr {
		add.childs_mut().foreach(|child| self.transform_assign(child));

		// Neutral element elimination.
		add.terms.retain(|child| !child.is_bvconst_with_value(0));

		// Flattening of nested adds.
		// TODO: Decide if it is useful to also pull-into negated-adds.
		//       Note: This requires to negate all pulled-in childs!
		use std::mem;
		for child in mem::replace(&mut add.terms, vec![]) {
			match child {
				Expr::Add(subadd) => {
					add.terms.extend(subadd.into_childs())
				}
				_ => {
					add.terms.push(child)
				}
			}
		}

		// Dissolve multiplicities: `(add a b a a)` to `(add (mul 3 a) b)`
		// TODO:

		if add.terms.iter().all(|child| child.kind() == ExprKind::Neg) {
			// Negation pulling
			// TODO: Decide if this is really needed.
			//       The oposite of this simplification would be great for flattening!
		}
		else if add.terms.iter().any(|child| child.kind() == ExprKind::Neg) {
			// Not all but some are neg -> inverse elimination possible

			// This piece of code does the following:
			// 
			// In case of an expression with a structure as:
			//  (a + b + (-c) + (-b))
			// or in terms of SMTLib: (Lisp-like)
			//  (+ a b (-c) (-b))
			// 
			// This checks for additive inverses and eliminates them.
			// So given the input from above the expected output is this:
			//  (+ a (-c))
			// 
			// Hopefully this can be rewritten to be less ugly.
			// Maybe based on intelligent sorting and deduplication?
			let (negs, nonnegs): (Vec<_>, Vec<_>) = mem::replace(&mut add.terms, vec![])
				.into_iter()
				.partition(|child| if let Expr::Neg(_) = *child { true } else { false });
			// This mapping is only done to make the following transformations less ugly.
			let mut negs: Vec<Neg> = negs
				.into_iter()
				.map(|neg| match neg {
					Expr::Neg(n) => n, // <- this is safe to do here since we already filtered above!
					_            => panic!("Internal Error: Expected a bvneg expression!")
				})
				.collect();
			// Partition into non-eliminated and eliminated to further 
			// enhance elimination for the other partition: The negations!
			let (mut nonnegs, eliminated): (Vec<_>, Vec<_>) = nonnegs
				.into_iter()
				.partition(|nonneg| negs.iter().find(|neg| &*neg.inner == nonneg).is_none());
			negs.retain(|neg| {
				eliminated.iter().find(|nonneg| *neg.inner == **nonneg).is_none()
			});
			// Re-insert non-eliminated expressions into the original vector.
			add.terms.append(&mut nonnegs);
			add.terms.extend(negs.into_iter().map(|f| f.into_variant()));
		}

		add.terms.sort();

		if add.terms.is_empty() {
			Expr::bvconst(add.ty().bits().unwrap(), 0)
		}
		else if add.terms.len() == 1 {
			add.terms.pop().unwrap()
		}
		else {
			add.into_variant()
		}
	}

	fn transform_bvmul(&mut self, mut mul: Mul) -> Expr {
		mul.childs_mut().foreach(|child| self.transform_assign(child));

		// Flattening of nested muls.
		use std::mem;
		for child in mem::replace(&mut mul.factors, vec![]) {
			match child {
				Expr::Mul(submul) => {
					mul.factors.extend(submul.into_childs())
				}
				_ => {
					mul.factors.push(child)
				}
			}
		}

		// Normalization
		mul.factors.sort();

		// Negation normalization
		{
			// Count negations.
			let num_negs = mul.factors
				.iter()
				.filter(|e| e.kind() == ExprKind::Neg)
				.count();
			// Remove all negations within this multiplication.
			mul.childs_mut().foreach(|f| f.assign_fn(Expr::unwrap_neg));
			// Normalize again without negations.
			mul.factors.sort();
			// If there were an odd number of negations we
			// need to put a negation back again.
			if num_negs.is_odd() {
				mul.factors
					.last_mut()
					.map(|f| f.assign_fn(Expr::wrap_with_neg));
			}
			// Normalize again with maybe single-negation.
			mul.factors.sort();
		}

		// Neutral element: `(* a 1)` to `(* a)`
		mul.factors.retain(|x| !x.is_bvconst_with_value(1));

		// Null element: `(* a 0)` to `0`
		if mul.factors.iter().any(|x| x.is_bvconst_with_value(0)) {
			return Expr::bvconst(mul.ty.bits().unwrap(), 0)
		}

		match mul.arity() {
			// No more elements left -> simply return 0
			0 => Expr::bvconst(mul.ty.bits().unwrap(), 0),
			// One element left, e.g. when it was `(* a 1)`, so return `a`
			1 => mul.factors.pop().unwrap(),
			// Else nothing special happens
			_ => mul.into_variant()
		}
	}

	fn transform_bvsub(&mut self, mut sub: Sub) -> Expr {
		self.transform_assign(&mut sub.minuend);
		self.transform_assign(&mut sub.subtrahend);

		// Inverse element: `(- a a) -> 0`
		if sub.minuend == sub.subtrahend {
			return Expr::bvconst(sub.ty.bits().unwrap(), 0)
		}

		// Null element: `(- 0 a) -> -a`
		if sub.minuend.is_bvconst_with_value(0) {
			return self.transform(
				Expr::Neg(Neg{ ty: sub.ty(), inner: sub.subtrahend }))
		}

		// Neutral element: `(- a 0) -> a`
		if sub.subtrahend.is_bvconst_with_value(0) {
			return *sub.minuend // already simplified (see above!)
		}

		// Lower to `Add`
		Expr::bvsum(
			sub.ty(),
			vec![
				self.transform_bvneg(Neg{ ty: sub.ty(), inner: sub.subtrahend }),
				*sub.minuend
			]
		)
	}

	fn transform_bvudiv(&mut self, mut udiv: Div) -> Expr {
		self.transform_assign(&mut udiv.dividend);
		self.transform_assign(&mut udiv.divisor);
		udiv.into_variant()
	}

	fn transform_bvumod(&mut self, mut umod: Mod) -> Expr {
		self.transform_assign(&mut umod.dividend);
		self.transform_assign(&mut umod.divisor);
		umod.into_variant()
	}

	fn transform_bvsdiv(&mut self, mut sdiv: SignedDiv) -> Expr {
		self.transform_assign(&mut sdiv.dividend);
		self.transform_assign(&mut sdiv.divisor);
		sdiv.into_variant()
	}

	fn transform_bvsmod(&mut self, mut smod: SignedMod) -> Expr {
		self.transform_assign(&mut smod.dividend);
		self.transform_assign(&mut smod.divisor);
		smod.into_variant()
	}

	fn transform_bvsrem(&mut self, mut srem: SignedRem) -> Expr {
		self.transform_assign(&mut srem.dividend);
		self.transform_assign(&mut srem.divisor);
		srem.into_variant()
	}

	//=========================================================================
	// BITVEC BITWISE OPERATIONS
	//=========================================================================

	fn transform_bvnot(&mut self, mut bvnot: BitNot) -> Expr {
		self.transform_assign(&mut bvnot.inner);
		bvnot.into_variant()
	}

	fn transform_bvand(&mut self, mut bvand: BitAnd) -> Expr {
		self.transform_assign(&mut bvand.left);
		self.transform_assign(&mut bvand.right);
		bvand.into_variant()
	}

	fn transform_bvor(&mut self, mut bvor: BitOr) -> Expr {
		self.transform_assign(&mut bvor.left);
		self.transform_assign(&mut bvor.right);
		bvor.into_variant()
	}

	fn transform_bvxor(&mut self, mut bvxor: BitXor) -> Expr {
		self.transform_assign(&mut bvxor.left);
		self.transform_assign(&mut bvxor.right);
		bvxor.into_variant()
	}

	fn transform_bvnand(&mut self, mut bvnand: BitNand) -> Expr {
		self.transform_assign(&mut bvnand.left);
		self.transform_assign(&mut bvnand.right);
		bvnand.into_variant()
	}

	fn transform_bvnor(&mut self, mut bvnor: BitNor) -> Expr {
		self.transform_assign(&mut bvnor.left);
		self.transform_assign(&mut bvnor.right);
		bvnor.into_variant()
	}

	fn transform_bvxnor(&mut self, mut bvxnor: BitXnor) -> Expr {
		self.transform_assign(&mut bvxnor.left);
		self.transform_assign(&mut bvxnor.right);
		bvxnor.into_variant()
	}

	//=========================================================================
	// BITVEC COMPARISONS
	//=========================================================================

	fn transform_bvult(&mut self, mut ult: Lt) -> Expr {
		self.transform_assign(&mut ult.left);
		self.transform_assign(&mut ult.right);
		// TODO: `x < y where x < y and x,y consteval => true`
		// TODO: `x < y where not(x < y) and x,y consteval => false`
		ult.into_variant()
	}

	fn transform_bvule(&mut self, mut ule: Le) -> Expr {
		self.transform_assign(&mut ule.left);
		self.transform_assign(&mut ule.right);
		// TODO: Convert `left =< right` to `not(left > right)` to `not(right < left)`
		//       Lower to `not` and `lt` only.
		ule.into_variant()
	}

	fn transform_bvugt(&mut self, ugt: Gt) -> Expr {
		self.transform_bvult(
			Lt{left: ugt.right, right: ugt.left, inner_ty: ugt.inner_ty})
	}

	fn transform_bvuge(&mut self, uge: Ge) -> Expr {
		self.transform_bvule(
			Le{left: uge.right, right: uge.left, inner_ty: uge.inner_ty})
	}

	fn transform_bvslt(&mut self, mut slt: SignedLt) -> Expr {
		self.transform_assign(&mut slt.left);
		self.transform_assign(&mut slt.right);
		slt.into_variant()
	}

	fn transform_bvsle(&mut self, mut sle: SignedLe) -> Expr {
		self.transform_assign(&mut sle.left);
		self.transform_assign(&mut sle.right);
		sle.into_variant()
	}

	fn transform_bvsgt(&mut self, sgt: SignedGt) -> Expr {
		self.transform_bvslt(
			SignedLt{left: sgt.right, right: sgt.left, inner_ty: sgt.inner_ty})
	}

	fn transform_bvsge(&mut self, sge: SignedGe) -> Expr {
		self.transform_bvsle(
			SignedLe{left: sge.right, right: sge.left, inner_ty: sge.inner_ty})
	}

	//=========================================================================
	// BITVEC SHIFT
	//=========================================================================

	fn transform_bvushl(&mut self, mut ushl: Shl) -> Expr {
		self.transform_assign(&mut ushl.shifted);
		self.transform_assign(&mut ushl.shift_amount);
		ushl.into_variant()
	}

	fn transform_bvushr(&mut self, mut ushr: Shr) -> Expr {
		self.transform_assign(&mut ushr.shifted);
		self.transform_assign(&mut ushr.shift_amount);
		ushr.into_variant()
	}

	fn transform_bvsshr(&mut self, mut sshr: SignedShr) -> Expr {
		self.transform_assign(&mut sshr.shifted);
		self.transform_assign(&mut sshr.shift_amount);
		sshr.into_variant()
	}

	//=========================================================================
	// BITVEC EXTEND & EXTRACT
	//=========================================================================

	fn transform_concat(&mut self, mut concat: Concat) -> Expr {
		self.transform_assign(&mut concat.hi);
		self.transform_assign(&mut concat.lo);
		concat.into_variant()
	}

	fn transform_extract(&mut self, mut extract: Extract) -> Expr {
		self.transform_assign(&mut extract.source);
		extract.into_variant()
	}

	fn transform_uextend(&mut self, mut zext: Extend) -> Expr {
		self.transform_assign(&mut zext.source);
		zext.into_variant()
	}

	fn transform_sextend(&mut self, mut sext: SignedExtend) -> Expr {
		self.transform_assign(&mut sext.source);
		sext.into_variant()
	}

	fn transform_read(&mut self, mut read: Read) -> Expr {
		self.transform_assign(&mut read.array);
		self.transform_assign(&mut read.index);
		read.into_variant()
	}

	fn transform_write(&mut self, mut write: Write) -> Expr {
		self.transform_assign(&mut write.array);
		self.transform_assign(&mut write.index);
		self.transform_assign(&mut write.new_val);
		write.into_variant()
	}

	fn transform_boolconst(&mut self, boolconst: BoolConst) -> Expr {
		boolconst.into_variant() // Nothing to do here!
	}

	fn transform_not(&mut self, mut not: Not) -> Expr {
		self.transform_assign(&mut not.inner);
		match *not.inner {
			Expr::Not(notnot) => self.transform(*notnot.inner),
			Expr::BoolConst(constant) => Expr::boolconst(!constant.value),
			_ => not.into_variant()
		}
	}

	fn transform_and(&mut self, mut and: And) -> Expr {
		and.childs_mut().foreach(|child| self.transform_assign(child));

		// Flatten nested ands.
		use std::mem;
		for child in mem::replace(&mut and.formulas, vec![]) {
			match child {
				Expr::And(suband) => {
					and.formulas.extend(suband.into_childs())
				}
				_ => {
					and.formulas.push(child)
				}
			}
		}

		// Deduplicate multiple unnecesary symbolically equal formulas
		// Also explicitely remove needless constant true booleans.
		and.formulas.retain(|f| !f.is_boolconst_with_value(true));
		match and.arity() {
			0 => return Expr::boolconst(true),
			1 => return and.formulas.pop().unwrap(),
			_ => ()
		}

		// Normalize & Deduplicate: `and a a` to `true`
		and.formulas.sort();
		and.formulas.dedup();
		if and.arity() == 1 {
			return Expr::boolconst(true);
		}


		// Case: `and ... false ...` to `false`
		if and.formulas.iter().any(|f| f.is_boolconst_with_value(false)) {
			return Expr::boolconst(false)
		}

		// Case: `and a (not a)` to `false`
		{
			let idns = and.formulas
				.iter()
				.filter(|f| f.kind() != ExprKind::Not);
			let nots = and.formulas
				.iter()
				.filter(|f| f.kind() == ExprKind::Not)
				.collect::<Vec<_>>(); // TODO: Replace collect with proper iteration.
			for (idn, not) in idns.cartesian_product(nots.iter()) {
				if idn.is_bool_contradiction(not) {
					return Expr::boolconst(false)
				}
			}
		}

		and.into_variant()
	}

	fn transform_or(&mut self, mut or: Or) -> Expr {
		debug_assert!(or.arity() >= 2);

		or.childs_mut().foreach(|child| self.transform_assign(child));

		// Flatten nested ors.
		use std::mem;
		for child in mem::replace(&mut or.formulas, vec![]) {
			match child {
				Expr::Or(subor) => {
					or.formulas.extend(subor.into_childs())
				}
				_ => {
					or.formulas.push(child)
				}
			}
		}

		// Deduplicate multiple unnecesary symbolically equal formulas
		// Also explicitely remove needless constant false booleans.
		or.formulas.retain(|f| !f.is_boolconst_with_value(false));
		match or.arity() {
			0 => return Expr::boolconst(false),
			1 => return or.formulas.pop().unwrap(),
			_ => ()
		}

		// Normalize & Deduplicate: `or a a` to `true`
		or.formulas.sort();
		or.formulas.dedup();
		if or.arity() == 1 {
			return Expr::boolconst(true);
		}

		// Case: `or ... true ...` to `true`
		if or.formulas.iter().any(|f| f.is_boolconst_with_value(true)) {
			return Expr::boolconst(true)
		}

		// Case: `or a (not a)` to `true`
		{
			let idns = or.formulas
				.iter()
				.filter(|f| f.kind() != ExprKind::Not);
			let nots = or.formulas
				.iter()
				.filter(|f| f.kind() == ExprKind::Not)
				.collect::<Vec<_>>(); // TODO: Replace collect with proper iteration.
			for (idn, not) in idns.cartesian_product(nots.iter()) {
				if idn.is_bool_contradiction(not) {
					return Expr::boolconst(true)
				}
			}
		}

		or.into_variant()
	}

	fn transform_xor(&mut self, mut xor: Xor) -> Expr {
		self.transform_assign(&mut xor.left);
		self.transform_assign(&mut xor.right);

		// Normalize by sorting (allowed through Commutativity)
		if !(xor.left <= xor.right) {
			::std::mem::swap(&mut xor.left, &mut xor.right);
		}

		// Symbolic tautology `xor a (not a)` to `true`
		if xor.left.is_bool_contradiction(&xor.right) {
			return Expr::boolconst(true)
		}

		// Symbolic contradiction `xor a a` to `false`
		if xor.left == xor.right {
			return Expr::boolconst(false)
		}

		xor.into_variant()
	}

	fn transform_iff(&mut self, mut iff: Iff) -> Expr {
		self.transform_assign(&mut iff.left);
		self.transform_assign(&mut iff.right);
		iff.into_variant()
	}

	fn transform_implies(&mut self, implies: Implies) -> Expr {
		self.transform_or(
			Or{formulas: vec![Expr::not(implies.assumption), *implies.implication]})
	}

	fn transform_param_bool(&mut self, mut parambool: ParamBool) -> Expr {
		self.transform_assign(&mut parambool.bool_var);
		self.transform_assign(&mut parambool.param);
		parambool.into_variant()
	}

	fn transform_equals(&mut self, mut equals: Equals) -> Expr {
		assert!(equals.exprs.len() >= 2,
			"Internal Solver Error: Simplifier::transform_equals: Equality requires at minimum 2 child expressions!");

		// Simplify child expressions.
		equals.childs_mut().foreach(|child| self.transform_assign(child));

		// Normalize child expressions and eleminate duplicates `a = b = a` => `a = b`
		equals.exprs.sort();

		// After deduplication: Find equal childs tautology: `(= a ... a)` to `true`
		equals.exprs.dedup();
		if equals.arity() == 1 {
			return Expr::boolconst(true)
		}

		use itertools::Itertools;

		// Find const constradicting pairs:
		//  - `(= 42 1337)    => false`
		//  - `(= false true) => false`
		// TODO: Optimization by filtering for `BitVecConst` and `BoolConst`.
		{
			let has_const_contradicting_pair = equals.exprs
				.iter()
				.cartesian_product(&equals.exprs)
				.any(|(l,r)| {
					match (l, r) {
						(&Expr::BitVecConst(ref l), &Expr::BitVecConst(ref r)) => l.value != r.value,
						(&Expr::BoolConst(ref l)  , &Expr::BoolConst(ref r)  ) => l.value != r.value,
						_ => false
					}
				}
			);
			if has_const_contradicting_pair {
				return Expr::boolconst(false)
			}
		}

		// Find symbolically contradicting pairs:
		//  - `(= a not(a)) => false`
		//  - `(= x (-x))   => false`
		{
			let has_symbolic_contradicting_pair = equals.exprs
				.iter()
				.cartesian_product(&equals.exprs)
				.any(|(l, r)| {
					match (l, r) {
						(l, r) if l.is_bool_contradiction(r)   => true,
						(l, r) if l.is_bitvec_contradiction(r) => true,
						_ => false
					}
				}
			);
			if has_symbolic_contradicting_pair {
				return Expr::boolconst(false)
			}
		}

		// Finally check for constant tautology evaluation.
		//  - `= 42 42 42 => true`
		// 
		// Note: This should be equal to the above dedup + len check.
		if let Some((head, tail)) = equals.exprs.split_first() {
			if tail.iter().all(|child| head == child) {
				return Expr::boolconst(true)
			}
		}

		equals.into_variant()
	}

	fn transform_ite(&mut self, mut ite: IfThenElse) -> Expr {
		self.transform_assign(&mut ite.cond);

		// Return then case if condition is tautology.
		if ite.cond.is_boolconst_with_value(true) {
			return self.transform(*ite.then_case)
		}

		// Returns else case if condition is contradiction.
		if ite.cond.is_boolconst_with_value(false) {
			return self.transform(*ite.else_case)
		}

		if let &Expr::BoolConst(BoolConst{value}) = &*ite.cond {
			if value {
				return self.transform(*ite.then_case)
			}
			else {
				return self.transform(*ite.else_case)
			}
		}

		{
			let ite_ty = ite.ty();
			if let Expr::Not(Not{inner}) = *ite.cond {

				return self.transform_ite(IfThenElse{
					ty: ite_ty,
					cond: inner,
					then_case: ite.else_case,
					else_case: ite.then_case
				})
			}
		}

		self.transform_assign(&mut ite.then_case);
		self.transform_assign(&mut ite.else_case);

		// Lower to then-case when both branches are equal.
		//  - `ite c a a => a`
		// 
		// Note: This could also be checked before traversing through 
		//       through the branches but was downstreamed in order to
		//       profit from possible simplifications and normalizations.
		if ite.then_case == ite.else_case {
			return ite.then_case.into_variant()
		}

		ite.into_variant()
	}

	fn transform_symbol(&mut self, symbol: Symbol) -> Expr {
		symbol.into_variant()
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

		#[test]
		fn propagate_add() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.bvneg(
					f.bvsum(vec![
						f.bitvec("x", Bits(32)),
						f.bitvec("y", Bits(32)),
						f.bvneg(f.bitvec("z", Bits(32)))
					])
				),
				f.bvsum(vec![
					f.bvneg(f.bitvec("x", Bits(32))),
					f.bvneg(f.bitvec("y", Bits(32))),
					f.bitvec("z", Bits(32))
				])
			);
		}

		#[test]
		fn propagate_mul() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.bvneg(
					f.bvprod(vec![
						f.bitvec("x", Bits(32)),
						f.bitvec("y", Bits(32)),
						f.bitvec("z", Bits(32))
					])
				),
				f.bvprod(vec![
					f.bvneg(f.bitvec("z", Bits(32))), // moved to front because of normalization!
					f.bitvec("x", Bits(32)),
					f.bitvec("y", Bits(32))
				])
			);
		}
	}

	#[test]
	fn integration_neg_sub() {
		let f = NaiveExprFactory::new();
		assert_simplified(
			f.bvneg(
				f.bvsub(
					f.bitvec("x", Bits(32)),
					f.bitvec("y", Bits(32))
				)
			),
			f.bvadd(
				f.bvneg(f.bitvec("x", Bits(32))),
				f.bitvec("y", Bits(32))
			)
		);
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

		#[test]
		fn not_elimination() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.ite(
					f.not(f.boolean("a")),
					f.bitvec("x", Bits(32)),
					f.bitvec("y", Bits(32))
				),
				f.ite(
					f.boolean("a"),
					f.bitvec("y", Bits(32)),
					f.bitvec("x", Bits(32))
				)
			)
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

				f.equality(vec![
					f.boolean("a"),
					f.boolean("b"),
					f.boolean("c"),
					f.boolean("d")
				])
			);
		}
	}

	mod add {
		use super::*;

		#[test]
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

				f.bvsum(vec![
					f.bitvec("x1", Bits(32)),
					f.bitvec("y1", Bits(32)),
					f.bitvec("x2", Bits(32)),
					f.bitvec("y2", Bits(32))
				])
			);
		}
	}

	mod mul {
		use super::*;

		#[test]
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
		fn dissolve_negs() {
			let f = NaiveExprFactory::new();
			// even
			assert_simplified(
				f.bvprod(vec![
					f.bvneg(f.bitvec("x", Bits(32))),
					f.bitvec("y", Bits(32)),
					f.bvneg(f.bitvec("z", Bits(32)))
				]),
				f.bvprod(vec![
					f.bitvec("x", Bits(32)),
					f.bitvec("y", Bits(32)),
					f.bitvec("z", Bits(32))
				])
			);
			// odd
			assert_simplified(
				f.bvprod(vec![
					f.bitvec("x1", Bits(32)),
					f.bvneg(f.bitvec("x2", Bits(32))),
					f.bvneg(f.bitvec("x3", Bits(32))),
					f.bvneg(f.bitvec("x4", Bits(32)))
				]),
				f.bvprod(vec![
					f.bvneg(f.bitvec("x4", Bits(32))), // moved to front due to normalization
					f.bitvec("x1", Bits(32)),
					f.bitvec("x2", Bits(32)),
					f.bitvec("x3", Bits(32))
				])
			)
		}

		#[test]
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

				f.bvprod(vec![
					f.bitvec("x1", Bits(32)),
					f.bitvec("y1", Bits(32)),
					f.bitvec("x2", Bits(32)),
					f.bitvec("y2", Bits(32))
				])
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

	mod sub {
		use super::*;

		#[test]
		fn neutral_element() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.bvsub(
					f.bitvec("x", Bits(32)),
					f.bvconst(Bits(32), 0)
				),
				f.bitvec("x", Bits(32))
			);
		}

		#[test]
		fn null_element() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.bvsub(
					f.bvconst(Bits(32), 0),
					f.bitvec("x", Bits(32))
				),
				f.bvneg(
					f.bitvec("x", Bits(32))
				)
			);
		}

		#[test]
		fn inverse_element() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.bvsub(
					f.bitvec("x", Bits(32)),
					f.bitvec("x", Bits(32))
				),
				f.bvconst(Bits(32), 0)
			);
		}

		#[test]
		fn add_lowering() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.bvsub(
					f.bitvec("x", Bits(32)),
					f.bvneg(
						f.bitvec("y", Bits(32))
					)
				),
				f.bvadd(
					f.bitvec("x", Bits(32)),
					f.bitvec("y", Bits(32))
				)
			);
		}
	}

	mod and {
		use super::*;

		#[test]
		fn const_tautology() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.and(
					f.boolconst(true),
					f.boolconst(true)
				),
				f.boolconst(true)
			);
		}

		#[test]
		fn const_contradiction() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.and(
					f.boolconst(true),
					f.boolconst(false)
				),
				f.boolconst(false)
			);
		}

		#[test]
		fn symbolic_dedup() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.and(
					f.boolean("a"),
					f.boolean("a")
				),
				f.boolconst(true)
			);
		}

		#[test]
		fn symbolic_contradiction() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.and(
					f.boolean("a"),
					f.not(f.boolean("a"))
				),
				f.boolconst(false)
			);
		}

		#[test]
		fn flatten() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.and(
					f.and(
						f.boolean("a"),
						f.boolean("b")
					),
					f.and(
						f.boolean("c"),
						f.boolean("d")
					)
				),
				f.conjunction(vec![
					f.boolean("a"),
					f.boolean("b"),
					f.boolean("c"),
					f.boolean("d")
				])
			);
		}
	}

	mod or {
		use super::*;

		#[test]
		fn const_tautology() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.or(
					f.boolconst(false),
					f.boolconst(true)
				),
				f.boolconst(true)
			);
		}

		#[test]
		fn const_contradiction() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.or(
					f.boolconst(false),
					f.boolconst(false)
				),
				f.boolconst(false)
			);
		}

		#[test]
		fn symbolic_dedup() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.or(
					f.boolean("a"),
					f.boolean("a")
				),
				f.boolconst(true)
			);
		}

		#[test]
		fn symbolic_contradiction() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.or(
					f.boolean("a"),
					f.not(f.boolean("a"))
				),
				f.boolconst(true)
			);
		}

		#[test]
		fn flatten() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.or(
					f.or(
						f.boolean("a"),
						f.boolean("b")
					),
					f.or(
						f.boolean("c"),
						f.boolean("d")
					)
				),
				f.disjunction(vec![
					f.boolean("a"),
					f.boolean("b"),
					f.boolean("c"),
					f.boolean("d")
				])
			);
		}
	}

	mod implies {
		use super::*;

		#[test]
		fn lowering() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.implies(
					f.boolean("a"),
					f.boolean("b")
				),
				f.or(
					f.not(f.boolean("a")),
					f.boolean("b")
				)
			)
		}
	}

	mod xor {
		use super::*;

		#[test]
		fn normalization() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.eq(
					f.xor(
						f.boolean("a"),
						f.boolean("b")
					),
					f.xor(
						f.boolean("b"),
						f.boolean("a")
					)
				),
				f.boolconst(true)
			)
		}

		#[test]
		fn symbolic_tautology() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.xor(
					f.boolean("a"),
					f.not(f.boolean("a"))
				),
				f.boolconst(true)
			)
		}

		#[test]
		fn symbolic_contradiction() {
			let f = NaiveExprFactory::new();
			assert_simplified(
				f.xor(
					f.boolean("a"),
					f.boolean("a")
				),
				f.boolconst(false)
			)
		}
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
