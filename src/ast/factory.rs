
use bitvec::BitVec;
use ast::variants::Expr;
use ast::Type;

pub trait ExprFactory {
	//=========================================================================
	// TERM EXPRESSIONS
	//=========================================================================

	fn bvconst<T: Into<BitVec>>(&mut self, value: T) -> Expr;

	// ARITHMETHIC EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvneg(&mut self, inner: Expr) -> Expr;

	fn bvadd(&mut self, left: Expr, right: Expr) -> Expr;
	fn bvsum(&mut self, terms: Vec<Expr>) -> Expr;

	fn bvmul(&mut self, left: Expr, right: Expr) -> Expr;
	fn bvprod(&mut self, terms: Vec<Expr>) -> Expr;

	fn bvsub(&mut self, minuend: Expr, subtrahend: Expr) -> Expr;
	fn bvudiv(&mut self, dividend: Expr, divisor: Expr) -> Expr;
	fn bvumod(&mut self, dividend: Expr, divisor: Expr) -> Expr;
	fn bvsdiv(&mut self, dividend: Expr, divisor: Expr) -> Expr;
	fn bvsmod(&mut self, dividend: Expr, divisor: Expr) -> Expr;
	fn bvsrem(&mut self, dividend: Expr, divisor: Expr) -> Expr;

	// BITWISE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvnot(&mut self, left: Expr, right: Expr) -> Expr;
	fn bvand(&mut self, left: Expr, right: Expr) -> Expr;
	fn bvor(&mut self, left: Expr, right: Expr) -> Expr;
	fn bvxor(&mut self, left: Expr, right: Expr) -> Expr;
	fn bvnand(&mut self, left: Expr, right: Expr) -> Expr;
	fn bvnor(&mut self, left: Expr, right: Expr) -> Expr;
	fn bvxnor(&mut self, left: Expr, right: Expr) -> Expr;

	// ORDER COMPARE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvult(&mut self, left: Expr, right: Expr) -> Expr;
	fn bvule(&mut self, left: Expr, right: Expr) -> Expr;
	fn bvugt(&mut self, left: Expr, right: Expr) -> Expr;
	fn bvuge(&mut self, left: Expr, right: Expr) -> Expr;
	fn bvslt(&mut self, left: Expr, right: Expr) -> Expr;
	fn bvsle(&mut self, left: Expr, right: Expr) -> Expr;
	fn bvsgt(&mut self, left: Expr, right: Expr) -> Expr;
	fn bvsge(&mut self, left: Expr, right: Expr) -> Expr;

	// SHIFT EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvushl(&mut self, shifted: Expr, shift_amount: Expr) -> Expr;
	fn bvushr(&mut self, shifted: Expr, shift_amount: Expr) -> Expr;
	fn bvsshr(&mut self, shifted: Expr, shift_amount: Expr) -> Expr;

	// EXTEND & TRUNCATE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn concat(&mut self, hi: Expr, lo: Expr) -> Expr;
	fn extract(&mut self, source: Expr, lo_bit: Expr, hi_bit: Expr) -> Expr;
	fn uextend(&mut self, source: Expr, target_width: Expr) -> Expr;
	fn sextend(&mut self, source: Expr, target_width: Expr) -> Expr;

	// ARRAY EXPRESSIONS
	//-------------------------------------------------------------------------

	fn read(&mut self, array: Expr, index: Expr) -> Expr;
	fn write(&mut self, array: Expr, index: Expr, new_val: Expr) -> Expr;

	//=========================================================================
	// FORMULA EXPRESSIONS
	//=========================================================================

	fn boolconst(&mut self, value: bool) -> Expr;

	fn not(&mut self, inner: Expr) -> Expr;

	fn and(&mut self, left: Expr, right: Expr) -> Expr;
	fn conjunction(&mut self, formulas: Vec<Expr>) -> Expr;

	fn or(&mut self, left: Expr, right: Expr) -> Expr;
	fn disjunction(&mut self, formulas: Vec<Expr>) -> Expr;

	fn xor(&mut self, left: Expr, right: Expr) -> Expr;
	fn iff(&mut self, left: Expr, right: Expr) -> Expr;
	fn implies(&mut self, left: Expr, right: Expr) -> Expr;

	fn parambool(&mut self, bool_var: Expr, parameter: Expr) -> Expr;

	//=========================================================================
	// GENERIC EXPRESSIONS
	//=========================================================================

	fn eq(&mut self, left: Expr, right: Expr) -> Expr;
	fn ne(&mut self, left: Expr, right: Expr) -> Expr;

	fn equality(&mut self, formulas: Vec<Expr>) -> Expr;

	fn ite(&mut self, cond: Expr, then_case: Expr, else_case: Expr) -> Expr;

	fn symbol<S: AsRef<str>>(&mut self, name: S, ty: Type);
	fn boolean<S: AsRef<str>>(&mut self, name: S);
	fn bitvec<S: AsRef<str>>(&mut self, name: S, bitwidth: usize);
	fn array<S: AsRef<str>>(&mut self, name: S, idx_width: usize, val_width: usize);
}
