
use bitvec::BitVec;
use ast::variants::Expr;
use ast::Type;
use ast::errors::Result;

pub trait ExprFactory {
	//=========================================================================
	// TERM EXPRESSIONS
	//=========================================================================

	fn bvconst<T: Into<BitVec>>(&mut self, value: T) -> Result<Expr>;

	// ARITHMETHIC EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvneg(&mut self, inner: Expr) -> Result<Expr>;

	fn bvadd(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvsum(&mut self, terms: Vec<Expr>) -> Result<Expr>;

	fn bvmul(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvprod(&mut self, terms: Vec<Expr>) -> Result<Expr>;

	fn bvsub(&mut self, minuend: Expr, subtrahend: Expr) -> Result<Expr>;
	fn bvudiv(&mut self, dividend: Expr, divisor: Expr) -> Result<Expr>;
	fn bvumod(&mut self, dividend: Expr, divisor: Expr) -> Result<Expr>;
	fn bvsdiv(&mut self, dividend: Expr, divisor: Expr) -> Result<Expr>;
	fn bvsmod(&mut self, dividend: Expr, divisor: Expr) -> Result<Expr>;
	fn bvsrem(&mut self, dividend: Expr, divisor: Expr) -> Result<Expr>;

	// BITWISE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvnot(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvand(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvor(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvxor(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvnand(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvnor(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvxnor(&mut self, left: Expr, right: Expr) -> Result<Expr>;

	// ORDER COMPARE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvult(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvule(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvugt(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvuge(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvslt(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvsle(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvsgt(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvsge(&mut self, left: Expr, right: Expr) -> Result<Expr>;

	// SHIFT EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvushl(&mut self, shifted: Expr, shift_amount: Expr) -> Result<Expr>;
	fn bvushr(&mut self, shifted: Expr, shift_amount: Expr) -> Result<Expr>;
	fn bvsshr(&mut self, shifted: Expr, shift_amount: Expr) -> Result<Expr>;

	// EXTEND & TRUNCATE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn concat(&mut self, hi: Expr, lo: Expr) -> Result<Expr>;
	fn extract(&mut self, source: Expr, lo_bit: Expr, hi_bit: Expr) -> Result<Expr>;
	fn uextend(&mut self, source: Expr, target_width: Expr) -> Result<Expr>;
	fn sextend(&mut self, source: Expr, target_width: Expr) -> Result<Expr>;

	// ARRAY EXPRESSIONS
	//-------------------------------------------------------------------------

	fn read(&mut self, array: Expr, index: Expr) -> Result<Expr>;
	fn write(&mut self, array: Expr, index: Expr, new_val: Expr) -> Result<Expr>;

	//=========================================================================
	// FORMULA EXPRESSIONS
	//=========================================================================

	fn boolconst(&mut self, value: bool) -> Result<Expr>;

	fn not(&mut self, inner: Expr) -> Result<Expr>;

	fn and(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn conjunction(&mut self, formulas: Vec<Expr>) -> Result<Expr>;

	fn or(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn disjunction(&mut self, formulas: Vec<Expr>) -> Result<Expr>;

	fn xor(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn iff(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn implies(&mut self, left: Expr, right: Expr) -> Result<Expr>;

	fn parambool(&mut self, bool_var: Expr, parameter: Expr) -> Result<Expr>;

	//=========================================================================
	// GENERIC EXPRESSIONS
	//=========================================================================

	fn eq(&mut self, left: Expr, right: Expr) -> Result<Expr>;
	fn ne(&mut self, left: Expr, right: Expr) -> Result<Expr>;

	fn equality(&mut self, formulas: Vec<Expr>) -> Result<Expr>;

	fn ite(&mut self, cond: Expr, then_case: Expr, else_case: Expr) -> Result<Expr>;

	fn symbol<S: AsRef<str>>(&mut self, name: S, ty: Type) -> Result<Expr>;
	fn boolean<S: AsRef<str>>(&mut self, name: S) -> Result<Expr>;
	fn bitvec<S: AsRef<str>>(&mut self, name: S, bitwidth: usize) -> Result<Expr>;
	fn array<S: AsRef<str>>(&mut self, name: S, idx_width: usize, val_width: usize) -> Result<Expr>;
}
