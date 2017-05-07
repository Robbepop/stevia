
use bitvec::BitVec;
use ast::variants::ExprVariant;
use ast::Type;

pub trait ExprFactory {
	//=========================================================================
	// TERM EXPRESSIONS
	//=========================================================================

	fn bitvec_const<T: Into<BitVec>>(&mut self, value: T) -> ExprVariant;

	// ARITHMETHIC EXPRESSIONS
	//-------------------------------------------------------------------------

	fn neg(&mut self, inner: ExprVariant) -> ExprVariant;

	fn add(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn sum(&mut self, terms: Vec<ExprVariant>) -> ExprVariant;

	fn mul(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn prod(&mut self, terms: Vec<ExprVariant>) -> ExprVariant;

	fn sub(&mut self, minuend: ExprVariant, subtrahend: ExprVariant) -> ExprVariant;
	fn udiv(&mut self, dividend: ExprVariant, divisor: ExprVariant) -> ExprVariant;
	fn umod(&mut self, dividend: ExprVariant, divisor: ExprVariant) -> ExprVariant;
	fn sdiv(&mut self, dividend: ExprVariant, divisor: ExprVariant) -> ExprVariant;
	fn smod(&mut self, dividend: ExprVariant, divisor: ExprVariant) -> ExprVariant;
	fn srem(&mut self, dividend: ExprVariant, divisor: ExprVariant) -> ExprVariant;

	// BITWISE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bitnot(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn bitand(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn bitor(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn bitxor(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn bitnand(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn bitnor(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn bitxnor(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;

	// ORDER COMPARE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn ult(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn ule(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn ugt(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn uge(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn slt(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn sle(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn sgt(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn sge(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;

	// SHIFT EXPRESSIONS
	//-------------------------------------------------------------------------

	fn ushl(&mut self, shifted: ExprVariant, shift_amount: ExprVariant) -> ExprVariant;
	fn ushr(&mut self, shifted: ExprVariant, shift_amount: ExprVariant) -> ExprVariant;
	fn sshr(&mut self, shifted: ExprVariant, shift_amount: ExprVariant) -> ExprVariant;

	// EXTEND & TRUNCATE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn concat(&mut self, hi: ExprVariant, lo: ExprVariant) -> ExprVariant;
	fn extract(&mut self, source: ExprVariant, lo_bit: ExprVariant, hi_bit: ExprVariant) -> ExprVariant;
	fn uextend(&mut self, source: ExprVariant, target_width: ExprVariant) -> ExprVariant;
	fn sextend(&mut self, source: ExprVariant, target_width: ExprVariant) -> ExprVariant;

	// ARRAY EXPRESSIONS
	//-------------------------------------------------------------------------

	fn read(&mut self, array: ExprVariant, index: ExprVariant) -> ExprVariant;
	fn write(&mut self, array: ExprVariant, index: ExprVariant, new_val: ExprVariant) -> ExprVariant;

	//=========================================================================
	// FORMULA EXPRESSIONS
	//=========================================================================

	fn bool_const(&mut self, value: bool) -> ExprVariant;

	fn not(&mut self, inner: ExprVariant) -> ExprVariant;

	fn and(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn conjunction(&mut self, formulas: Vec<ExprVariant>) -> ExprVariant;

	fn or(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn disjunction(&mut self, formulas: Vec<ExprVariant>) -> ExprVariant;

	fn xor(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn iff(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn implies(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;

	fn parametric_bool(&mut self, bool_var: ExprVariant, parameter: ExprVariant) -> ExprVariant;

	//=========================================================================
	// GENERIC EXPRESSIONS
	//=========================================================================

	fn eq(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;
	fn ne(&mut self, left: ExprVariant, right: ExprVariant) -> ExprVariant;

	fn equality(&mut self, formulas: Vec<ExprVariant>) -> ExprVariant;

	fn ite(&mut self, cond: ExprVariant, then_case: ExprVariant, else_case: ExprVariant) -> ExprVariant;
	fn symbol(&mut self, name: &str, ty: Type);
}
