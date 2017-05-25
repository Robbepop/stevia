use std::ops::Range;

use bitvec::BitVec;

use ast::{Bits, Type};
use ast::variants::Expr;
use ast::errors::Result;

pub trait ExprFactoryImpl {
	//=========================================================================
	// TERM EXPRESSIONS
	//=========================================================================

	fn bvconst_impl<T: Into<BitVec>>(&self, bits: Bits, value: T) -> Result<Expr>;

	// ARITHMETHIC EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvneg_impl(&self, inner: Expr) -> Result<Expr>;

	fn bvadd_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvsum_impl(&self, terms: Vec<Expr>) -> Result<Expr>;

	fn bvmul_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvprod_impl(&self, terms: Vec<Expr>) -> Result<Expr>;

	fn bvsub_impl(&self, minuend: Expr, subtrahend: Expr) -> Result<Expr>;
	fn bvudiv_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr>;
	fn bvumod_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr>;
	fn bvsdiv_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr>;
	fn bvsmod_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr>;
	fn bvsrem_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr>;

	// BITWISE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvnot_impl(&self, inner: Expr) -> Result<Expr>;
	fn bvand_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvor_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvxor_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvnand_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvnor_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvxnor_impl(&self, left: Expr, right: Expr) -> Result<Expr>;

	// ORDER COMPARE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvult_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvule_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvugt_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvuge_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvslt_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvsle_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvsgt_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn bvsge_impl(&self, left: Expr, right: Expr) -> Result<Expr>;

	// SHIFT EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvushl_impl(&self, shifted: Expr, shift_amount: Expr) -> Result<Expr>;
	fn bvushr_impl(&self, shifted: Expr, shift_amount: Expr) -> Result<Expr>;
	fn bvsshr_impl(&self, shifted: Expr, shift_amount: Expr) -> Result<Expr>;

	// EXTEND & TRUNCATE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn concat_impl(&self, hi: Expr, lo: Expr) -> Result<Expr>;
	fn extract_impl(&self, source: Expr, range: Range<usize>) -> Result<Expr>;
	fn uextend_impl(&self, source: Expr, extension: usize) -> Result<Expr>;
	fn sextend_impl(&self, source: Expr, extension: usize) -> Result<Expr>;

	// ARRAY EXPRESSIONS
	//-------------------------------------------------------------------------

	fn read_impl(&self, array: Expr, index: Expr) -> Result<Expr>;
	fn write_impl(&self, array: Expr, index: Expr, new_val: Expr) -> Result<Expr>;

	//=========================================================================
	// FORMULA EXPRESSIONS
	//=========================================================================

	fn boolconst_impl(&self, value: bool) -> Result<Expr>;

	fn not_impl(&self, inner: Expr) -> Result<Expr>;

	fn and_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn conjunction_impl(&self, formulas: Vec<Expr>) -> Result<Expr>;

	fn or_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn disjunction_impl(&self, formulas: Vec<Expr>) -> Result<Expr>;

	fn xor_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn iff_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn implies_impl(&self, left: Expr, right: Expr) -> Result<Expr>;

	fn parambool_impl(&self, bool_var: Expr, parameter: Expr) -> Result<Expr>;

	//=========================================================================
	// GENERIC EXPRESSIONS
	//=========================================================================

	fn eq_impl(&self, left: Expr, right: Expr) -> Result<Expr>;
	fn ne_impl(&self, left: Expr, right: Expr) -> Result<Expr>;

	fn equality_impl(&self, formulas: Vec<Expr>) -> Result<Expr>;

	fn ite_impl(&self, cond: Expr, then_case: Expr, else_case: Expr) -> Result<Expr>;

	fn symbol_impl(&self, name: &str, ty: Type) -> Result<Expr>;
	fn boolean_impl(&self, name: &str) -> Result<Expr>;
	fn bitvec_impl(&self, name: &str, bitwidth: Bits) -> Result<Expr>;
	fn array_impl(&self, name: &str, idx_width: Bits, val_width: Bits) -> Result<Expr>;
}

pub trait ExprFactory {
	//=========================================================================
	// TERM EXPRESSIONS
	//=========================================================================

	fn bvconst<BV>(&self, bits: Bits, value: BV) -> Result<Expr>
		where BV: Into<BitVec>;

	// ARITHMETHIC EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvneg<E>(&self, inner: E) -> Result<Expr>
		where E: Into<Result<Expr>>;

	fn bvadd<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvsum<V, T>(&self, terms: V) -> Result<Expr>
		where V: IntoIterator<Item=T>,
		      T: Into<Result<Expr>>;

	fn bvmul<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvprod<V, T>(&self, terms: V) -> Result<Expr>
		where V: IntoIterator<Item=T>,
		      T: Into<Result<Expr>>;

	fn bvsub<L, R>(&self, minuend: L, subtrahend: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvudiv<L, R>(&self, dividend: L, divisor: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvumod<L, R>(&self, dividend: L, divisor: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvsdiv<L, R>(&self, dividend: L, divisor: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvsmod<L, R>(&self, dividend: L, divisor: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvsrem<L, R>(&self, dividend: L, divisor: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;

	// BITWISE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvnot<E>(&self, inner: E) -> Result<Expr>
		where E: Into<Result<Expr>>;
	fn bvand<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvor<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvxor<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvnand<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvnor<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvxnor<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;

	// ORDER COMPARE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvult<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvule<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvugt<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvuge<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvslt<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvsle<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvsgt<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn bvsge<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;

	// SHIFT EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvushl<S, A>(&self, shifted: S, shift_amount: A) -> Result<Expr>
		where S: Into<Result<Expr>>,
		      A: Into<Result<Expr>>;
	fn bvushr<S, A>(&self, shifted: S, shift_amount: A) -> Result<Expr>
		where S: Into<Result<Expr>>,
		      A: Into<Result<Expr>>;
	fn bvsshr<S, A>(&self, shifted: S, shift_amount: A) -> Result<Expr>
		where S: Into<Result<Expr>>,
		      A: Into<Result<Expr>>;

	// EXTEND & TRUNCATE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn concat<H, L>(&self, hi: H, lo: L) -> Result<Expr>
		where H: Into<Result<Expr>>,
		      L: Into<Result<Expr>>;

	fn extract<S>(&self, source: S, range: Range<usize>) -> Result<Expr>
		where S: Into<Result<Expr>>;

	fn uextend<S>(&self, source: S, extension: usize) -> Result<Expr>
		where S: Into<Result<Expr>>;

	fn sextend<S>(&self, source: S, extension: usize) -> Result<Expr>
		where S: Into<Result<Expr>>;

	// ARRAY EXPRESSIONS
	//-------------------------------------------------------------------------

	fn read<A, I>(&self, array: A, index: I) -> Result<Expr>
		where A: Into<Result<Expr>>,
		      I: Into<Result<Expr>>;
	fn write<A, I, V>(&self, array: A, index: I, new_val: V) -> Result<Expr>
		where A: Into<Result<Expr>>,
		      I: Into<Result<Expr>>,
		      V: Into<Result<Expr>>;

	//=========================================================================
	// FORMULA EXPRESSIONS
	//=========================================================================

	fn boolconst(&self, value: bool) -> Result<Expr>;

	fn not<E>(&self, inner: E) -> Result<Expr>
		where E: Into<Result<Expr>>;

	fn and<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;

	fn conjunction<V, T>(&self, formulas: V) -> Result<Expr>
		where V: IntoIterator<Item=T>,
		      T: Into<Result<Expr>>;

	fn or<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;

	fn disjunction<V, T>(&self, formulas: V) -> Result<Expr>
		where V: IntoIterator<Item=T>,
		      T: Into<Result<Expr>>;

	fn xor<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn iff<L, R>(&self, assumption: L, implication: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn implies<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;

	fn parambool<L, R>(&self, bool_var: L, parameter: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;

	//=========================================================================
	// GENERIC EXPRESSIONS
	//=========================================================================

	fn eq<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;
	fn ne<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>;

	fn equality<V, T>(&self, formulas: V) -> Result<Expr>
		where V: IntoIterator<Item=T>,
		      T: Into<Result<Expr>>;

	fn ite<C, T, E>(&self, cond: C, then_case: T, else_case: E) -> Result<Expr>
		where C: Into<Result<Expr>>,
		      T: Into<Result<Expr>>,
		      E: Into<Result<Expr>>;

	fn symbol(&self, name: &str, ty: Type) -> Result<Expr>;
	fn boolean(&self, name: &str) -> Result<Expr>;
	fn bitvec(&self, name: &str, bitwidth: Bits) -> Result<Expr>;
	fn array(&self, name: &str, idx_width: Bits, val_width: Bits) -> Result<Expr>;
}

impl<ConcreteFactory> ExprFactory for ConcreteFactory where ConcreteFactory: ExprFactoryImpl {
	//=========================================================================
	// TERM EXPRESSIONS
	//=========================================================================

	fn bvconst<BV>(&self, bits: Bits, value: BV) -> Result<Expr>
		where BV: Into<BitVec>
	{
		self.bvconst_impl(bits, value)
	}

	// ARITHMETHIC EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvneg<E>(&self, inner: E) -> Result<Expr>
		where E: Into<Result<Expr>>
	{
		self.bvneg_impl(inner.into()?)
	}


	fn bvadd<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvadd_impl(left.into()?, right.into()?)
	}

	fn bvsum<V, T>(&self, terms: V) -> Result<Expr>
		where V: IntoIterator<Item=T>,
		      T: Into<Result<Expr>>
	{
		self.bvsum_impl(terms
			.into_iter()
			.map(|res| res.into())
			.collect::<Result<Vec<Expr>>>()?)
	}

	fn bvmul<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvmul_impl(left.into()?, right.into()?)
	}

	fn bvprod<V, T>(&self, terms: V) -> Result<Expr>
		where V: IntoIterator<Item=T>,
		      T: Into<Result<Expr>>
	{
		self.bvprod_impl(terms
			.into_iter()
			.map(|res| res.into())
			.collect::<Result<Vec<Expr>>>()?)
	}

	fn bvsub<L, R>(&self, minuend: L, subtrahend: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvsub_impl(minuend.into()?, subtrahend.into()?)
	}

	fn bvudiv<L, R>(&self, dividend: L, divisor: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvudiv_impl(dividend.into()?, divisor.into()?)
	}

	fn bvumod<L, R>(&self, dividend: L, divisor: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvumod_impl(dividend.into()?, divisor.into()?)
	}

	fn bvsdiv<L, R>(&self, dividend: L, divisor: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvsdiv_impl(dividend.into()?, divisor.into()?)
	}

	fn bvsmod<L, R>(&self, dividend: L, divisor: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvsmod_impl(dividend.into()?, divisor.into()?)
	}

	fn bvsrem<L, R>(&self, dividend: L, divisor: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvsrem_impl(dividend.into()?, divisor.into()?)
	}


	// BITWISE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvnot<E>(&self, inner: E) -> Result<Expr>
		where E: Into<Result<Expr>>
	{
		self.bvnot_impl(inner.into()?)
	}

	fn bvand<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvand_impl(left.into()?, right.into()?)
	}

	fn bvor<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvor_impl(left.into()?, right.into()?)
	}

	fn bvxor<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvxor_impl(left.into()?, right.into()?)
	}

	fn bvnand<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvnand_impl(left.into()?, right.into()?)
	}

	fn bvnor<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvnor_impl(left.into()?, right.into()?)
	}

	fn bvxnor<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvxnor_impl(left.into()?, right.into()?)
	}


	// ORDER COMPARE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvult<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvult_impl(left.into()?, right.into()?)
	}

	fn bvule<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvule_impl(left.into()?, right.into()?)
	}

	fn bvugt<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvugt_impl(left.into()?, right.into()?)
	}

	fn bvuge<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvuge_impl(left.into()?, right.into()?)
	}

	fn bvslt<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvslt_impl(left.into()?, right.into()?)
	}

	fn bvsle<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvsle_impl(left.into()?, right.into()?)
	}

	fn bvsgt<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvsgt_impl(left.into()?, right.into()?)
	}

	fn bvsge<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.bvsge_impl(left.into()?, right.into()?)
	}


	// SHIFT EXPRESSIONS
	//-------------------------------------------------------------------------

	fn bvushl<S, A>(&self, shifted: S, shift_amount: A) -> Result<Expr>
		where S: Into<Result<Expr>>,
		      A: Into<Result<Expr>>
	{
		self.bvushl_impl(shifted.into()?, shift_amount.into()?)
	}

	fn bvushr<S, A>(&self, shifted: S, shift_amount: A) -> Result<Expr>
		where S: Into<Result<Expr>>,
		      A: Into<Result<Expr>>
	{
		self.bvushr_impl(shifted.into()?, shift_amount.into()?)
	}

	fn bvsshr<S, A>(&self, shifted: S, shift_amount: A) -> Result<Expr>
		where S: Into<Result<Expr>>,
		      A: Into<Result<Expr>>
	{
		self.bvsshr_impl(shifted.into()?, shift_amount.into()?)
	}


	// EXTEND & TRUNCATE EXPRESSIONS
	//-------------------------------------------------------------------------

	fn concat<H, L>(&self, hi: H, lo: L) -> Result<Expr>
		where H: Into<Result<Expr>>,
		      L: Into<Result<Expr>>
	{
		self.concat_impl(hi.into()?, lo.into()?)
	}

	fn extract<S>(&self, source: S, range: Range<usize>) -> Result<Expr>
		where S: Into<Result<Expr>>
	{
		self.extract_impl(source.into()?, range)
	}

	fn uextend<S>(&self, source: S, target_width: usize) -> Result<Expr>
		where S: Into<Result<Expr>>
	{
		self.uextend_impl(source.into()?, target_width)
	}

	fn sextend<S>(&self, source: S, target_width: usize) -> Result<Expr>
		where S: Into<Result<Expr>>
	{
		self.sextend_impl(source.into()?, target_width)
	}


	// ARRAY EXPRESSIONS
	//-------------------------------------------------------------------------

	fn read<A, I>(&self, array: A, index: I) -> Result<Expr>
		where A: Into<Result<Expr>>,
		      I: Into<Result<Expr>>
	{
		self.read_impl(array.into()?, index.into()?)
	}

	fn write<A, I, V>(&self, array: A, index: I, new_val: V) -> Result<Expr>
		where A: Into<Result<Expr>>,
		      I: Into<Result<Expr>>,
		      V: Into<Result<Expr>>
	{
		self.write_impl(array.into()?, index.into()?, new_val.into()?)
	}

	//=========================================================================
	// FORMULA EXPRESSIONS
	//=========================================================================

	fn boolconst(&self, value: bool) -> Result<Expr>
	{
		self.boolconst_impl(value)
	}

	fn not<E>(&self, inner: E) -> Result<Expr>
		where E: Into<Result<Expr>>
	{
		self.not_impl(inner.into()?)
	}

	fn and<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.and_impl(left.into()?, right.into()?)
	}

	fn conjunction<V, T>(&self, formulas: V) -> Result<Expr>
		where V: IntoIterator<Item=T>,
		      T: Into<Result<Expr>>
	{
		self.conjunction_impl(formulas
			.into_iter()
			.map(|res| res.into())
			.collect::<Result<Vec<Expr>>>()?)
	}

	fn or<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.or_impl(left.into()?, right.into()?)
	}

	fn disjunction<V, T>(&self, formulas: V) -> Result<Expr>
		where V: IntoIterator<Item=T>,
		      T: Into<Result<Expr>>
	{
		self.disjunction_impl(formulas
			.into_iter()
			.map(|res| res.into())
			.collect::<Result<Vec<Expr>>>()?)
	}

	fn xor<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.xor_impl(left.into()?, right.into()?)
	}

	fn iff<L, R>(&self, assumption: L, implication: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.iff_impl(assumption.into()?, implication.into()?)
	}

	fn implies<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.implies_impl(left.into()?, right.into()?)
	}

	fn parambool<L, R>(&self, bool_var: L, parameter: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.parambool_impl(bool_var.into()?, parameter.into()?)
	}

	//=========================================================================
	// GENERIC EXPRESSIONS
	//=========================================================================

	fn eq<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.eq_impl(left.into()?, right.into()?)
	}

	fn ne<L, R>(&self, left: L, right: R) -> Result<Expr>
		where L: Into<Result<Expr>>,
		      R: Into<Result<Expr>>
	{
		self.ne_impl(left.into()?, right.into()?)
	}

	fn equality<V, T>(&self, formulas: V) -> Result<Expr>
		where V: IntoIterator<Item=T>,
		      T: Into<Result<Expr>>
	{
		self.equality_impl(formulas
			.into_iter()
			.map(|res| res.into())
			.collect::<Result<Vec<Expr>>>()?)
	}

	fn ite<C, T, E>(&self, cond: C, then_case: T, else_case: E) -> Result<Expr>
		where C: Into<Result<Expr>>,
		      T: Into<Result<Expr>>,
		      E: Into<Result<Expr>>
	{
		self.ite_impl(cond.into()?, then_case.into()?, else_case.into()?)
	}

	fn symbol(&self, name: &str, ty: Type) -> Result<Expr>
	{
		self.symbol_impl(name, ty)
	}

	fn boolean(&self, name: &str) -> Result<Expr>
	{
		self.boolean_impl(name)
	}

	fn bitvec(&self, name: &str, bitwidth: Bits) -> Result<Expr>
	{
		self.bitvec_impl(name, bitwidth)
	}

	fn array(&self, name: &str, idx_width: Bits, val_width: Bits) -> Result<Expr>
	{
		self.array_impl(name, idx_width, val_width)
	}
}
