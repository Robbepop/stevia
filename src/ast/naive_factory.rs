use std::ops::Range;
use std::collections::HashMap;
use std::cell::RefCell;

use string_interner::StringInterner;

use apint::ApInt;

use ast::expr;
use ast::prelude::*;
use ast::{AstError, ErrorKind, CommonBitVec};
use ast::factory::ExprFactoryImpl;

#[derive(Debug, Clone)]
pub struct NaiveExprFactory {
	/// Used to intern and cache symbol names.
	symbols: RefCell<StringInterner<SymName>>,
	/// Stores a type for every symbol to enforce symbol type-safety.
	types: RefCell<HashMap<SymName, Type>>
}

impl NaiveExprFactory {
	pub fn new() -> NaiveExprFactory {
		NaiveExprFactory{
			symbols: RefCell::new(StringInterner::new()),
			types  : RefCell::new(HashMap::new())
		}
	}
}

impl Default for NaiveExprFactory {
    fn default() -> Self {
        Self::new()
    }
}

impl ExprFactoryImpl for NaiveExprFactory {
	fn bvconst_impl<T: Into<ApInt>>(&self, bits: Bits, value: T) -> Result<Expr> {
		Ok(Expr::BitVecConst(expr::BitVecConst{
			value: value.into(),
			ty   : bits.into()
		}))
	}

	fn bvneg_impl(&self, inner: Expr) -> Result<Expr> {
		inner.ty().kind().expect(TypeKind::BitVec)?;
		Ok(Expr::bvneg(Box::new(inner)))
	}

	fn bvadd_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		self.bvsum_impl(vec![left, right])
	}

	fn bvsum_impl(&self, terms: Vec<Expr>) -> Result<Expr> {
		let common_ty = terms.iter().map(|e| e.ty()).common_bitvec()?;
		Ok(Expr::bvsum(common_ty, terms))
	}

	fn bvmul_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::Mul(expr::Mul{
			factors: vec![left, right],
			ty     : Type::BitVec(common)
		}))
	}

	fn bvprod_impl(&self, terms: Vec<Expr>) -> Result<Expr> {
		Ok(Expr::Mul(expr::Mul{
			ty     : terms.iter().map(|e| e.ty()).common_bitvec()?,
			factors: terms
		}))
	}

	fn bvsub_impl(&self, minuend: Expr, subtrahend: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(minuend.ty(), subtrahend.ty())?;
		Ok(Expr::Sub(expr::Sub{
			minuend   : Box::new(minuend),
			subtrahend: Box::new(subtrahend),
			ty        : Type::BitVec(common)
		}))
	}

	fn bvudiv_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(dividend.ty(), divisor.ty())?;
		Ok(Expr::Div(expr::Div{
			dividend: Box::new(dividend),
			divisor : Box::new(divisor),
			ty      : Type::BitVec(common)
		}))
	}

	fn bvumod_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(dividend.ty(), divisor.ty())?;
		Ok(Expr::Mod(expr::Mod{
			dividend: Box::new(dividend),
			divisor : Box::new(divisor),
			ty      : Type::BitVec(common)
		}))
	}

	fn bvsdiv_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(dividend.ty(), divisor.ty())?;
		Ok(Expr::SignedDiv(expr::SignedDiv{
			dividend: Box::new(dividend),
			divisor : Box::new(divisor),
			ty      : Type::BitVec(common)
		}))
	}

	fn bvsmod_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(dividend.ty(), divisor.ty())?;
		Ok(Expr::SignedMod(expr::SignedMod{
			dividend: Box::new(dividend),
			divisor : Box::new(divisor),
			ty      : Type::BitVec(common)
		}))
	}

	fn bvsrem_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(dividend.ty(), divisor.ty())?;
		Ok(Expr::SignedRem(expr::SignedRem{
			dividend: Box::new(dividend),
			divisor : Box::new(divisor),
			ty      : Type::BitVec(common)
		}))
	}

	fn bvnot_impl(&self, inner: Expr) -> Result<Expr> {
		let bits = inner.ty().bitwidth()?;
		Ok(Expr::BitNot(expr::BitNot{
			inner: Box::new(inner),
			ty   : Type::BitVec(bits)
		}))
	}

	fn bvand_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::BitAnd(expr::BitAnd{
			left : Box::new(left),
			right: Box::new(right),
			ty   : Type::BitVec(common)
		}))
	}

	fn bvor_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::BitOr(expr::BitOr{
			left : Box::new(left),
			right: Box::new(right),
			ty   : Type::BitVec(common)
		}))
	}

	fn bvxor_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::BitXor(expr::BitXor{
			left : Box::new(left),
			right: Box::new(right),
			ty   : Type::BitVec(common)
		}))
	}

	fn bvnand_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::BitNand(expr::BitNand{
			left : Box::new(left),
			right: Box::new(right),
			ty   : Type::BitVec(common)
		}))
	}

	fn bvnor_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::BitNor(expr::BitNor{
			left : Box::new(left),
			right: Box::new(right),
			ty   : Type::BitVec(common)
		}))
	}

	fn bvxnor_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::BitXnor(expr::BitXnor{
			left : Box::new(left),
			right: Box::new(right),
			ty   : Type::BitVec(common)
		}))
	}

	fn bvult_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::Lt(expr::Lt{
			left : Box::new(left),
			right: Box::new(right),
			inner_ty: Type::BitVec(common)
		}))
	}

	fn bvule_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::Le(expr::Le{
			left : Box::new(left),
			right: Box::new(right),
			inner_ty: Type::BitVec(common)
		}))
	}

	fn bvugt_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::Gt(expr::Gt{
			left : Box::new(left),
			right: Box::new(right),
			inner_ty: Type::BitVec(common)
		}))
	}

	fn bvuge_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::Ge(expr::Ge{
			left : Box::new(left),
			right: Box::new(right),
			inner_ty: Type::BitVec(common)
		}))
	}

	fn bvslt_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::SignedLt(expr::SignedLt{
			left : Box::new(left),
			right: Box::new(right),
			inner_ty: Type::BitVec(common)
		}))
	}

	fn bvsle_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::SignedLe(expr::SignedLe{
			left : Box::new(left),
			right: Box::new(right),
			inner_ty: Type::BitVec(common)
		}))
	}

	fn bvsgt_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::SignedGt(expr::SignedGt{
			left : Box::new(left),
			right: Box::new(right),
			inner_ty: Type::BitVec(common)
		}))
	}

	fn bvsge_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::SignedGe(expr::SignedGe{
			left : Box::new(left),
			right: Box::new(right),
			inner_ty: Type::BitVec(common)
		}))
	}

	fn bvushl_impl(&self, shifted: Expr, shift_amount: Expr) -> Result<Expr> {
		shifted.ty().kind().expect(TypeKind::BitVec)?;
		shift_amount.ty().kind().expect(TypeKind::BitVec)?;
		Ok(Expr::Shl(expr::Shl{
			ty          : shifted.ty(),
			shifted     : Box::new(shifted),
			shift_amount: Box::new(shift_amount)
		}))
	}

	fn bvushr_impl(&self, shifted: Expr, shift_amount: Expr) -> Result<Expr> {
		shifted.ty().kind().expect(TypeKind::BitVec)?;
		shift_amount.ty().kind().expect(TypeKind::BitVec)?;
		Ok(Expr::Shr(expr::Shr{
			ty          : shifted.ty(),
			shifted     : Box::new(shifted),
			shift_amount: Box::new(shift_amount)
		}))
	}

	fn bvsshr_impl(&self, shifted: Expr, shift_amount: Expr) -> Result<Expr> {
		shifted.ty().kind().expect(TypeKind::BitVec)?;
		shift_amount.ty().kind().expect(TypeKind::BitVec)?;
		Ok(Expr::SignedShr(expr::SignedShr{
			ty          : shifted.ty(),
			shifted     : Box::new(shifted),
			shift_amount: Box::new(shift_amount)
		}))
	}

	fn concat_impl(&self, hi: Expr, lo: Expr) -> Result<Expr> {
		hi.ty().kind().expect(TypeKind::BitVec)?;
		lo.ty().kind().expect(TypeKind::BitVec)?;
		Ok(Expr::concat(Box::new(hi), Box::new(lo)))
	}

	fn extract_impl(&self, source: Expr, range: Range<usize>) -> Result<Expr> {
		source.ty().kind().expect(TypeKind::BitVec)?;
		Ok(Expr::Extract(expr::Extract{
			source: Box::new(source),
			ty    : Type::BitVec(range.end - range.start),
			range : range,
		}))
	}

	fn uextend_impl(&self, source: Expr, extension: usize) -> Result<Expr> {
		source.ty().kind().expect(TypeKind::BitVec)?;
		Ok(Expr::uextend(Box::new(source), extension))
	}

	fn sextend_impl(&self, source: Expr, extension: usize) -> Result<Expr> {
		source.ty().kind().expect(TypeKind::BitVec)?;
		Ok(Expr::sextend(Box::new(source), extension))
	}

	fn read_impl(&self, array: Expr, index: Expr) -> Result<Expr> {
		if let Type::Array(idx_width, val_width) = array.ty() {
			index.ty().expect(Type::BitVec(idx_width))?;
			Ok(Expr::read(
				Type::Array(idx_width, val_width),
				Box::new(array),
				Box::new(index)
			))
		}
		else {
			Err(AstError(ErrorKind::ExpectedArrayTypeKind{found_kind: array.ty().kind()}))
		}
	}

	fn write_impl(&self, array: Expr, index: Expr, new_val: Expr) -> Result<Expr> {
		if let Type::Array(idx_width, val_width) = array.ty() {
			index.ty().expect(Type::BitVec(idx_width))?;
			new_val.ty().expect(Type::BitVec(val_width))?;
			Ok(Expr::write(
				Type::Array(idx_width, val_width),
				Box::new(array),
				Box::new(index),
				Box::new(new_val)
			))
		}
		else {
			Err(AstError(ErrorKind::ExpectedArrayTypeKind{found_kind: array.ty().kind()}))
		}
	}

	fn boolconst_impl(&self, value: bool) -> Result<Expr> {
		Ok(Expr::boolconst(value))
	}

	fn not_impl(&self, inner: Expr) -> Result<Expr> {
		inner.ty().expect(Type::Boolean)?;
		Ok(Expr::not(Box::new(inner)))
	}

	fn and_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		self.conjunction_impl(vec![left, right])
	}

	fn conjunction_impl(&self, formulas: Vec<Expr>) -> Result<Expr> {
		for formula in &formulas {
			formula.ty().expect(Type::Boolean)?;
		}
		Ok(Expr::conjunction(formulas))
	}

	fn or_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		self.disjunction_impl(vec![left, right])
	}

	fn disjunction_impl(&self, formulas: Vec<Expr>) -> Result<Expr> {
		for formula in &formulas {
			formula.ty().expect(Type::Boolean)?;
		}
		Ok(Expr::disjunction(formulas))
	}

	fn xor_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().expect(Type::Boolean)?;
		right.ty().expect(Type::Boolean)?;
		Ok(Expr::xor(Box::new(left), Box::new(right)))
	}

	fn iff_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().expect(Type::Boolean)?;
		right.ty().expect(Type::Boolean)?;
		Ok(Expr::iff(Box::new(left), Box::new(right)))
	}

	fn implies_impl(&self, assumption: Expr, implication: Expr) -> Result<Expr> {
		assumption.ty().expect(Type::Boolean)?;
		implication.ty().expect(Type::Boolean)?;
		Ok(Expr::implies(Box::new(assumption), Box::new(implication)))
	}

	fn parambool_impl(&self, bool_var: Expr, parameter: Expr) -> Result<Expr> {
		bool_var.ty().expect(Type::Boolean)?;
		parameter.ty().expect(Type::Boolean)?;
		Ok(Expr::parambool(Box::new(bool_var), Box::new(parameter)))
	}

	fn eq_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		self.equality_impl(vec![left, right])
	}

	fn ne_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		self.not(self.eq(left, right))
	}

	fn equality_impl(&self, exprs: Vec<Expr>) -> Result<Expr> {
		use ast::CommonType;
		let inner_ty = exprs.iter().map(|e| e.ty()).common_type()?;
		Ok(Expr::equality(inner_ty, exprs))
	}

	/// Creates an if-then-else expression.
	/// 
	/// Checks if cond (condition) is of type boolean and also checks if
	/// then-case and else-case return a common type.
	fn ite_impl(&self, cond: Expr, then_case: Expr, else_case: Expr) -> Result<Expr> {
		cond.ty().expect(Type::Boolean)?;
		let common_type = Type::common_of(then_case.ty(), else_case.ty())?;
		Ok(Expr::IfThenElse(expr::IfThenElse{
			cond     : Box::new(cond),
			then_case: Box::new(then_case),
			else_case: Box::new(else_case),
			ty       : common_type
		}))
	}

	fn symbol_impl(&self, name: &str, ty: Type) -> Result<Expr> {
		let sym = self.symbols.borrow_mut().get_or_intern(name);
		if let Some(assoc_ty) = self.types.borrow_mut().insert(sym, ty) {
			if ty != assoc_ty {
				return Type::common_of(ty, assoc_ty)
					.map(|_| Expr::Symbol(expr::Symbol{name: sym, ty}))
			}
		}
		Ok(Expr::symbol(sym, ty))
	}

	fn boolean_impl(&self, name: &str) -> Result<Expr> {
		self.symbol(name, Type::Boolean)
	}

	fn bitvec_impl(&self, name: &str, bits: Bits) -> Result<Expr> {
		self.symbol(name, Type::from(bits))
	}

	fn array_impl(&self, name: &str, idx_width: Bits, val_width: Bits) -> Result<Expr> {
		self.symbol(name, Type::from((idx_width, val_width)))
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn bvsum() {
		let f = NaiveExprFactory::new();
		{
			let valid = f.bvsum(vec![
				f.bitvec("x", Bits(32)),
				f.bvconst(Bits(32), 42)
			]);
			assert!(valid.is_ok());
		}
		{
			let invalid = f.bvsum(vec![
				f.bitvec("x", Bits(32)),
				f.boolconst(true)
			]);
			assert!(invalid.is_err());
		}
	}

	#[test]
	fn bvprod() {
		let f = NaiveExprFactory::new();
		{
			let valid = f.bvprod(vec![
				f.bitvec("x", Bits(32)),
				f.bvconst(Bits(32), 42)
			]);
			assert!(valid.is_ok());
		}
		{
			let invalid = f.bvprod(vec![
				f.bitvec("x", Bits(32)),
				f.boolconst(true)
			]);
			assert!(invalid.is_err());
		}
	}

	#[test]
	fn conjunction() {
		let f = NaiveExprFactory::new();
		{
			let valid = f.conjunction(vec![
				f.boolean("a"),
				f.boolconst(true)
			]);
			assert!(valid.is_ok());
		}
		{
			let invalid = f.conjunction(vec![
				f.boolean("a"),
				f.bvconst(Bits(32), 1337)
			]);
			assert!(invalid.is_err());
		}
	}

	#[test]
	fn disjunction() {
		let f = NaiveExprFactory::new();
		{
			let valid = f.disjunction(vec![
				f.boolean("a"),
				f.boolconst(true)
			]);
			assert!(valid.is_ok());
		}
		{
			let invalid = f.disjunction(vec![
				f.boolean("a"),
				f.bvconst(Bits(32), 1337)
			]);
			assert!(invalid.is_err());
		}
	}

	#[test]
	fn equality() {
		let f = NaiveExprFactory::new();
		{
			let valid = f.equality(vec![
				f.boolean("a"),
				f.boolconst(true)
			]);
			assert!(valid.is_ok());
		}
		{
			let invalid = f.equality(vec![
				f.boolean("a"),
				f.bvconst(Bits(32), 1337)
			]);
			assert!(invalid.is_err());
		}
		{
			let valid = f.equality(vec![
				f.bitvec("x", Bits(32)),
				f.bvconst(Bits(32), 42)
			]);
			assert!(valid.is_ok());
		}
		{
			let invalid = f.equality(vec![
				f.bitvec("x", Bits(32)),
				f.boolconst(true)
			]);
			assert!(invalid.is_err());
		}
	}
}
