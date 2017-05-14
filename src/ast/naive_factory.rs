
use bitvec::BitVec;

use ast::expr;
use ast::prelude::*;
use ast::{AstError, ErrorKind};
use ast::factory::ExprFactoryImpl;

pub struct NaiveExprFactory {
	// TODO: ctx: Context
}

impl NaiveExprFactory {
	pub fn new() -> NaiveExprFactory {
		NaiveExprFactory{}
	}
}

impl ExprFactoryImpl for NaiveExprFactory {
	fn bvconst_impl<T: Into<BitVec>>(&self, bits: Bits, value: T) -> Result<Expr> {
		Ok(Expr::BitVecConst(expr::BitVecConst{
			value: value.into(),
			ty   : bits.into()
		}))
	}

	fn bvneg_impl(&self, inner: Expr) -> Result<Expr> {
		let bits = inner.ty().bitwidth()?;
		Ok(Expr::Neg(expr::Neg{
			inner: Box::new(inner),
			ty   : Type::BitVec(bits)
		}))
	}

	fn bvadd_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::Add(expr::Add{
			terms: vec![left, right],
			ty   : Type::BitVec(common)
		}))
	}

	// fn bvsum_impl(&self, terms: Vec<Expr>) -> Result<Expr> {
	// 	Ok(Expr::BoolConst(BoolConst{value: true}))
	// }

	fn bvmul_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::Mul(expr::Mul{
			factors: vec![left, right],
			ty     : Type::BitVec(common)
		}))
	}

	// fn bvprod_impl(&self, terms: Vec<Expr>) -> Result<Expr> {
	// 	Ok(Expr::BoolConst(BoolConst{value: true}))
	// }

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
			ty   : Type::BitVec(common)
		}))
	}

	fn bvule_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::Le(expr::Le{
			left : Box::new(left),
			right: Box::new(right),
			ty   : Type::BitVec(common)
		}))
	}

	fn bvugt_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::Gt(expr::Gt{
			left : Box::new(left),
			right: Box::new(right),
			ty   : Type::BitVec(common)
		}))
	}

	fn bvuge_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::Ge(expr::Ge{
			left : Box::new(left),
			right: Box::new(right),
			ty   : Type::BitVec(common)
		}))
	}

	fn bvslt_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::SignedLt(expr::SignedLt{
			left : Box::new(left),
			right: Box::new(right),
			ty   : Type::BitVec(common)
		}))
	}

	fn bvsle_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::SignedLe(expr::SignedLe{
			left : Box::new(left),
			right: Box::new(right),
			ty   : Type::BitVec(common)
		}))
	}

	fn bvsgt_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::SignedGt(expr::SignedGt{
			left : Box::new(left),
			right: Box::new(right),
			ty   : Type::BitVec(common)
		}))
	}

	fn bvsge_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common = Type::common_bitwidth(left.ty(), right.ty())?;
		Ok(Expr::SignedGe(expr::SignedGe{
			left : Box::new(left),
			right: Box::new(right),
			ty   : Type::BitVec(common)
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
		let hi_bits = Type::bitwidth(hi.ty())?;
		let lo_bits = Type::bitwidth(hi.ty())?;
		Ok(Expr::Concat(expr::Concat{
			hi: Box::new(hi),
			lo: Box::new(lo),
			ty: Type::BitVec(hi_bits + lo_bits)
		}))
	}

	fn extract_impl(&self, source: Expr, lo_bit: Expr, hi_bit: Expr) -> Result<Expr> {
		source.ty().kind().expect(TypeKind::BitVec)?;
		lo_bit.ty().kind().expect(TypeKind::BitVec)?;
		hi_bit.ty().kind().expect(TypeKind::BitVec)?;
		Ok(Expr::Extract(expr::Extract{
			source: Box::new(source),
			hi_bit: Box::new(hi_bit),
			lo_bit: Box::new(lo_bit),
			ty    : panic!("FIXME/TODO - Error at NaiveExprFactory::extract_impl: \\
			                Cannot infer correct type since `hi_bit - lo_bit` is not necessarily evaluatable!")
		}))
	}

	fn uextend_impl(&self, source: Expr, extension: Expr) -> Result<Expr> {
		source.ty().kind().expect(TypeKind::BitVec)?;
		extension.ty().kind().expect(TypeKind::BitVec)?;
		Ok(Expr::Extend(expr::Extend{
			source   : Box::new(source),
			extension: Box::new(extension),
			ty       : panic!("FIXME/TODO - Error at NaiveExprFactory::uextend_impl: \\
			                   Cannot infer correct type since `extension` is not necessarily evaluatable!")
		}))
	}

	fn sextend_impl(&self, source: Expr, extension: Expr) -> Result<Expr> {
		source.ty().kind().expect(TypeKind::BitVec)?;
		extension.ty().kind().expect(TypeKind::BitVec)?;
		Ok(Expr::SignedExtend(expr::SignedExtend{
			source   : Box::new(source),
			extension: Box::new(extension),
			ty       : panic!("FIXME/TODO - Error at NaiveExprFactory::sextend_impl: \\
			                   Cannot infer correct type since `extension` is not necessarily evaluatable!")
		}))
	}

	fn read_impl(&self, array: Expr, index: Expr) -> Result<Expr> {
		if let Type::Array(idx_width, val_width) = array.ty() {
			index.ty().expect(Type::BitVec(idx_width))?;
			Ok(Expr::Read(expr::Read{
				array: Box::new(array),
				index: Box::new(index),
				ty   : Type::Array(idx_width, val_width)
			}))
		}
		else {
			Err(AstError(ErrorKind::ExpectedArrayTypeKind{found_kind: array.ty().kind()}))
		}
	}

	fn write_impl(&self, array: Expr, index: Expr, new_val: Expr) -> Result<Expr> {
		if let Type::Array(idx_width, val_width) = array.ty() {
			index.ty().expect(Type::BitVec(idx_width))?;
			new_val.ty().expect(Type::BitVec(val_width))?;
			Ok(Expr::Write(expr::Write{
				array  : Box::new(array),
				index  : Box::new(index),
				new_val: Box::new(new_val),
				ty     : Type::Array(idx_width, val_width)
			}))
		}
		else {
			Err(AstError(ErrorKind::ExpectedArrayTypeKind{found_kind: array.ty().kind()}))
		}
	}

	fn boolconst_impl(&self, value: bool) -> Result<Expr> {
		Ok(Expr::BoolConst(expr::BoolConst{value}))
	}

	fn not_impl(&self, inner: Expr) -> Result<Expr> {
		inner.ty().expect(Type::Boolean)?;
		Ok(Expr::Not(expr::Not{
			inner: Box::new(inner)
		}))
	}

	fn and_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().expect(Type::Boolean)?;
		right.ty().expect(Type::Boolean)?;
		Ok(Expr::And(expr::And{
			formulas: vec![left, right]
		}))
	}

	// fn conjunction_impl(&self, formulas: Vec<Expr>) -> Result<Expr> {
	// 	Ok(Expr::BoolConst(BoolConst{value: true}))
	// }

	fn or_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().expect(Type::Boolean)?;
		right.ty().expect(Type::Boolean)?;
		Ok(Expr::Or(expr::Or{
			formulas: vec![left, right]
		}))
	}

	// fn disjunction_impl(&self, formulas: Vec<Expr>) -> Result<Expr> {
	// 	Ok(Expr::BoolConst(BoolConst{value: true}))
	// }

	fn xor_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().expect(Type::Boolean)?;
		right.ty().expect(Type::Boolean)?;
		Ok(Expr::Xor(expr::Xor{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn iff_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().expect(Type::Boolean)?;
		right.ty().expect(Type::Boolean)?;
		Ok(Expr::Iff(expr::Iff{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn implies_impl(&self, assumption: Expr, implication: Expr) -> Result<Expr> {
		assumption.ty().expect(Type::Boolean)?;
		implication.ty().expect(Type::Boolean)?;
		Ok(Expr::Implies(expr::Implies{
			assumption : Box::new(assumption),
			implication: Box::new(implication)
		}))
	}

	fn parambool_impl(&self, bool_var: Expr, parameter: Expr) -> Result<Expr> {
		bool_var.ty().expect(Type::Boolean)?;
		parameter.ty().expect(Type::Boolean)?;
		Ok(Expr::ParamBool(expr::ParamBool{
			bool_var: Box::new(bool_var),
			param   : Box::new(parameter)
		}))
	}

	fn eq_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let common_ty = Type::common_of(left.ty(), right.ty())?;
		Ok(Expr::Equals(expr::Equals{
			exprs   : vec![left, right],
			inner_ty: common_ty
		}))
	}

	fn ne_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let eq = self.eq(left, right);
		self.not(eq)
	}

	// fn equality_impl(&self, exprs: Vec<Expr>) -> Result<Expr> {
	// 	if let Some((fst, tail)) = exprs.split_first() {
	// 		for expr in exprs.iter() { expr.ty().expect(fst.ty())?; }
	// 	}
	// 	else {
	// 		return Err(expr::errors::AstError(expr::errors::ErrorKind::TooFewChildren{
	// 			given: 0, expected_min: 1
	// 		}));
	// 	}
	// 	Ok(Expr::Equals(expr::Equals{exprs: exprs}))
	// }

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

	/// TODO: Handle `SymName` generation and check for type conflicts with previously
	///       defined symbols referencing the same name.
	fn symbol_impl(&self, name: &str, ty: Type) -> Result<Expr> {
		Ok(Expr::Symbol(expr::Symbol{name: SymName(0), ty}))
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
