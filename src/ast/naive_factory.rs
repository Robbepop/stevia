
// !! CURRENTLY SET ON HOLD BECAUSE OF OTHER TODOs !!

use ast;
use bitvec::BitVec;

use ast::Type;
use ast::factory::{ExprFactory, ExprFactoryImpl};

use ast::traits::ExprTrait;
use ast::Expr;
use ast::formulas::BoolConst;
use ast::errors::Result;

pub struct NaiveExprFactory {
	// TODO: ctx: Context
}

impl NaiveExprFactory {
	pub fn new() -> NaiveExprFactory {
		NaiveExprFactory{}
	}
}

impl ExprFactoryImpl for NaiveExprFactory {
	fn bvconst_impl<T: Into<BitVec>>(&self, value: T) -> Result<Expr> {
		Ok(Expr::BitVecConst(ast::BitVecConst{
			value: value.into()
		}))
	}

	fn bvneg_impl(&self, inner: Expr) -> Result<Expr> {
		inner.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::Neg(ast::Neg{
			inner: Box::new(inner)
		}))
	}

	fn bvadd_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().kind().expect(ast::TypeKind::BitVec)?;
		right.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::Add(ast::Add{
			terms: vec![left, right]
		}))
	}

	// fn bvsum_impl(&self, terms: Vec<Expr>) -> Result<Expr> {
	// 	Ok(Expr::BoolConst(BoolConst{value: true}))
	// }

	fn bvmul_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().kind().expect(ast::TypeKind::BitVec)?;
		right.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::Mul(ast::Mul{
			factors: vec![left, right]
		}))
	}

	// fn bvprod_impl(&self, terms: Vec<Expr>) -> Result<Expr> {
	// 	Ok(Expr::BoolConst(BoolConst{value: true}))
	// }

	fn bvsub_impl(&self, minuend: Expr, subtrahend: Expr) -> Result<Expr> {
		minuend.ty().kind().expect(ast::TypeKind::BitVec)?;
		subtrahend.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::Sub(ast::Sub{
			minuend   : Box::new(minuend),
			subtrahend: Box::new(subtrahend)
		}))
	}

	fn bvudiv_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		dividend.ty().kind().expect(ast::TypeKind::BitVec)?;
		divisor.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::Div(ast::Div{
			dividend: Box::new(dividend),
			divisor : Box::new(divisor)
		}))
	}

	fn bvumod_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		dividend.ty().kind().expect(ast::TypeKind::BitVec)?;
		divisor.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::Mod(ast::Mod{
			dividend: Box::new(dividend),
			divisor : Box::new(divisor)
		}))
	}

	fn bvsdiv_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		dividend.ty().kind().expect(ast::TypeKind::BitVec)?;
		divisor.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::SignedDiv(ast::SignedDiv{
			dividend: Box::new(dividend),
			divisor : Box::new(divisor)
		}))
	}

	fn bvsmod_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		dividend.ty().kind().expect(ast::TypeKind::BitVec)?;
		divisor.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::SignedMod(ast::SignedMod{
			dividend: Box::new(dividend),
			divisor : Box::new(divisor)
		}))
	}

	fn bvsrem_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		dividend.ty().kind().expect(ast::TypeKind::BitVec)?;
		divisor.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::SignedRem(ast::SignedRem{
			dividend: Box::new(dividend),
			divisor : Box::new(divisor)
		}))
	}

	fn bvnot_impl(&self, inner: Expr) -> Result<Expr> {
		inner.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::BitNot(ast::BitNot{
			inner: Box::new(inner)
		}))
	}

	fn bvand_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().kind().expect(ast::TypeKind::BitVec)?;
		right.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::BitAnd(ast::BitAnd{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn bvor_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().kind().expect(ast::TypeKind::BitVec)?;
		right.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::BitOr(ast::BitOr{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn bvxor_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().kind().expect(ast::TypeKind::BitVec)?;
		right.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::BitXor(ast::BitXor{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn bvnand_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().kind().expect(ast::TypeKind::BitVec)?;
		right.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::BitNand(ast::BitNand{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn bvnor_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().kind().expect(ast::TypeKind::BitVec)?;
		right.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::BitNor(ast::BitNor{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn bvxnor_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().kind().expect(ast::TypeKind::BitVec)?;
		right.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::BitXnor(ast::BitXnor{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn bvult_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().kind().expect(ast::TypeKind::BitVec)?;
		right.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::Lt(ast::Lt{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn bvule_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().kind().expect(ast::TypeKind::BitVec)?;
		right.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::Le(ast::Le{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn bvugt_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().kind().expect(ast::TypeKind::BitVec)?;
		right.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::Gt(ast::Gt{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn bvuge_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().kind().expect(ast::TypeKind::BitVec)?;
		right.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::Ge(ast::Ge{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn bvslt_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().kind().expect(ast::TypeKind::BitVec)?;
		right.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::SignedLt(ast::SignedLt{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn bvsle_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().kind().expect(ast::TypeKind::BitVec)?;
		right.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::SignedLe(ast::SignedLe{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn bvsgt_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().kind().expect(ast::TypeKind::BitVec)?;
		right.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::SignedGt(ast::SignedGt{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn bvsge_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().kind().expect(ast::TypeKind::BitVec)?;
		right.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::SignedGe(ast::SignedGe{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn bvushl_impl(&self, shifted: Expr, shift_amount: Expr) -> Result<Expr> {
		shifted.ty().kind().expect(ast::TypeKind::BitVec)?;
		shift_amount.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::Shl(ast::Shl{
			shifted     : Box::new(shifted),
			shift_amount: Box::new(shift_amount)
		}))
	}

	fn bvushr_impl(&self, shifted: Expr, shift_amount: Expr) -> Result<Expr> {
		shifted.ty().kind().expect(ast::TypeKind::BitVec)?;
		shift_amount.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::Shr(ast::Shr{
			shifted     : Box::new(shifted),
			shift_amount: Box::new(shift_amount)
		}))
	}

	fn bvsshr_impl(&self, shifted: Expr, shift_amount: Expr) -> Result<Expr> {
		shifted.ty().kind().expect(ast::TypeKind::BitVec)?;
		shift_amount.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::SignedShr(ast::SignedShr{
			shifted     : Box::new(shifted),
			shift_amount: Box::new(shift_amount)
		}))
	}

	fn concat_impl(&self, hi: Expr, lo: Expr) -> Result<Expr> {
		hi.ty().kind().expect(ast::TypeKind::BitVec)?;
		lo.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::Concat(ast::Concat{ // TODO: calculate bitwidth
			hi: Box::new(hi),
			lo: Box::new(lo)
		}))
	}

	fn extract_impl(&self, source: Expr, lo_bit: Expr, hi_bit: Expr) -> Result<Expr> {
		source.ty().kind().expect(ast::TypeKind::BitVec)?;
		lo_bit.ty().kind().expect(ast::TypeKind::BitVec)?;
		hi_bit.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::Extract(ast::Extract{
			source: Box::new(source),
			hi_bit: Box::new(hi_bit),
			lo_bit: Box::new(lo_bit)
		}))
	}

	fn uextend_impl(&self, source: Expr, extension: Expr) -> Result<Expr> {
		source.ty().kind().expect(ast::TypeKind::BitVec)?;
		extension.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::Extend(ast::Extend{
			source   : Box::new(source),
			extension: Box::new(extension)
		}))
	}

	fn sextend_impl(&self, source: Expr, extension: Expr) -> Result<Expr> {
		source.ty().kind().expect(ast::TypeKind::BitVec)?;
		extension.ty().kind().expect(ast::TypeKind::BitVec)?;
		Ok(Expr::SignedExtend(ast::SignedExtend{
			source   : Box::new(source),
			extension: Box::new(extension)
		}))
	}

	fn read_impl(&self, array: Expr, index: Expr) -> Result<Expr> {
		if let Type::Array(idx_width, _) = array.ty() {
			index.ty().expect(Type::BitVec(idx_width))?;
			Ok(Expr::Read(ast::Read{
				array: Box::new(array),
				index: Box::new(index)
			}))
		}
		else {
			Err(ast::AstError(
				ast::ErrorKind::ExpectedArrayTypeKind{found_kind: array.ty().kind()}))
		}
	}

	fn write_impl(&self, array: Expr, index: Expr, new_val: Expr) -> Result<Expr> {
		if let Type::Array(idx_width, val_width) = array.ty() {
			index.ty().expect(Type::BitVec(idx_width))?;
			new_val.ty().expect(Type::BitVec(val_width))?;
			Ok(Expr::Write(ast::Write{
				array  : Box::new(array),
				index  : Box::new(index),
				new_val: Box::new(new_val)
			}))
		}
		else {
			Err(ast::AstError(
				ast::ErrorKind::ExpectedArrayTypeKind{found_kind: array.ty().kind()}))
		}
	}

	fn boolconst_impl(&self, value: bool) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value}))
	}

	fn not_impl(&self, inner: Expr) -> Result<Expr> {
		inner.ty().expect(Type::Boolean)?;
		Ok(Expr::Not(ast::Not{
			inner: Box::new(inner)
		}))
	}

	fn and_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().expect(Type::Boolean)?;
		right.ty().expect(Type::Boolean)?;
		Ok(Expr::And(ast::And{
			formulas: vec![left, right]
		}))
	}

	// fn conjunction_impl(&self, formulas: Vec<Expr>) -> Result<Expr> {
	// 	Ok(Expr::BoolConst(BoolConst{value: true}))
	// }

	fn or_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().expect(Type::Boolean)?;
		right.ty().expect(Type::Boolean)?;
		Ok(Expr::Or(ast::Or{
			formulas: vec![left, right]
		}))
	}

	// fn disjunction_impl(&self, formulas: Vec<Expr>) -> Result<Expr> {
	// 	Ok(Expr::BoolConst(BoolConst{value: true}))
	// }

	fn xor_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().expect(Type::Boolean)?;
		right.ty().expect(Type::Boolean)?;
		Ok(Expr::Xor(ast::Xor{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn iff_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		left.ty().expect(Type::Boolean)?;
		right.ty().expect(Type::Boolean)?;
		Ok(Expr::Iff(ast::Iff{
			left : Box::new(left),
			right: Box::new(right)
		}))
	}

	fn implies_impl(&self, assumption: Expr, implication: Expr) -> Result<Expr> {
		assumption.ty().expect(Type::Boolean)?;
		implication.ty().expect(Type::Boolean)?;
		Ok(Expr::Implies(ast::Implies{
			assumption : Box::new(assumption),
			implication: Box::new(implication)
		}))
	}

	fn parambool_impl(&self, bool_var: Expr, parameter: Expr) -> Result<Expr> {
		bool_var.ty().expect(Type::Boolean)?;
		parameter.ty().expect(Type::Boolean)?;
		Ok(Expr::ParamBool(ast::ParamBool{
			bool_var: Box::new(bool_var),
			param   : Box::new(parameter)
		}))
	}

	fn eq_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Type::common_of(left.ty(), right.ty())?;
		Ok(Expr::Equals(ast::Equals{exprs: vec![left, right]}))
		// self.equality(vec![left, right])
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
	// 		return Err(ast::errors::AstError(ast::errors::ErrorKind::TooFewChildren{
	// 			given: 0, expected_min: 1
	// 		}));
	// 	}
	// 	Ok(Expr::Equals(ast::Equals{exprs: exprs}))
	// }

	/// Creates an if-then-else expression.
	/// 
	/// Checks if cond (condition) is of type boolean and also checks if
	/// then-case and else-case return a common type.
	fn ite_impl(&self, cond: Expr, then_case: Expr, else_case: Expr) -> Result<Expr> {
		cond.ty().expect(Type::Boolean)?;
		let common_type = Type::common_of(then_case.ty(), else_case.ty())?;
		Ok(Expr::IfThenElse(ast::IfThenElse{
			cond     : Box::new(cond),
			then_case: Box::new(then_case),
			else_case: Box::new(else_case),
			ty       : common_type
		}))
	}

	/// TODO: Handle `SymName` generation and check for type conflicts with previously
	///       defined symbols referencing the same name.
	fn symbol_impl(&self, name: &str, ty: Type) -> Result<Expr> {
		Ok(Expr::Symbol(ast::Symbol{name: ast::SymName(0), ty}))
	}

	fn boolean_impl(&self, name: &str) -> Result<Expr> {
		self.symbol(name, Type::Boolean)
	}

	fn bitvec_impl(&self, name: &str, bitwidth: usize) -> Result<Expr> {
		self.symbol(name, Type::BitVec(bitwidth))
	}

	fn array_impl(&self, name: &str, idx_width: usize, val_width: usize) -> Result<Expr> {
		self.symbol(name, Type::Array(idx_width, val_width))
	}
}
