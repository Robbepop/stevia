
// !! CURRENTLY SET ON HOLD BECAUSE OF OTHER TODOs !!

use ast;
use bitvec::BitVec;

use ast::Type;
use ast::factory::{ExprFactory, ExprFactoryImpl};

use ast::traits::ExprTrait;
use ast::variants::Expr;
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
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvneg_impl(&self, inner: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvadd_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	// fn bvsum_impl(&self, terms: Vec<Expr>) -> Result<Expr> {
	// 	Ok(Expr::BoolConst(BoolConst{value: true}))
	// }

	fn bvmul_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	// fn bvprod_impl(&self, terms: Vec<Expr>) -> Result<Expr> {
	// 	Ok(Expr::BoolConst(BoolConst{value: true}))
	// }

	fn bvsub_impl(&self, minuend: Expr, subtrahend: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvudiv_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvumod_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvsdiv_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvsmod_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvsrem_impl(&self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvnot_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvand_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvor_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvxor_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvnand_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvnor_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvxnor_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvult_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvule_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvugt_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvuge_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvslt_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvsle_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvsgt_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvsge_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvushl_impl(&self, shifted: Expr, shift_amount: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvushr_impl(&self, shifted: Expr, shift_amount: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvsshr_impl(&self, shifted: Expr, shift_amount: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn concat_impl(&self, hi: Expr, lo: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn extract_impl(&self, source: Expr, lo_bit: Expr, hi_bit: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn uextend_impl(&self, source: Expr, target_width: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn sextend_impl(&self, source: Expr, target_width: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn read_impl(&self, array: Expr, index: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn write_impl(&self, array: Expr, index: Expr, new_val: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn boolconst_impl(&self, value: bool) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value}))
	}

	fn not_impl(&self, inner: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn and_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	// fn conjunction_impl(&self, formulas: Vec<Expr>) -> Result<Expr> {
	// 	Ok(Expr::BoolConst(BoolConst{value: true}))
	// }

	fn or_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	// fn disjunction_impl(&self, formulas: Vec<Expr>) -> Result<Expr> {
	// 	Ok(Expr::BoolConst(BoolConst{value: true}))
	// }

	fn xor_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn iff_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn implies_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn parambool_impl(&self, bool_var: Expr, parameter: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn eq_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		Type::common_of(left.ty(), right.ty())?;
		Ok(ast::variants::Expr::Equals(ast::Equals{exprs: vec![left, right]}))
		// self.equality(vec![left, right])
	}

	fn ne_impl(&self, left: Expr, right: Expr) -> Result<Expr> {
		let eq = self.eq(left, right)?;
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
	// 	Ok(ast::variants::Expr::Equals(ast::Equals{exprs: exprs}))
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
