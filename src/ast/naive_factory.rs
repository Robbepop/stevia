
// !! CURRENTLY SET ON HOLD BECAUSE OF OTHER TODOs !!

use ast;
use bitvec::BitVec;

use ast::Type;
use ast::factory::ExprFactory;

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

impl ExprFactory for NaiveExprFactory {
	fn bvconst<T: Into<BitVec>>(&mut self, value: T) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvneg(&mut self, inner: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvadd(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvsum(&mut self, terms: Vec<Expr>) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvmul(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvprod(&mut self, terms: Vec<Expr>) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvsub(&mut self, minuend: Expr, subtrahend: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvudiv(&mut self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvumod(&mut self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvsdiv(&mut self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvsmod(&mut self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvsrem(&mut self, dividend: Expr, divisor: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvnot(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvand(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvor(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvxor(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvnand(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvnor(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvxnor(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvult(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvule(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvugt(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvuge(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvslt(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvsle(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvsgt(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvsge(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvushl(&mut self, shifted: Expr, shift_amount: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvushr(&mut self, shifted: Expr, shift_amount: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn bvsshr(&mut self, shifted: Expr, shift_amount: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn concat(&mut self, hi: Expr, lo: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn extract(&mut self, source: Expr, lo_bit: Expr, hi_bit: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn uextend(&mut self, source: Expr, target_width: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn sextend(&mut self, source: Expr, target_width: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn read(&mut self, array: Expr, index: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn write(&mut self, array: Expr, index: Expr, new_val: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn boolconst(&mut self, value: bool) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value}))
	}

	fn not(&mut self, inner: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn and(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn conjunction(&mut self, formulas: Vec<Expr>) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn or(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn disjunction(&mut self, formulas: Vec<Expr>) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn xor(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn iff(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn implies(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn parambool(&mut self, bool_var: Expr, parameter: Expr) -> Result<Expr> {
		Ok(Expr::BoolConst(BoolConst{value: true}))
	}

	fn eq(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		self.equality(vec![left, right])
	}

	fn ne(&mut self, left: Expr, right: Expr) -> Result<Expr> {
		let eq = self.eq(left, right)?;
		self.not(eq)
	}

	fn equality(&mut self, exprs: Vec<Expr>) -> Result<Expr> {
		if let Some((fst, tail)) = exprs.split_first() {
			for expr in exprs.iter() { expr.ty().expect(fst.ty())?; }
		}
		else {
			return Err(ast::errors::AstError(ast::errors::ErrorKind::TooFewChildren{
				given: 0, expected_min: 1
			}));
		}
		Ok(ast::variants::Expr::Equals(ast::Equals{exprs: exprs}))
	}

	/// Creates an if-then-else expression.
	/// 
	/// Checks if cond (condition) is of type boolean and also checks if
	/// then-case and else-case return a common type.
	fn ite(&mut self, cond: Expr, then_case: Expr, else_case: Expr) -> Result<Expr> {
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
	fn symbol<S: AsRef<str>>(&mut self, name: S, ty: Type) -> Result<Expr> {
		Ok(Expr::Symbol(ast::Symbol{name: ast::SymName(0), ty}))
	}

	fn boolean<S: AsRef<str>>(&mut self, name: S) -> Result<Expr> {
		self.symbol(name, Type::Boolean)
	}

	fn bitvec<S: AsRef<str>>(&mut self, name: S, bitwidth: usize) -> Result<Expr> {
		self.symbol(name, Type::BitVec(bitwidth))
	}

	fn array<S: AsRef<str>>(&mut self, name: S, idx_width: usize, val_width: usize) -> Result<Expr> {
		self.symbol(name, Type::Array(idx_width, val_width))
	}
}
