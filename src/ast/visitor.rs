
use ast::prelude::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Event {
	Entering,
	Leaving
}

pub trait Visitor<'ast>: Sized {

	// TERM EXPRESSIONS

	fn visit_bvconst(&mut self, expr: &'ast BitVecConst, event: Event);
	fn visit_bvneg(&mut self, expr: &'ast Neg, event: Event);
	fn visit_bvadd(&mut self, expr: &'ast Add, event: Event);
	fn visit_bvmul(&mut self, expr: &'ast Mul, event: Event);
	fn visit_bvsub(&mut self, expr: &'ast Sub, event: Event);
	fn visit_bvudiv(&mut self, expr: &'ast Div, event: Event);
	fn visit_bvumod(&mut self, expr: &'ast Mod, event: Event);
	fn visit_bvsdiv(&mut self, expr: &'ast SignedDiv, event: Event);
	fn visit_bvsmod(&mut self, expr: &'ast SignedMod, event: Event);
	fn visit_bvsrem(&mut self, expr: &'ast SignedRem, event: Event);

	fn visit_bvnot(&mut self, expr: &'ast BitNot, event: Event);
	fn visit_bvand(&mut self, expr: &'ast BitAnd, event: Event);
	fn visit_bvor(&mut self, expr: &'ast BitOr, event: Event);
	fn visit_bvxor(&mut self, expr: &'ast BitXor, event: Event);
	fn visit_bvnand(&mut self, expr: &'ast BitNand, event: Event);
	fn visit_bvnor(&mut self, expr: &'ast BitNor, event: Event);
	fn visit_bvxnor(&mut self, expr: &'ast BitXnor, event: Event);

	fn visit_bvult(&mut self, expr: &'ast Lt, event: Event);
	fn visit_bvule(&mut self, expr: &'ast Le, event: Event);
	fn visit_bvugt(&mut self, expr: &'ast Gt, event: Event);
	fn visit_bvuge(&mut self, expr: &'ast Ge, event: Event);
	fn visit_bvslt(&mut self, expr: &'ast SignedLt, event: Event);
	fn visit_bvsle(&mut self, expr: &'ast SignedLe, event: Event);
	fn visit_bvsgt(&mut self, expr: &'ast SignedGt, event: Event);
	fn visit_bvsge(&mut self, expr: &'ast SignedGe, event: Event);

	fn visit_bvushl(&mut self, expr: &'ast Shl, event: Event);
	fn visit_bvushr(&mut self, expr: &'ast Shr, event: Event);
	fn visit_bvsshr(&mut self, expr: &'ast SignedShr, event: Event);

	fn visit_concat(&mut self, expr: &'ast Concat, event: Event);
	fn visit_extract(&mut self, expr: &'ast Extract, event: Event);
	fn visit_uextend(&mut self, expr: &'ast Extend, event: Event);
	fn visit_sextend(&mut self, expr: &'ast SignedExtend, event: Event);

	fn visit_read(&mut self, expr: &'ast Read, event: Event);
	fn visit_write(&mut self, expr: &'ast Write, event: Event);

	// FORMULA EXPRESSIONS

	fn visit_boolconst(&mut self, expr: &'ast BoolConst, event: Event);

	fn visit_not(&mut self, expr: &'ast Not, event: Event);

	fn visit_and(&mut self, expr: &'ast And, event: Event);
	fn visit_or(&mut self, expr: &'ast Or, event: Event);
	fn visit_xor(&mut self, expr: &'ast Xor, event: Event);
	fn visit_iff(&mut self, expr: &'ast Iff, event: Event);
	fn visit_implies(&mut self, expr: &'ast Implies, event: Event);

	fn visit_param_bool(&mut self, expr: &'ast ParamBool, event: Event);

	// GENERIC EXPRESSIONS

	fn visit_equals(&mut self, expr: &'ast Equals, event: Event);
	fn visit_ite(&mut self, expr: &'ast IfThenElse, event: Event);
	fn visit_symbol(&mut self, expr: &'ast Symbol, event: Event);

	fn visit_at_event(&mut self, expr: &'ast Expr, event: Event) {
		use self::Expr::*;
		match *expr {
			BitVecConst(ref expr) => self.visit_bvconst(expr, event),
			Neg(ref expr) => self.visit_bvneg(expr, event),
			Add(ref expr) => self.visit_bvadd(expr, event),
			Mul(ref expr) => self.visit_bvmul(expr, event),
			Sub(ref expr) => self.visit_bvsub(expr, event),
			Div(ref expr) => self.visit_bvudiv(expr, event),
			Mod(ref expr) => self.visit_bvumod(expr, event),
			SignedDiv(ref expr) => self.visit_bvsdiv(expr, event),
			SignedMod(ref expr) => self.visit_bvsmod(expr, event),
			SignedRem(ref expr) => self.visit_bvsrem(expr, event),

			BitNot(ref expr) => self.visit_bvnot(expr, event),
			BitAnd(ref expr) => self.visit_bvand(expr, event),
			BitOr(ref expr) => self.visit_bvor(expr, event),
			BitXor(ref expr) => self.visit_bvxor(expr, event),
			BitNand(ref expr) => self.visit_bvnand(expr, event),
			BitNor(ref expr) => self.visit_bvnor(expr, event),
			BitXnor(ref expr) => self.visit_bvxnor(expr, event),

			Lt(ref expr) => self.visit_bvult(expr, event),
			Le(ref expr) => self.visit_bvule(expr, event),
			Gt(ref expr) => self.visit_bvugt(expr, event),
			Ge(ref expr) => self.visit_bvuge(expr, event),
			SignedLt(ref expr) => self.visit_bvslt(expr, event),
			SignedLe(ref expr) => self.visit_bvsle(expr, event),
			SignedGt(ref expr) => self.visit_bvsgt(expr, event),
			SignedGe(ref expr) => self.visit_bvsge(expr, event),

			Shl(ref expr) => self.visit_bvushl(expr, event),
			Shr(ref expr) => self.visit_bvushr(expr, event),
			SignedShr(ref expr) => self.visit_bvsshr(expr, event),

			Concat(ref expr) => self.visit_concat(expr, event),
			Extract(ref expr) => self.visit_extract(expr, event),
			Extend(ref expr) => self.visit_uextend(expr, event),
			SignedExtend(ref expr) => self.visit_sextend(expr, event),

			Read(ref expr) => self.visit_read(expr, event),
			Write(ref expr) => self.visit_write(expr, event),

			// FORMULA EXPRESSIONS

			BoolConst(ref expr) => self.visit_boolconst(expr, event),

			Not(ref expr) => self.visit_not(expr, event),

			And(ref expr) => self.visit_and(expr, event),
			Or(ref expr) => self.visit_or(expr, event),
			Xor(ref expr) => self.visit_xor(expr, event),
			Iff(ref expr) => self.visit_iff(expr, event),
			Implies(ref expr) => self.visit_implies(expr, event),

			ParamBool(ref expr) => self.visit_param_bool(expr, event),

			// GENERIC EXPRESSIONS

			Equals(ref expr) => self.visit_equals(expr, event),
			IfThenElse(ref expr) => self.visit_ite(expr, event),
			Symbol(ref expr) => self.visit_symbol(expr, event)
		}
	}

	fn visit(&mut self, expr: &'ast Expr) {
		self.visit_at_event(expr, Event::Entering);
		walk_expr(self, expr);
		self.visit_at_event(expr, Event::Leaving);
	}
}

fn walk_expr<'ast, V: Visitor<'ast>>(visitor: &mut V, expr: &'ast Expr) {
	for child in expr.childs() {
		visitor.visit(child)
	}
}
