
use ast::prelude::*;
use ast::expr::*;
use ast::visitor::{Visitor, Event};

pub fn pretty_print_expr(out: &mut ::std::io::Write, expr: &Expr) {
	PrettyPrinter::new(out).visit(expr);
}

struct PrettyPrinter<'out> {
	indent: String,
	out   : &'out mut ::std::io::Write
}

impl<'out> PrettyPrinter<'out> {
	fn new(out: &'out mut ::std::io::Write) -> PrettyPrinter {
		PrettyPrinter{
			indent: String::new(),
			out   : out
		}
	}
}

impl<'out> PrettyPrinter<'out> {
	fn push_indent(&mut self) {
		self.indent.push('\t');
	}

	fn pop_indent(&mut self) {
		self.indent.pop();
	}

	fn inline<S: AsRef<str>>(&mut self, event: Event, content: S) {
		use self::Event::*;
		match event {
			Entering => {
				writeln!(self.out, "{}( {} )", &self.indent, content.as_ref()).unwrap();
			},
			Leaving => ()
		}
	}

	fn block<S: AsRef<str>>(&mut self, event: Event, tag: S) {
		use self::Event::*;
		match event {
			Entering => {
				writeln!(self.out, "{}({}", &self.indent, tag.as_ref()).unwrap();
				self.push_indent();
			},
			Leaving => {
				self.pop_indent();
				writeln!(self.out, "{})", &self.indent).unwrap();
			}
		}
	}
}

impl<'ast, 'out> Visitor<'ast> for PrettyPrinter<'out> {
	fn visit_bvconst(&mut self, expr: &'ast BitVecConst, event: Event) {
		self.inline(event,
			format!("bvconst :{} {}", expr.ty.bitwidth().unwrap(), expr.value.to_u64()))
	}

	fn visit_bvneg(&mut self, _: &'ast Neg, event: Event) {
		self.block(event, "bvneg")
	}

	fn visit_bvadd(&mut self, _: &'ast Add, event: Event) {
		self.block(event, "bvadd")
	}

	fn visit_bvmul(&mut self, _: &'ast Mul, event: Event) {
		self.block(event, "bvmul")
	}

	fn visit_bvsub(&mut self, _: &'ast Sub, event: Event) {
		self.block(event, "bvsub")
	}

	fn visit_bvudiv(&mut self, _: &'ast Div, event: Event) {
		self.block(event, "bvudiv")
	}

	fn visit_bvumod(&mut self, _: &'ast Mod, event: Event) {
		self.block(event, "bvumod")
	}

	fn visit_bvsdiv(&mut self, _: &'ast SignedDiv, event: Event) {
		self.block(event, "bvsdiv")
	}

	fn visit_bvsmod(&mut self, _: &'ast SignedMod, event: Event) {
		self.block(event, "bvsmod")
	}

	fn visit_bvsrem(&mut self, _: &'ast SignedRem, event: Event) {
		self.block(event, "bvsrem")
	}

	fn visit_bvnot(&mut self, _: &'ast BitNot, event: Event) {
		self.block(event, "bvnot")
	}

	fn visit_bvand(&mut self, _: &'ast BitAnd, event: Event) {
		self.block(event, "bvand")
	}

	fn visit_bvor(&mut self, _: &'ast BitOr, event: Event) {
		self.block(event, "bvor")
	}

	fn visit_bvxor(&mut self, _: &'ast BitXor, event: Event) {
		self.block(event, "bvxor")
	}

	fn visit_bvnand(&mut self, _: &'ast BitNand, event: Event) {
		self.block(event, "bvnand")
	}

	fn visit_bvnor(&mut self, _: &'ast BitNor, event: Event) {
		self.block(event, "bvnor")
	}

	fn visit_bvxnor(&mut self, _: &'ast BitXnor, event: Event) {
		self.block(event, "bvxnor")
	}

	fn visit_bvult(&mut self, _: &'ast Lt, event: Event) {
		self.block(event, "bvult")
	}

	fn visit_bvule(&mut self, _: &'ast Le, event: Event) {
		self.block(event, "bvule")
	}

	fn visit_bvugt(&mut self, _: &'ast Gt, event: Event) {
		self.block(event, "bvugt")
	}

	fn visit_bvuge(&mut self, _: &'ast Ge, event: Event) {
		self.block(event, "bvuge")
	}

	fn visit_bvslt(&mut self, _: &'ast SignedLt, event: Event) {
		self.block(event, "bvslt")
	}

	fn visit_bvsle(&mut self, _: &'ast SignedLe, event: Event) {
		self.block(event, "bvsle")
	}

	fn visit_bvsgt(&mut self, _: &'ast SignedGt, event: Event) {
		self.block(event, "bvsgt")
	}

	fn visit_bvsge(&mut self, _: &'ast SignedGe, event: Event) {
		self.block(event, "bvsge")
	}

	fn visit_bvushl(&mut self, _: &'ast Shl, event: Event) {
		self.block(event, "bvushl")
	}

	fn visit_bvushr(&mut self, _: &'ast Shr, event: Event) {
		self.block(event, "bvushr")
	}

	fn visit_bvsshr(&mut self, _: &'ast SignedShr, event: Event) {
		self.block(event, "bvsshr")
	}

	fn visit_concat(&mut self, _: &'ast Concat, event: Event) {
		self.block(event, "concat")
	}

	fn visit_extract(&mut self, _: &'ast Extract, event: Event) {
		self.block(event, "extract")
	}

	fn visit_uextend(&mut self, _: &'ast Extend, event: Event) {
		self.block(event, "uextend")
	}

	fn visit_sextend(&mut self, _: &'ast SignedExtend, event: Event) {
		self.block(event, "sextend")
	}

	fn visit_read(&mut self, _: &'ast Read, event: Event) {
		self.block(event, "read")
	}

	fn visit_write(&mut self, _: &'ast Write, event: Event) {
		self.block(event, "write")
	}

	fn visit_boolconst(&mut self, expr: &'ast BoolConst, event: Event) {
		self.inline(event, format!("{}", expr.value))
	}

	fn visit_not(&mut self, _: &'ast Not, event: Event) {
		self.block(event, "not")
	}

	fn visit_and(&mut self, _: &'ast And, event: Event) {
		self.block(event, "and")
	}

	fn visit_or(&mut self, _: &'ast Or, event: Event) {
		self.block(event, "or")
	}

	fn visit_xor(&mut self, _: &'ast Xor, event: Event) {
		self.block(event, "xor")
	}

	fn visit_iff(&mut self, _: &'ast Iff, event: Event) {
		self.block(event, "iff")
	}

	fn visit_implies(&mut self, _: &'ast Implies, event: Event) {
		self.block(event, "implies")
	}

	fn visit_param_bool(&mut self, _: &'ast ParamBool, event: Event) {
		self.block(event, "param_bool")
	}

	fn visit_equals(&mut self, _: &'ast Equals, event: Event) {
		self.block(event, "=")
	}

	fn visit_ite(&mut self, _: &'ast IfThenElse, event: Event) {
		self.block(event, "ite")
	}

	fn visit_symbol(&mut self, expr: &'ast Symbol, event: Event) {
		self.inline(event, format!("symbol {:?}", expr.name))
	}
}
