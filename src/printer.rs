use ast::prelude::*;

// SMTLib2.5 syntax for sorts (a.k.a. types).
// ==========================================
//
// - `(_ Bitvec m)`: A bitvector type with a bit-width of m.
// - `Bool`: A boolean type.
// - `(Array i v)`: An array type wih index bit-width of i and value bit-width of v.

use std::fmt;

pub fn print_smtlib2<'e, E>(out: &mut fmt::Write, expr: E)
    where E: Into<&'e AnyExpr>
{
    let expr = expr.into();
    let mut traverser = RecursiveTraverseVisitor::new(
        SMTLibPrinter::new(out));
    traverser.traverse_visit(expr);
}

/// Visitor for expression trees that prints the expression tree in SMTLib 2.5 format.
struct SMTLibPrinter<'out> {
    /// Current level of indentation.
    indent: String,
    /// The stream to print the given expression tree into.
    out : &'out mut fmt::Write
}

impl<'out> SMTLibPrinter<'out> {
    fn new(out: &mut fmt::Write) -> SMTLibPrinter {
        SMTLibPrinter{ indent: String::new(), out }
    }

    fn inc_indent(&mut self) {
        self.indent.push(' ');
        self.indent.push(' ');
    }

    fn dec_indent(&mut self) {
        self.indent.pop();
        self.indent.pop();
    }

    fn write_line<S>(&mut self, line: S)
        where S: AsRef<str>
    {
        writeln!(self.out, "{}{}", self.indent, line.as_ref()).unwrap();
    }

    fn write<S>(&mut self, content: S)
        where S: AsRef<str>
    {
        write!(self.out, "{}", content.as_ref()).unwrap();
    }

	fn write_inline<S>(&mut self, event: VisitEvent, content: S)
        where S: AsRef<str>
    {
        if let VisitEvent::Entering = event {
            self.write_line(content);
        }
	}

	fn write_block<S>(&mut self, event: VisitEvent, tag: S)
        where S: AsRef<str>
    {
		use self::VisitEvent::*;
		match event {
			Entering => {
                self.write_line(tag);
				self.inc_indent();
			},
			Leaving => {
				self.dec_indent();
                self.write_line(")");
			}
		}
    }
}

impl<'out> Visitor for SMTLibPrinter<'out> {
    fn visit_cond(&mut self, _: &expr::IfThenElse, event: VisitEvent) {
        self.write_block(event, format!("(ite"))
    }

    fn visit_var(&mut self, var: &expr::Symbol, event: VisitEvent) {
        let resolved_name: &str = &var.name;
        match var.ty() {
            Type::Bool => {
                self.write_inline(event, format!("({} Bool)", resolved_name));
            }
            Type::Bitvec(bv_ty) => {
                self.write_inline(event, format!("(_ {} (_ Bitvec {}))",
                    resolved_name, bv_ty.width().raw_width().to_usize()));
            }
            Type::Array(array_ty) => {
                self.write_inline(event, format!("({} (_ Bitvec {}) (_ Bitvec {})",
                    resolved_name,
                    array_ty.index_ty().width().raw_width().to_usize(),
                    array_ty.value_ty().width().raw_width().to_usize()));
            }
        }
    }

    fn visit_bool_const(&mut self, bool_const: &expr::BoolConst, event: VisitEvent) {
        self.write_inline(event, format!("{}", bool_const.val));
    }

    fn visit_bool_equals(&mut self, _bool_equals: &expr::BoolEquals, event: VisitEvent) {
        self.write_block(event, format!("(="))
    }

    fn visit_and(&mut self, _and: &expr::And, event: VisitEvent) {
        self.write_block(event, format!("(and"))
    }

    fn visit_or(&mut self, _or: &expr::Or, event: VisitEvent) {
        self.write_block(event, format!("(or"))
    }

    fn visit_not(&mut self, _not: &expr::Not, event: VisitEvent) {
        self.write_block(event, format!("(not"))
    }

    fn visit_xor(&mut self, _xor: &expr::Xor, event: VisitEvent) {
        self.write_block(event, format!("(xor"))
    }

    fn visit_implies(&mut self, _implies: &expr::Implies, event: VisitEvent) {
        self.write_block(event, format!("(=>"))
    }

    fn visit_array_read(&mut self, _array_read: &expr::ArrayRead, event: VisitEvent) {
        self.write_block(event, format!("(read"))
    }

    fn visit_array_write(&mut self, _array_write: &expr::ArrayWrite, event: VisitEvent) {
        self.write_block(event, format!("(write"))
    }

    fn visit_bitvec_const(&mut self, bitvec_const: &expr::BitvecConst, event: VisitEvent) {
        let print_str = match bitvec_const.val.try_to_i64() {
            Ok(val) => format!("{}", val),
            Err(_) => String::from("(Error bv_val_overflow)")
        };
        self.write_inline(event, print_str)
    }

    fn visit_add(&mut self, _add: &expr::Add, event: VisitEvent) {
        self.write_block(event, format!("(bvadd"))
    }

    fn visit_mul(&mut self, _mul: &expr::Mul, event: VisitEvent) {
        self.write_block(event, format!("(bvmul"))
    }

    fn visit_neg(&mut self, _neg: &expr::Neg, event: VisitEvent) {
        self.write_block(event, format!("(-"))
    }

    fn visit_sdiv(&mut self, _sdiv: &expr::SignedDiv, event: VisitEvent) {
        self.write_block(event, format!("(bvsdiv"))
    }

    fn visit_smod(&mut self, _smod: &expr::SignedModulo, event: VisitEvent) {
        self.write_block(event, format!("(bvsmod"))
    }

    fn visit_srem(&mut self, _srem: &expr::SignedRemainder, event: VisitEvent) {
        self.write_block(event, format!("(bvsrem"))
    }

    fn visit_sub(&mut self, _sub: &expr::Sub, event: VisitEvent) {
        self.write_block(event, format!("(bvsub"))
    }

    fn visit_udiv(&mut self, _udiv: &expr::UnsignedDiv, event: VisitEvent) {
        self.write_block(event, format!("(bvudiv"))
    }

    fn visit_urem(&mut self, _urem: &expr::UnsignedRemainder, event: VisitEvent) {
        self.write_block(event, format!("(bvurem"))
    }

    fn visit_bitnot(&mut self, _bitnot: &expr::BitNot, event: VisitEvent) {
        self.write_block(event, format!("(bvnot"))
    }

    fn visit_bitand(&mut self, _bitand: &expr::BitAnd, event: VisitEvent) {
        self.write_block(event, format!("(bvand"))
    }

    fn visit_bitor(&mut self, _bitor: &expr::BitOr, event: VisitEvent) {
        self.write_block(event, format!("(bvor"))
    }

    fn visit_bitxor(&mut self, _bitxor: &expr::BitXor, event: VisitEvent) {
        self.write_block(event, format!("(bvxor"))
    }

    fn visit_concat(&mut self, _concat: &expr::Concat, event: VisitEvent) {
        self.write_block(event, format!("(concat"))
    }

    fn visit_extract(&mut self, _extract: &expr::Extract, event: VisitEvent) {
        self.write_block(event, format!("(extract"))
    }

    fn visit_sext(&mut self, _sext: &expr::SignExtend, event: VisitEvent) {
        self.write_block(event, format!("(bvsext"))
    }

    fn visit_zext(&mut self, _zext: &expr::ZeroExtend, event: VisitEvent) {
        self.write_block(event, format!("(bvzext"))
    }

    fn visit_bitvec_equals(&mut self, _bitvec_equals: &expr::BitvecEquals, event: VisitEvent) {
        self.write_block(event, format!("(="))
    }

    fn visit_sge(&mut self, _sge: &expr::SignedGreaterEquals, event: VisitEvent) {
        self.write_block(event, format!("(bvsge"))
    }

    fn visit_sgt(&mut self, _sgt: &expr::SignedGreaterThan, event: VisitEvent) {
        self.write_block(event, format!("(bvsgt"))
    }

    fn visit_sle(&mut self, _sle: &expr::SignedLessEquals, event: VisitEvent) {
        self.write_block(event, format!("(bvsle"))
    }

    fn visit_slt(&mut self, _slt: &expr::SignedLessThan, event: VisitEvent) {
        self.write_block(event, format!("(bvslt"))
    }

    fn visit_uge(&mut self, _uge: &expr::UnsignedGreaterEquals, event: VisitEvent) {
        self.write_block(event, format!("(bvuge"))
    }

    fn visit_ugt(&mut self, _ugt: &expr::UnsignedGreaterThan, event: VisitEvent) {
        self.write_block(event, format!("(bvugt"))
    }

    fn visit_ule(&mut self, _ule: &expr::UnsignedLessEquals, event: VisitEvent) {
        self.write_block(event, format!("(bvule"))
    }

    fn visit_ult(&mut self, _ult: &expr::UnsignedLessThan, event: VisitEvent) {
        self.write_block(event, format!("(bvult"))
    }

    fn visit_ashr(&mut self, _ashr: &expr::ArithmeticShiftRight, event: VisitEvent) {
        self.write_block(event, format!("(bvashr"))
    }

    fn visit_lshr(&mut self, _lshr: &expr::LogicalShiftRight, event: VisitEvent) {
        self.write_block(event, format!("(bvlshr"))
    }

    fn visit_shl(&mut self, _shl: &expr::ShiftLeft, event: VisitEvent) {
        self.write_block(event, format!("(bvshl"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn new_builder() -> PlainExprTreeBuilder {
        PlainExprTreeBuilder::default()
    }

    #[test]
    fn simple() {
        let b = new_builder();
        let expr = b.and(
            b.or_n(vec![
                b.bool_var("a"),
                b.not(
                    b.bool_var("b")
                ),
                b.bool_const(false)
            ]),
            b.cond(
                b.bool_var("c"),
                b.bool_const(true),
                b.not(
                    b.bool_var("d")
                )
            )
        ).unwrap();
        let mut sink = String::new();
        print_smtlib2(&mut sink, &expr);
        let expected = String::from(
        // How to improve the current testing situation:
        //
        // - use library macros such as include_str! or include_bytes!
        // - use something like the "\x20" hack here https://internals.rust-lang.org/t/allow-escaping-space-in-strings/6825
"\
(and
  (or
    (a Bool)
    (not
      (b Bool)
    )
    false
  )
  (ite
    (c Bool)
    true
    (not
      (d Bool)
    )
  )
)
"
        );
        println!("\n{}", sink);
        assert_eq!(sink, expected);
    }
}
