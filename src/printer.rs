use ast::prelude::*;

use std::fmt;

/// Writes the given expression tree into the given writer in the SMTLib2 syntax format.
pub fn write_smtlib2<'e, E>(out: &mut fmt::Write, expr: E)
    where E: Into<&'e AnyExpr>
{
    let expr = expr.into();
    SMTLibWriter::new(out).write_expr(expr)
}

/// Visitor for expression trees that prints the expression tree in SMTLib 2.5 format.
struct SMTLibWriter<'out> {
    /// Current level of indentation.
    indent: usize,
    /// The maximum recursive arity before writing expressions inline.
    max_inline_recursive_arity: usize,
    /// The spaces written per indentation.
    spaces_per_indentation: usize,
    /// The stream to print the given expression tree into.
    out : &'out mut fmt::Write
}

impl<'out> SMTLibWriter<'out> {
    /// Create a new `SMTLibWriter` for the given buffer.
    fn new(out: &mut fmt::Write) -> SMTLibWriter {
        SMTLibWriter{
            indent: 0,
            max_inline_recursive_arity: 4,
            spaces_per_indentation: 2,
            out
        }
    }

    /// Returns `true` if the given expression is inline writable.
    fn is_inline_writable<E>(&self, expr: &E) -> bool
    where
        E: HasArity + Children
    {
        !exceeds_recursive_arity(self.max_inline_recursive_arity, expr)
    }

    /// Increases the indentation by 1.
    fn inc_indent(&mut self) {
        self.indent += 1;
    }

    /// Decreases the indentation by 1.
    fn dec_indent(&mut self) {
        self.indent -= 1;
    }

    /// Writes the current indentation into the buffer.
    fn write_ident(&mut self) {
        for _ in 0..self.indent {
            for _ in 0..self.spaces_per_indentation {
                write!(self.out, " ").unwrap();
            }
        }
    }

    /// Writes a simple line break into the buffer.
    fn writeln(&mut self) {
        writeln!(self.out).unwrap();
    }

    /// Writes the given content string into the buffer.
    fn write<S>(&mut self, content: S)
    where
        S: AsRef<str>
    {
        write!(self.out, "{}", content.as_ref()).unwrap()
    }

    /// Writes the given boolean constant expression into the buffer.
    fn write_bool_const(&mut self, bool_const: &expr::BoolConst) {
        self.write(format!("{}", bool_const.val))
    }

    /// Write the given bitvector constant expression into the buffer.
    fn write_bitvec_const(&mut self, bitvec_const: &expr::BitvecConst) {
        let print_str = match bitvec_const.val.try_to_i64() {
            Ok(val) => format!("{}", val),
            Err(_) => String::from("(Error bv_val_overflow)")
        };
        self.write(print_str);
    }

    /// Writes the given variable expression into the buffer.
    ///
    /// # SMTLib2.5 syntax for sorts (a.k.a. types)
    ///
    /// - `Bool`: A boolean type.
    /// - `(_ Bitvec m)`: A bitvector type with a bit-width of m.
    /// - `(Array i v)`: An array type wih index bit-width of i and value bit-width of v.
    fn write_var(&mut self, var: &expr::Symbol) {
        let resolved_name: &str = &var.name;
        match var.ty() {
            Type::Bool => {
                self.write(format!("({} Bool)", resolved_name))
            }
            Type::Bitvec(bv_ty) => {
                self.write(
                    format!("(_ {} (_ Bitvec {}))",
                        resolved_name,
                        bv_ty.width().raw_width().to_usize())
                    )
            }
            Type::Array(array_ty) => {
                self.write(
                    format!("({} (_ Bitvec {}) (_ Bitvec {})",
                        resolved_name,
                        array_ty.index_ty().width().raw_width().to_usize(),
                        array_ty.value_ty().width().raw_width().to_usize()
                    )
                )
            }
        }
    }

    /// Writes the given expression inline into the buffer.
    /// 
    /// This method won't create new line breaks.
    fn write_expr_inline(&mut self, expr: &AnyExpr) {
        use ast::AnyExpr::*;
        self.write(" ");
        match expr {
            BoolConst(bool_const) => return self.write_bool_const(bool_const),
            BitvecConst(bv_const) => return self.write_bitvec_const(bv_const),
            Symbol(symbol)        => return self.write_var(symbol),
            expr => {
                self.write(format!("({}", expr.kind().smtlib2_name()))
            }
        }
        for child in expr.children() {
            self.write_expr_inline(child)
        }
        self.write(")")
    }

    /// Writes the given expression into the buffer.
    /// 
    /// This writes the expression on its own line.
    fn write_expr(&mut self, expr: &AnyExpr) {
        if self.indent > 0 {
            self.writeln();
        }
        self.write_ident();
        use ast::AnyExpr::*;
        match expr {
            BoolConst(bool_const) => return self.write_bool_const(bool_const),
            BitvecConst(bv_const) => return self.write_bitvec_const(bv_const),
            Symbol(symbol)        => return self.write_var(symbol),
            expr => {
                self.write(format!("({}", expr.kind().smtlib2_name()))
            }
        }
        if self.is_inline_writable(expr) {
            for child in expr.children() {
                self.write_expr_inline(child)
            }
            self.write(")")
        } else {
            self.inc_indent();
            for child in expr.children() {
                self.write_expr(child)
            }
            self.dec_indent();
            self.writeln();
            self.write_ident();
            self.write(")")
        }
    }
}

impl ExprKind {
    /// Returns the SMTLib 2.5 name of the associated expression.
    /// 
    /// # Note
    /// 
    /// Some expressions such as boolean constants, bitvector constants and symbols
    /// do not have a specified SMTLib 2.5 name and will have a well-fitting replacement
    /// string returned.
    pub fn smtlib2_name(self) -> &'static str {
        use ast::ExprKind::*;
        match self {
            Symbol => "symbol",
            BoolConst => "boolconst",
            BitvecConst => "bvconst",
            IfThenElse => "cond",
            BoolEquals => "bveq",
            Not => "not",
            And => "and",
            Or => "or",
            Implies => "=>",
            Xor => "xor",
            BitvecEquals => "bveq",
            Neg => "bvneg",
            Add => "bvadd",
            Mul => "bvmul",
            Sub => "bvsub",
            UnsignedDiv => "bvudiv",
            SignedDiv => "bvsdiv",
            SignedModulo => "bvsmod",
            UnsignedRemainder => "bvurem",
            SignedRemainder => "bvsrem",
            BitNot => "bvnot",
            BitAnd => "bvand",
            BitOr => "bvor",
            BitXor => "bvxor",
            SignedGreaterEquals => "bvsge",
            SignedGreaterThan => "bvsgt",
            SignedLessEquals => "bvsle",
            SignedLessThan => "bvslt",
            UnsignedGreaterEquals => "bvuge",
            UnsignedGreaterThan => "bvugt",
            UnsignedLessEquals => "bvule",
            UnsignedLessThan => "bvult",
            ShiftLeft => "bvshl",
            LogicalShiftRight => "bvlshr",
            ArithmeticShiftRight => "bvashr",
            Concat => "concat",
            Extract => "extract",
            SignExtend => "sext",
            ZeroExtend => "zext",
            ArrayRead => "read",
            ArrayWrite => "write"
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn new_builder() -> PlainExprTreeBuilder {
        PlainExprTreeBuilder::default()
    }

    fn assert_written_eq_string<E, S>(expr: E, expected_str: S)
        where E: IntoAnyExprOrError,
              S: Into<String>
    {
        let expr = expr.into_any_expr_or_error().unwrap();
        let mut sink = String::new();
        write_smtlib2(&mut sink, &expr);
        let expected_str = expected_str.into();
        println!("\n{}", sink);
        assert_eq!(sink, expected_str);
    }

    #[test]
    fn simple_inline_and() {
        let b = new_builder();
        assert_written_eq_string(
            b.and_n(vec![
                b.bool_var("a"),
                b.bool_var("b"),
                b.bool_var("c")
            ]),
            "(and (a Bool) (b Bool) (c Bool))"
        )
    }

    #[test]
    fn simple_block_and() {
        let b = new_builder();
        assert_written_eq_string(
            b.and_n(vec![
                b.bool_var("a"),
                b.bool_var("b"),
                b.bool_var("c"),
                b.bool_var("d")
            ]),
"\
(and
  (a Bool)
  (b Bool)
  (c Bool)
  (d Bool)
)"
        )
    }

    #[test]
    fn complex() {
        let b = new_builder();
        assert_written_eq_string(
            b.and(
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
            ),
"\
(and
  (or
    (a Bool)
    (not (b Bool))
    false
  )
  (cond
    (c Bool)
    true
    (not (d Bool))
  )
)"
        )
    }
}
