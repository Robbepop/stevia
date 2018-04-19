use ast::prelude::*;

/// Validates the consistency of the given expression tree.
///
/// # Note
///
/// Consistency of an expression tree is determined by the following factors:
///
/// - Types of all expressions and their child expressions are valid.
/// - Arities of all expressions are within legal bounds.
/// - Cast invariances are met for all casting expressions.
///
/// This collects all found errors into a vector and returns it if non-empty.
pub fn assert_consistency_recursively<'ctx, 'e, E>(ctx: &'ctx Context, expr: E) -> Result<(), Vec<ExprError>>
where
    E: Into<&'e AnyExpr>,
{
    let expr = expr.into();
    let mut traverser = RecursiveTraverseVisitor::new(ConsistencyChecker::new(ctx));
    traverser.traverse_visit(expr);
    let result = traverser.into_visitor();
    if result.found_errors.is_empty() {
        return Ok(());
    }
    Err(result.found_errors)
}

/// Checks the consistency of an expression tree.
///
/// Stores all errors found for later introspection.
struct ConsistencyChecker<'ctx> {
    /// All found errors are stored here.
    found_errors: Vec<ExprError>,
    /// The associated context of this consistency checker.
    ctx: &'ctx Context
}

impl<'ctx> ConsistencyChecker<'ctx> {
    /// Creates a new consistency checker for the given context.
    pub fn new(ctx: &'ctx Context) -> Self {
        Self{ found_errors: vec![], ctx }
    }
}

/// Asserts the consistency of the conditional expression.
fn assert_cond_consistency(expr: &expr::IfThenElse) -> ExprResult<()> {
    expect_bool_ty(&expr.children.cond).map_err(|e| {
        e.context("The condition of an if-then-else expression must be of boolean type.")
    })?;
    expect_common_ty(&expr.children.then_case, &expr.children.else_case).map_err(|e| {
        e.context(
        "The types of the then-case and else-case of an if-then-else expression must be the same.")
    })?;
    Ok(())
}

/// Assert the consistency of symbol expressions.
fn assert_symbol_consistency(ctx: &Context, expr: &expr::Symbol) -> ExprResult<()> {
    if let SymbolId::Named(named) = expr.id {
        let assoc_ty = ctx.symbol_types
                          .get(named)
                          .expect("Expected to have an associated type to this named symbol. \
                                   Maybe the wrong context is in used?");
        return expect_matching_symbol_type(assoc_ty, expr.ty(), named)
    }
    Ok(())
}

/// Assert the consistency of boolean equality expressions.
fn assert_bool_equals_consistency(expr: &expr::BoolEquals) -> ExprResult<()> {
    error::expect_min_children(2, expr)?;
    error::expect_concrete_ty_n(expr.ty(), expr)?;
    Ok(())
}

impl<'ctx> ConsistencyChecker<'ctx> {
    /// Forwards the given expression to the given checker and adds a potential
    /// found error to the list of found errors.
    fn forward_assert_consistency<E, F>(&mut self, expr: &E, checker: F)
    where
        F: Fn(&E) -> ExprResult<()>,
    {
        if let Err(err) = checker(expr) {
            self.found_errors.push(err)
        }
    }
}

impl<'ctx> Visitor for ConsistencyChecker<'ctx> {
    fn visit_any_expr(&mut self, expr: &AnyExpr, event: VisitEvent) {
        if event != VisitEvent::Leaving {
            return;
        }
        use self::AnyExpr::*;
        match expr {
            IfThenElse(expr) => self.visit_cond(expr, event),
            Symbol(expr) => self.visit_var(expr, event),

            BoolConst(expr) => self.visit_bool_const(expr, event),
            BoolEquals(expr) => self.visit_bool_equals(expr, event),
            BitvecEquals(expr) => self.visit_bitvec_equals(expr, event),
            Not(expr) => self.visit_not(expr, event),
            And(expr) => self.visit_and(expr, event),
            Or(expr) => self.visit_or(expr, event),
            Xor(expr) => self.visit_xor(expr, event),
            Implies(expr) => self.visit_implies(expr, event),

            SignedGreaterEquals(expr) => self.visit_sge(expr, event),
            SignedGreaterThan(expr) => self.visit_sgt(expr, event),
            SignedLessEquals(expr) => self.visit_sle(expr, event),
            SignedLessThan(expr) => self.visit_slt(expr, event),
            UnsignedGreaterEquals(expr) => self.visit_uge(expr, event),
            UnsignedGreaterThan(expr) => self.visit_ugt(expr, event),
            UnsignedLessEquals(expr) => self.visit_ule(expr, event),
            UnsignedLessThan(expr) => self.visit_ult(expr, event),

            Add(expr) => self.visit_add(expr, event),
            BitvecConst(expr) => self.visit_bitvec_const(expr, event),
            Mul(expr) => self.visit_mul(expr, event),
            Neg(expr) => self.visit_neg(expr, event),
            SignedDiv(expr) => self.visit_sdiv(expr, event),
            SignedModulo(expr) => self.visit_smod(expr, event),
            SignedRemainder(expr) => self.visit_srem(expr, event),
            Sub(expr) => self.visit_sub(expr, event),
            UnsignedDiv(expr) => self.visit_udiv(expr, event),
            UnsignedRemainder(expr) => self.visit_urem(expr, event),

            BitAnd(expr) => self.visit_bitand(expr, event),
            BitNot(expr) => self.visit_bitnot(expr, event),
            BitOr(expr) => self.visit_bitor(expr, event),
            BitXor(expr) => self.visit_bitxor(expr, event),

            Concat(expr) => self.visit_concat(expr, event),
            Extract(expr) => self.visit_extract(expr, event),
            SignExtend(expr) => self.visit_sext(expr, event),
            ZeroExtend(expr) => self.visit_zext(expr, event),

            ArithmeticShiftRight(expr) => self.visit_ashr(expr, event),
            LogicalShiftRight(expr) => self.visit_lshr(expr, event),
            ShiftLeft(expr) => self.visit_shl(expr, event),

            ArrayRead(expr) => self.visit_array_read(expr, event),
            ArrayWrite(expr) => self.visit_array_write(expr, event),
        }
    }

    fn visit_bool_expr(&mut self, _: &AnyExpr, _: VisitEvent) {
        unreachable!()
    }

    fn visit_bitvec_expr(&mut self, _: &AnyExpr, _: VisitEvent) {
        unreachable!()
    }

    fn visit_array_expr(&mut self, _: &AnyExpr, _: VisitEvent) {
        unreachable!()
    }

    fn visit_cond(&mut self, cond: &expr::IfThenElse, _: VisitEvent) {
        self.forward_assert_consistency(cond, assert_cond_consistency)
    }

    fn visit_var(&mut self, var: &expr::Symbol, _: VisitEvent) {
        if let Err(err) = assert_symbol_consistency(self.ctx, var) {
            self.found_errors.push(err)
        }
    }

    fn visit_bool_const(&mut self, _bool_const: &expr::BoolConst, _: VisitEvent) {}

    fn visit_bool_equals(&mut self, bool_equals: &expr::BoolEquals, _: VisitEvent) {
        self.forward_assert_consistency(bool_equals, assert_bool_equals_consistency)
    }

    fn visit_and(&mut self, _and: &expr::And, _: VisitEvent) {}

    fn visit_or(&mut self, _or: &expr::Or, _: VisitEvent) {}

    fn visit_not(&mut self, _not: &expr::Not, _: VisitEvent) {}

    fn visit_xor(&mut self, _xor: &expr::Xor, _: VisitEvent) {}

    fn visit_implies(&mut self, _implies: &expr::Implies, _: VisitEvent) {}

    fn visit_array_read(&mut self, _array_read: &expr::ArrayRead, _: VisitEvent) {}

    fn visit_array_write(&mut self, _array_write: &expr::ArrayWrite, _: VisitEvent) {}

    fn visit_bitvec_const(&mut self, _bitvec_const: &expr::BitvecConst, _: VisitEvent) {}

    fn visit_add(&mut self, _add: &expr::Add, _: VisitEvent) {}

    fn visit_mul(&mut self, _mul: &expr::Mul, _: VisitEvent) {}

    fn visit_neg(&mut self, _neg: &expr::Neg, _: VisitEvent) {}

    fn visit_sdiv(&mut self, _sdiv: &expr::SignedDiv, _: VisitEvent) {}

    fn visit_smod(&mut self, _smod: &expr::SignedModulo, _: VisitEvent) {}

    fn visit_srem(&mut self, _srem: &expr::SignedRemainder, _: VisitEvent) {}

    fn visit_sub(&mut self, _sub: &expr::Sub, _: VisitEvent) {}

    fn visit_udiv(&mut self, _udiv: &expr::UnsignedDiv, _: VisitEvent) {}

    fn visit_urem(&mut self, _urem: &expr::UnsignedRemainder, _: VisitEvent) {}

    fn visit_bitnot(&mut self, _bitnot: &expr::BitNot, _: VisitEvent) {}

    fn visit_bitand(&mut self, _bitand: &expr::BitAnd, _: VisitEvent) {}

    fn visit_bitor(&mut self, _bitor: &expr::BitOr, _: VisitEvent) {}

    fn visit_bitxor(&mut self, _bitxor: &expr::BitXor, _: VisitEvent) {}

    fn visit_concat(&mut self, _concat: &expr::Concat, _: VisitEvent) {}

    fn visit_extract(&mut self, _extract: &expr::Extract, _: VisitEvent) {}

    fn visit_sext(&mut self, _sext: &expr::SignExtend, _: VisitEvent) {}

    fn visit_zext(&mut self, _zext: &expr::ZeroExtend, _: VisitEvent) {}

    fn visit_bitvec_equals(&mut self, _bitvec_equals: &expr::BitvecEquals, _: VisitEvent) {}

    fn visit_sge(&mut self, _sge: &expr::SignedGreaterEquals, _: VisitEvent) {}

    fn visit_sgt(&mut self, _sgt: &expr::SignedGreaterThan, _: VisitEvent) {}

    fn visit_sle(&mut self, _sle: &expr::SignedLessEquals, _: VisitEvent) {}

    fn visit_slt(&mut self, _slt: &expr::SignedLessThan, _: VisitEvent) {}

    fn visit_uge(&mut self, _uge: &expr::UnsignedGreaterEquals, _: VisitEvent) {}

    fn visit_ugt(&mut self, _ugt: &expr::UnsignedGreaterThan, _: VisitEvent) {}

    fn visit_ule(&mut self, _ule: &expr::UnsignedLessEquals, _: VisitEvent) {}

    fn visit_ult(&mut self, _ult: &expr::UnsignedLessThan, _: VisitEvent) {}

    fn visit_ashr(&mut self, _ashr: &expr::ArithmeticShiftRight, _: VisitEvent) {}

    fn visit_lshr(&mut self, _lshr: &expr::LogicalShiftRight, _: VisitEvent) {}

    fn visit_shl(&mut self, _shl: &expr::ShiftLeft, _: VisitEvent) {}
}

#[cfg(test)]
mod tests {
    use super::*;

    fn new_context_and_builder() -> (ArcContext, PlainExprTreeBuilder) {
        let ctx = Context::arced();
        let builder = PlainExprTreeBuilder::from_context(ctx.clone());
        (ctx, builder)
    }

    mod cond {
        use super::*;

        #[test]
        fn ok() {
            let (ctx, b) = new_context_and_builder();
            let expr = b.cond(
                b.bool_var("a"),
                b.bool_var("b"),
                b.bool_var("c")
            ).unwrap();
            assert!(assert_consistency_recursively(&ctx, &expr).is_ok())
        }

        #[test]
        fn non_bool_cond() {
            let (ctx, b) = new_context_and_builder();
            // Create new correct conditional expression.
            let mut expr = expr::IfThenElse::new(
                b.bool_var("a").unwrap(),
                b.bool_var("b").unwrap(),
                b.bool_var("c").unwrap(),
            ).unwrap();
            // Break the condition type invariant.
            expr.children.cond = b.bitvec_var(BitvecTy::w32(), "x").unwrap();
            assert!(assert_consistency_recursively(&ctx, &AnyExpr::from(expr)).is_err())
        }

        #[test]
        fn non_common_ty_then_else() {
            let (ctx, b) = new_context_and_builder();
            // Create new correct conditional expression.
            let expr = expr::IfThenElse::new(
                b.bool_var("a").unwrap(),
                b.bool_var("b").unwrap(),
                b.bool_var("c").unwrap(),
            ).unwrap();
            {
                let mut expr = expr.clone();
                // Break the then-case type invariant.
                expr.children.then_case = b.bitvec_var(BitvecTy::w32(), "x").unwrap();
                assert!(assert_consistency_recursively(&ctx, &AnyExpr::from(expr)).is_err());
            }
            {
                let mut expr = expr.clone();
                // Break the then-case type invariant.
                expr.children.else_case = b.bitvec_var(BitvecTy::w32(), "x").unwrap();
                assert!(assert_consistency_recursively(&ctx, &AnyExpr::from(expr)).is_err());
            }
        }
    }

    mod symbol {
        use super::*;

        #[test]
        fn ok() {
            let (ctx, b) = new_context_and_builder();
            {
                let bool_symbol = b.bool_var("a").unwrap();
                assert!(assert_consistency_recursively(&ctx, &bool_symbol).is_ok())
            }
            {
                let bitvec_symbol = b.bitvec_var(BitvecTy::w32(), "x").unwrap();
                assert!(assert_consistency_recursively(&ctx, &bitvec_symbol).is_ok())
            }
            {
                let array_symbol = b.array_var(ArrayTy::new(BitvecTy::w32(), BitvecTy::w64()), "A").unwrap();
                assert!(assert_consistency_recursively(&ctx, &array_symbol).is_ok())
            }
        }

        #[test]
        fn invalid_alias() {
            let (ctx1, b1) = new_context_and_builder();
            let (ctx2, b2) = new_context_and_builder();
            let sym1 = b1.bool_var("a").unwrap();
            let sym2 = b2.bitvec_var(BitvecTy::w32(), "a").unwrap();
            assert!(assert_consistency_recursively(&ctx2, &sym1).is_err());
            assert!(assert_consistency_recursively(&ctx1, &sym2).is_err());
        }
    }

    mod bool_equals {
        use super::*;

        #[test]
        fn ok() {
            let (ctx, b) = new_context_and_builder();
            let expr = b.bool_equals(
                b.bool_var("a"),
                b.bool_var("b")
            ).unwrap();
            assert!(assert_consistency_recursively(&ctx, &expr).is_ok());
        }

        #[test]
        fn unexpected_child_ty() {
            let (ctx, b) = new_context_and_builder();
            let mut expr = expr::BoolEquals::binary(
                b.bool_var("a").unwrap(),
                b.bool_var("b").unwrap()
            ).unwrap();
            expr.children.push(b.bitvec_var(BitvecTy::w32(), "x").unwrap());
            assert!(assert_consistency_recursively(&ctx, &AnyExpr::from(expr)).is_err());
        }
    }
}
