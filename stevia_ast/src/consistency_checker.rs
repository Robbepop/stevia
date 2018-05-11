use crate::prelude::*;

pub trait AssertConsistency {
    /// Asserts the consistency of `self`.
    ///
    /// # Errors
    ///
    /// If `self` is not consistent in itself in association
    /// with the given context.
    fn assert_consistency(&self, ctx: &Context) -> ExprResult<()>;
}

impl AssertConsistency for expr::ArrayRead {
    fn assert_consistency(&self, _: &Context) -> ExprResult<()> {
        let array_ty = expect_array_ty(&self.children.array)
            .map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(format!(
                    "Expected the left hand-side expression of the {:?} \
                    expression to be of array type.",
                    self.kind().camel_name()
                ))
            })?;
        expect_type(array_ty.index_ty(), &self.children.index)
            .map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(format!(
                    "Expected the right hand-side expression of the {:?} \
                    expression to be of the same bitvector type as the index-type \
                    of the left hand-side array expression.",
                    self.kind().camel_name()
                ))
            })
    }
}

impl AssertConsistency for expr::ArrayWrite {
    fn assert_consistency(&self, _: &Context) -> ExprResult<()> {
        let array_ty = expect_array_ty(&self.children.array)
            .map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(format!(
                    "Expected the array (left hand-side) expression of the {:?} \
                    expression to be of array type.",
                    self.kind().camel_name()
                ))
            })?;
        expect_type(array_ty.index_ty(), &self.children.index)
            .map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(format!(
                    "Expected the index (middle) expression of the {:?} \
                    expression to be of the same bitvector type as the index-type \
                    of the left hand-side array expression.",
                    self.kind().camel_name()
                ))
            })?;
        expect_type(array_ty.value_ty(), &self.children.value)
            .map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(format!(
                    "Expected the value (right hand-side) expression of the {:?} \
                    expression to be of the same bitvector type as the value-type \
                    of the left hand-side array expression.",
                    self.kind().camel_name()
                ))
            })
    }
}

impl AssertConsistency for expr::Not {
    fn assert_consistency(&self, _: &Context) -> ExprResult<()> {
        error::expr_expect_type(Type::Bool, &*self.child)
    }
}

impl AssertConsistency for expr::Neg {
    fn assert_consistency(&self, _: &Context) -> ExprResult<()> {
        error::expr_expect_type(self.ty(), &*self.child)
    }
}

impl AssertConsistency for expr::BitNot {
    fn assert_consistency(&self, _: &Context) -> ExprResult<()> {
        error::expr_expect_type(self.ty(), &*self.child)
    }
}

impl<M> AssertConsistency for ExtendExpr<M>
where
    M: ExprMarker,
    ExtendExpr<M>: Into<AnyExtendExpr>
{
    fn assert_consistency(&self, _: &Context) -> ExprResult<()> {
        let target_bvty = self.bitvec_ty;
        let src_bvty = expect_bitvec_ty(&*self.src)
            .map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(format!(
                    "Expected bitvector expression for the child expression of this {:?} expression.\
                    Encountered in expression: {:?}",
                    self.kind().camel_name(),
                    self
                ))
            })?;
        if target_bvty.width() < src_bvty.width() {
            return Err(CastError::extend_to_smaller(src_bvty, self.clone()).into())
        }
        Ok(())
    }
}

impl AssertConsistency for expr::Concat {
    fn assert_consistency(&self, _: &Context) -> ExprResult<()> {
        let bvty = self.bitvec_ty;

        let lhs_bvty = expect_bitvec_ty(&self.children.lhs)
            .map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(format!(
                    "Expected bitvector type for the left hand-side child expression of this {:?} \
                    expression: {:?}",
                    self.kind().camel_name(),
                    self
                ))
            })?;
        let rhs_bvty = expect_bitvec_ty(&self.children.rhs)
            .map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(format!(
                    "Expected bitvector type for the right hand-side child expression of this {:?} \
                    expression: {:?}",
                    self.kind().camel_name(),
                    self
                ))
            })?;
        let concat_bvty = BitvecTy::from(lhs_bvty.width().len_bits() + rhs_bvty.width().len_bits());
        if bvty != concat_bvty {
            return error::expr_expect_type(concat_bvty, self)
                .map_err(ExprError::from)
                .map_err(|e| {
                    e.context_msg(format!(
                        "Expect the concatenation of bitvectors with bit-widths of {:?} and {:?} to be of bit-width {:?}.",
                        lhs_bvty,
                        rhs_bvty,
                        concat_bvty
                    ))
                })
        }
        Ok(())
    }
}

impl AssertConsistency for expr::Extract {
    fn assert_consistency(&self, _: &Context) -> ExprResult<()> {
        let src_width = expect_bitvec_ty(&*self.src)
            .map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(
                    "Encountered non-bitvector type for the child expression of an Extract expression.",
                )
            })?;
        if self.lo >= self.hi {
            return Err(CastError::extract_lo_greater_equal_hi(self.clone()).into());
        }
        if BitvecTy::from(self.hi) > src_width {
            return Err(CastError::extract_hi_overflow(self.clone()).into());
        }
        Ok(())
    }
}

impl AssertConsistency for expr::IfThenElse {
    fn assert_consistency(&self, _: &Context) -> ExprResult<()> {
        expect_type(Type::Bool, &self.children.cond)
            .map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg("The condition of an if-then-else expression must be of boolean type.")
            })?;
        expect_common_ty(&self.children.then_case, &self.children.else_case)
            .map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(
                "The types of the then-case and else-case of an if-then-else expression must be the same.")
            })?;
        Ok(())
    }
}

impl AssertConsistency for expr::BoolConst {
    fn assert_consistency(&self, _: &Context) -> ExprResult<()> {
        Ok(())
    }
}

impl AssertConsistency for expr::BitvecConst {
    fn assert_consistency(&self, _: &Context) -> ExprResult<()> {
        Ok(())
    }
}

impl AssertConsistency for expr::Symbol {
    fn assert_consistency(&self, ctx: &Context) -> ExprResult<()> {
        if let SymbolId::Named(named) = self.id {
            let assoc_ty = ctx.symbol_types.get(named).expect(
                "Expected to have an associated type to this named symbol. \
                 Maybe the wrong context is in used?",
            );
            if assoc_ty != self.ty() {
                return Err(ExprError::unmatching_symbol_types(
                    assoc_ty, self.ty(), named
                ));
            }
        }
        Ok(())
    }
}

impl<M> AssertConsistency for BinBoolExpr<M>
where
    M: ExprMarker,
{
    fn assert_consistency(&self, _: &Context) -> ExprResult<()> {
        error::expr_expect_type(Type::Bool, self.lhs_child()).map_err(|e| {
            e.context_msg(format!(
                "Expected boolean type for the left hand-side expression of this {:?} expression: {:?}",
                self.kind().camel_name(),
                self
            ))
        })?;
        error::expr_expect_type(Type::Bool, self.rhs_child()).map_err(|e| {
            e.context_msg(format!(
                "Expected boolean type for the right hand-side expression of this {:?} expression: {:?}",
                self.kind().camel_name(),
                self)
            )
        })
    }
}

impl<M> AssertConsistency for BinTermExpr<M>
where
    M: ExprMarker,
{
    fn assert_consistency(&self, _: &Context) -> ExprResult<()> {
        let expected_ty = self.ty();
        error::expr_expect_type(expected_ty, self.lhs_child()).map_err(|e| {
            e.context_msg(format!(
                "Expected concrete type (= {:?}) for the left hand-side expression of this {:?} expression: {:?}",
                expected_ty,
                self.kind().camel_name(),
                self)
            )
        })?;
        error::expr_expect_type(expected_ty, self.rhs_child()).map_err(|e| {
            e.context_msg(format!(
                "Expected concrete type (= {:?}) for the right hand-side expression of this {:?} expression: {:?}",
                expected_ty,
                self.kind().camel_name(),
                self)
            )
        })
    }
}

impl AssertConsistency for expr::BitvecEquals {
    fn assert_consistency(&self, _: &Context) -> ExprResult<()> {
        error::expr_expect_min_arity(2, self)?;
        error::expr_expect_type_n(self.children_bitvec_ty, self)
    }
}

impl<M> AssertConsistency for NaryBoolExpr<M>
where
    M: ExprMarker,
    NaryBoolExpr<M>: Into<AnyExpr>,
{
    fn assert_consistency(&self, _: &Context) -> ExprResult<()> {
        error::expr_expect_min_arity(2, self)?;
        error::expr_expect_type_n(Type::Bool, self)
    }
}

impl<M> AssertConsistency for NaryTermExpr<M>
where
    M: ExprMarker,
    NaryTermExpr<M>: Into<AnyExpr>,
{
    fn assert_consistency(&self, _: &Context) -> ExprResult<()> {
        error::expr_expect_min_arity(2, self)?;
        error::expr_expect_type_n(self.ty(), self)
    }
}

impl<M> AssertConsistency for ComparisonExpr<M>
where
    M: ExprMarker,
    ComparisonExpr<M>: Into<AnyExpr>,
{
    fn assert_consistency(&self, _: &Context) -> ExprResult<()> {
        error::expr_expect_type(Type::Bool, self)?;
        let bvty = expect_bitvec_ty(self.lhs_child())?;
        error::expr_expect_type(bvty, self.rhs_child())
    }
}

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
pub fn assert_consistency_recursively<'ctx, 'e, E>(
    ctx: &'ctx Context,
    expr: E,
) -> Result<(), Vec<ExprError>>
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
    ctx: &'ctx Context,
}

impl<'ctx> ConsistencyChecker<'ctx> {
    /// Creates a new consistency checker for the given context.
    pub fn new(ctx: &'ctx Context) -> Self {
        Self {
            found_errors: vec![],
            ctx,
        }
    }
}

impl<'ctx> Visitor for ConsistencyChecker<'ctx> {
    fn visit_any_expr(&mut self, expr: &AnyExpr, event: VisitEvent) {
        if event != VisitEvent::Leaving {
            return;
        }
        if let Err(err) = expr.assert_consistency(&self.ctx) {
            self.found_errors.push(err)
        }
    }
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
            let expr = b.cond(b.bool_var("a"), b.bool_var("b"), b.bool_var("c"))
                .unwrap();
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
                let array_symbol = b.array_var(ArrayTy::new(BitvecTy::w32(), BitvecTy::w64()), "A")
                    .unwrap();
                assert!(assert_consistency_recursively(&ctx, &array_symbol).is_ok())
            }
        }

        #[test]
        fn generated_symbol() {
            let (ctx, _) = new_context_and_builder();
            let gensym = expr::Symbol::new_unnamed(&ctx, Type::Bool);
            assert!(assert_consistency_recursively(&ctx, &AnyExpr::from(gensym)).is_ok())
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

    macro_rules! gen_bool_nary_expr_impl {
        ($mod_name:ident, $build_name:ident, $ty_name:ident) => {
            mod $mod_name {
                use super::*;

                #[test]
                fn ok() {
                    let (ctx, b) = new_context_and_builder();
                    let expr = b.$build_name(b.bool_var("a"), b.bool_var("b")).unwrap();
                    assert!(assert_consistency_recursively(&ctx, &expr).is_ok());
                }

                #[test]
                fn too_few_children() {
                    let (ctx, b) = new_context_and_builder();
                    let mut expr =
                        expr::$ty_name::binary(b.bool_var("a").unwrap(), b.bool_var("b").unwrap())
                            .unwrap();
                    expr.children.pop();
                    assert!(assert_consistency_recursively(&ctx, &AnyExpr::from(expr)).is_err());
                }

                #[test]
                fn unexpected_child_ty() {
                    let (ctx, b) = new_context_and_builder();
                    let mut expr =
                        expr::$ty_name::binary(b.bool_var("a").unwrap(), b.bool_var("b").unwrap())
                            .unwrap();
                    expr.children
                        .push(b.bitvec_var(BitvecTy::w32(), "x").unwrap());
                    assert!(assert_consistency_recursively(&ctx, &AnyExpr::from(expr)).is_err());
                }
            }
        };
    }

    gen_bool_nary_expr_impl!(bool_equals, bool_equals, BoolEquals);
    gen_bool_nary_expr_impl!(and, and, And);
    gen_bool_nary_expr_impl!(or, or, Or);

    macro_rules! gen_bitvec_nary_expr_impl {
        ($mod_name:ident, $build_name:ident, $ty_name:ident) => {
            mod $mod_name {
                use super::*;

                #[test]
                fn ok() {
                    let (ctx, b) = new_context_and_builder();
                    let expr = b.$build_name(
                        b.bitvec_var(BitvecTy::w32(), "x"),
                        b.bitvec_var(BitvecTy::w32(), "y"),
                    ).unwrap();
                    assert!(assert_consistency_recursively(&ctx, &expr).is_ok());
                }

                #[test]
                fn too_few_children() {
                    let (ctx, b) = new_context_and_builder();
                    let mut expr = expr::$ty_name::binary(
                        b.bitvec_var(BitvecTy::w32(), "x").unwrap(),
                        b.bitvec_var(BitvecTy::w32(), "y").unwrap(),
                    ).unwrap();
                    expr.children.pop();
                    assert!(assert_consistency_recursively(&ctx, &AnyExpr::from(expr)).is_err());
                }

                #[test]
                fn unexpected_child_ty() {
                    let (ctx, b) = new_context_and_builder();
                    let mut expr = expr::$ty_name::binary(
                        b.bitvec_var(BitvecTy::w32(), "x").unwrap(),
                        b.bitvec_var(BitvecTy::w32(), "y").unwrap(),
                    ).unwrap();
                    expr.children.push(b.bool_var("a").unwrap());
                    assert!(assert_consistency_recursively(&ctx, &AnyExpr::from(expr)).is_err());
                }
            }
        };
    }

    gen_bitvec_nary_expr_impl!(bitvec_add, bitvec_add, Add);
    gen_bitvec_nary_expr_impl!(bitvec_mul, bitvec_mul, Mul);
    gen_bitvec_nary_expr_impl!(bitvec_and, bitvec_and, BitAnd);
    gen_bitvec_nary_expr_impl!(bitvec_or, bitvec_or, BitOr);

    macro_rules! gen_bool_bin_expr_impl {
        ($mod_name:ident, $builder_name:ident, $ty_name:ident) => {
            mod $mod_name {
                use super::*;

                #[test]
                fn ok() {
                    let (ctx, b) = new_context_and_builder();
                    let bin_expr = b.$builder_name(b.bool_var("a"), b.bool_var("b")).unwrap();
                    assert!(assert_consistency_recursively(&ctx, &bin_expr).is_ok())
                }

                #[test]
                fn invalid_lhs() {
                    let (ctx, b) = new_context_and_builder();
                    let mut bin_expr =
                        expr::$ty_name::new(b.bool_var("a").unwrap(), b.bool_var("b").unwrap())
                            .unwrap();
                    bin_expr.children.lhs = b.bitvec_var(BitvecTy::w32(), "x").unwrap();
                    assert!(assert_consistency_recursively(&ctx, &AnyExpr::from(bin_expr)).is_err())
                }

                #[test]
                fn invalid_rhs() {
                    let (ctx, b) = new_context_and_builder();
                    let mut bin_expr =
                        expr::$ty_name::new(b.bool_var("a").unwrap(), b.bool_var("b").unwrap())
                            .unwrap();
                    bin_expr.children.rhs = b.bitvec_var(BitvecTy::w32(), "x").unwrap();
                    assert!(assert_consistency_recursively(&ctx, &AnyExpr::from(bin_expr)).is_err())
                }
            }
        };
    }

    gen_bool_bin_expr_impl!(xor, xor, Xor);
    gen_bool_bin_expr_impl!(implies, implies, Implies);

    macro_rules! gen_comparison_impl {
        ($mod_name:ident, $builder_name:ident, $ty_name:ident) => {
            mod $mod_name {
                use super::*;

                #[test]
                fn ok() {
                    let (ctx, b) = new_context_and_builder();
                    let cmp = b.$builder_name(
                        b.bitvec_var(BitvecTy::w32(), "x"),
                        b.bitvec_var(BitvecTy::w32(), "y"),
                    ).unwrap();
                    assert!(assert_consistency_recursively(&ctx, &cmp).is_ok())
                }

                #[test]
                fn unmatching_bitvecs() {
                    let (ctx, b) = new_context_and_builder();
                    let mut cmp = expr::$ty_name::new(
                        b.bitvec_var(BitvecTy::w32(), "x").unwrap(),
                        b.bitvec_var(BitvecTy::w32(), "y").unwrap(),
                    ).unwrap();
                    cmp.children.rhs = b.bitvec_var(BitvecTy::w64(), "y64").unwrap();
                    assert!(assert_consistency_recursively(&ctx, &AnyExpr::from(cmp)).is_err())
                }

                #[test]
                fn bool_lhs() {
                    let (ctx, b) = new_context_and_builder();
                    let mut cmp = expr::$ty_name::new(
                        b.bitvec_var(BitvecTy::w32(), "x").unwrap(),
                        b.bitvec_var(BitvecTy::w32(), "y").unwrap(),
                    ).unwrap();
                    cmp.children.lhs = b.bool_var("a").unwrap();
                    assert!(assert_consistency_recursively(&ctx, &AnyExpr::from(cmp)).is_err())
                }
            }
        };
    }

    gen_comparison_impl!(sle, bitvec_sle, SignedLessEquals);
    gen_comparison_impl!(slt, bitvec_slt, SignedLessThan);
    gen_comparison_impl!(sge, bitvec_sge, SignedGreaterEquals);
    gen_comparison_impl!(sgt, bitvec_sgt, SignedGreaterThan);

    gen_comparison_impl!(ule, bitvec_ule, UnsignedLessEquals);
    gen_comparison_impl!(ult, bitvec_ult, UnsignedLessThan);
    gen_comparison_impl!(uge, bitvec_uge, UnsignedGreaterEquals);
    gen_comparison_impl!(ugt, bitvec_ugt, UnsignedGreaterThan);
}
