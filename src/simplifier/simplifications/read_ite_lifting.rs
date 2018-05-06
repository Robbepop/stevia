use ast::prelude::*;

/// Lifts if-then-else expressions that are childs of array-reads and have
/// an array-write child themself.
/// 
/// Note that the current implementation might grow the AST by an exponential
/// factor in the worst case. This can be avoided by inserting indirections that
/// are to be cloned instead of potentially expensive sub-trees of the AST.
/// However, this has yet to be implemented which requires another architectural
/// enhancement on the side of the general simplifier design to allow for
/// post-processing steps.
#[derive(Debug, Clone)]
pub struct ArrayReadIteLifter<'ctx> {
    // ctx: ArcContext
    ctx: &'ctx Context
}

impl<'ctx> From<ArcContext> for ArrayReadIteLifter<'ctx> {
    fn from(_ctx: ArcContext) -> Self {
        // Self{_ctx}
        unimplemented!()
    }
}

impl<'ctx> From<&'ctx Context> for ArrayReadIteLifter<'ctx> {
    fn from(ctx: &'ctx Context) -> Self {
        Self{ ctx: ctx }
    }
}

impl<'ctx> AutoImplAnyExprTransformer for ArrayReadIteLifter<'ctx> {}

fn array_read_ite_lifting(read: expr::ArrayRead) -> TransformOutcome {
    if let box ArrayReadChildren{ index, array: AnyExpr::IfThenElse(ite) } = read.children {
        let (cond, then_case, else_case) = ite.into_children_tuple();
        return TransformOutcome::transformed(
            expr::IfThenElse::new(
                cond,
                expr::ArrayRead::new(
                    then_case,
                    // FIXME: Depending on the depth of the sub-tree behind `index`
                    //        `index.clone()` might be a very expensive operation and
                    //        should be avoided in the general case.
                    index.clone()
                ).unwrap(),
                expr::ArrayRead::new(
                    else_case,
                    index
                ).unwrap(),
            ).unwrap()
        )
    }
    TransformOutcome::identity(read)
}

impl<'ctx> Transformer for ArrayReadIteLifter<'ctx> {
    fn transform_array_read(&self, read: expr::ArrayRead) -> TransformOutcome {
        array_read_ite_lifting(read)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simplifier::prelude::*;

    type ArrayReadIteLifterSimplifier<'ctx> = BaseSimplifier<ArrayReadIteLifter<'ctx>>;

    fn create_simplifier(ctx: &Context) -> ArrayReadIteLifterSimplifier {
        ArrayReadIteLifterSimplifier::from(ctx)
    }

    fn simplify(ctx: &Context, expr: &mut AnyExpr) -> TransformEffect {
        create_simplifier(ctx).simplify(expr)
    }

    fn assert_simplified<E1, E2>(ctx: &Context, input: E1, expected: E2)
        where E1: IntoAnyExprOrError,
              E2: IntoAnyExprOrError
    {
        let mut input = input.into_any_expr_or_error().unwrap();
        let expected = expected.into_any_expr_or_error().unwrap();
        simplify(ctx, &mut input);
        assert_eq!(input, expected);
    }

    fn new_context_and_builder() -> (ArcContext, PlainExprTreeBuilder) {
        let ctx = Context::arced();
        let builder = PlainExprTreeBuilder::from_context(ctx.clone());
        (ctx, builder)
    }

    #[test]
    fn simple() {
        let (ctx, b) = new_context_and_builder();
        assert_simplified(&ctx,
            b.array_read(
                b.cond(
                    b.bool_var("cond"),
                    b.array_var(ArrayTy::new(BitvecTy::w32(), BitvecTy::w8()), "arr1"),
                    b.array_var(ArrayTy::new(BitvecTy::w32(), BitvecTy::w8()), "arr2")
                ),
                b.bitvec_var(BitvecTy::w32(), "idx")
            ),
            b.cond(
                b.bool_var("cond"),
                b.array_read(
                    b.array_var(ArrayTy::new(BitvecTy::w32(), BitvecTy::w8()), "arr1"),
                    b.bitvec_var(BitvecTy::w32(), "idx")
                ),
                b.array_read(
                    b.array_var(ArrayTy::new(BitvecTy::w32(), BitvecTy::w8()), "arr2"),
                    b.bitvec_var(BitvecTy::w32(), "idx")
                )
            )
        )
    }

    #[test]
    fn write_in_ite() {
        let (ctx, b) = new_context_and_builder();
        assert_simplified(&ctx,
            b.array_read(
                b.cond(
                    b.bool_var("cond"),
                    b.array_write(
                        b.array_var(ArrayTy::new(BitvecTy::w32(), BitvecTy::w8()), "arr1"),
                        b.bitvec_var(BitvecTy::w32(), "idx_i"),
                        b.bitvec_var(BitvecTy::w8(), "val")
                    ),
                    b.array_var(ArrayTy::new(BitvecTy::w32(), BitvecTy::w8()), "arr2")
                ),
                b.bitvec_var(BitvecTy::w32(), "idx_j")
            ),
            b.cond(
                b.bool_var("cond"),
                b.array_read(
                    b.array_write(
                        b.array_var(ArrayTy::new(BitvecTy::w32(), BitvecTy::w8()), "arr1"),
                        b.bitvec_var(BitvecTy::w32(), "idx_i"),
                        b.bitvec_var(BitvecTy::w8(), "val")
                    ),
                    b.bitvec_var(BitvecTy::w32(), "idx_j")
                ),
                b.array_read(
                    b.array_var(ArrayTy::new(BitvecTy::w32(), BitvecTy::w8()), "arr2"),
                    b.bitvec_var(BitvecTy::w32(), "idx_j")
                )
            )
        )
    }
}
