use ast::prelude::*;

// use either::Either;
// use itertools::Itertools;

pub mod prelude {
    pub use super::{
        ArrayReadIteLifter
    };
}

/// Lifts if-then-else expressions that are childs of array-reads and have
/// an array-write child themself.
/// 
/// This does not increase the size of the AST and is important to constitute
/// array-read and array-write elimination transformations.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ArrayReadIteLifter;

impl AutoImplAnyTransformer for ArrayReadIteLifter {}

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

impl Transformer for ArrayReadIteLifter {
    fn transform_array_read(&self, read: expr::ArrayRead) -> TransformOutcome {
        array_read_ite_lifting(read)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simplifier::prelude::*;

    modular_ast_transformer! {
        struct ArrayReadIteLifterTransformer {
            _0: ArrayReadIteLifter
        }
    }
    type ArrayReadIteLifterSimplifier = BaseSimplifier<ArrayReadIteLifterTransformer>;

    fn create_simplifier() -> ArrayReadIteLifterSimplifier {
        ArrayReadIteLifterSimplifier::default()
    }

    fn simplify(expr: &mut AnyExpr) -> TransformEffect {
        create_simplifier().simplify(expr)
    }

    fn assert_simplified<E1, E2>(input: E1, expected: E2)
        where E1: IntoAnyExprOrError,
              E2: IntoAnyExprOrError
    {
        let mut input = input.into_any_expr_or_error().unwrap();
        let expected = expected.into_any_expr_or_error().unwrap();
        simplify(&mut input);
        assert_eq!(input, expected);
    }

    fn new_builder() -> PlainExprTreeBuilder {
        PlainExprTreeBuilder::default()
    }

    #[test]
    fn simple() {
        let b = new_builder();
        assert_simplified(
            b.array_read(
                b.cond(
                    b.bool_var("cond"),
                    b.array_var(ArrayTy::new(BitvecTy::w32(), BitvecTy::w8()), "arr1"),
                    b.array_var(ArrayTy::new(BitvecTy::w32(), BitvecTy::w8()), "arr2")
                ),
                b.bitvec_var(BitvecTy::w32(), "idx_j")
            ),
            b.cond(
                b.bool_var("cond"),
                b.array_read(
                    b.array_var(ArrayTy::new(BitvecTy::w32(), BitvecTy::w8()), "arr1"),
                    b.bitvec_var(BitvecTy::w32(), "idx_j")
                ),
                b.array_read(
                    b.array_var(ArrayTy::new(BitvecTy::w32(), BitvecTy::w8()), "arr2"),
                    b.bitvec_var(BitvecTy::w32(), "idx_j")
                )
            )
        )
    }

    #[test]
    fn write_in_ite() {
        let b = new_builder();
        assert_simplified(
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
