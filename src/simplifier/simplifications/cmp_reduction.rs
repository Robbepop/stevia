use ast::prelude::*;

/// Reduces this `SignedGreaterEquals` to using less-than as only comparison.
fn reduce_sge_to_slt(sge: expr::SignedGreaterEquals) -> expr::Not {
    unsafe{ expr::SignedLessThan::from_raw_parts(sge.children_bitvec_ty, sge.children) }.wrap_with_not()
}

/// Reduces this `SignedLessThan` to using less-than as only comparison.
fn reduce_sgt_to_slt(sgt: expr::SignedGreaterThan) -> expr::SignedLessThan {
    let mut sgt = sgt;
    sgt.children.swap_children();
    unsafe{ expr::SignedLessThan::from_raw_parts(sgt.children_bitvec_ty, sgt.children) }
}

/// Creates a new `SignedLessEquals` expression from the given `SignedGreaterThan`.
fn reduce_sle_to_slt(sle: expr::SignedLessEquals) -> expr::Not {
    let mut sle = sle;
    sle.children.swap_children();
    unsafe{ expr::SignedLessThan::from_raw_parts(sle.children_bitvec_ty, sle.children).wrap_with_not() }
}

/// Reduces this `UnsignedGreaterEquals` to using less-than as only comparison.
fn reduce_uge_to_ult(uge: expr::UnsignedGreaterEquals) -> expr::Not {
    unsafe{ expr::UnsignedLessThan::from_raw_parts(uge.children_bitvec_ty, uge.children) }.wrap_with_not()
}

/// Reduces this `UnsignedLessThan` to using less-than as only comparison.
fn reduce_ugt_to_ult(ugt: expr::UnsignedGreaterThan) -> expr::UnsignedLessThan {
    let mut ugt = ugt;
    ugt.children.swap_children();
    unsafe{ expr::UnsignedLessThan::from_raw_parts(ugt.children_bitvec_ty, ugt.children) }
}

/// Creates a new `UnsignedLessEquals` expression from the given `SignedGreaterThan`.
fn reduce_ule_to_ult(ule: expr::UnsignedLessEquals) -> expr::Not {
    let mut ule = ule;
    ule.children.swap_children();
    unsafe{ expr::UnsignedLessThan::from_raw_parts(ule.children_bitvec_ty, ule.children).wrap_with_not() }
}

/// Reduces comparison expressions to less-than forms.
/// 
/// # Examples
/// 
/// - `a > b` is simplified to `b < a`
/// - `a >= b` is simplified to `not(a < b)`
/// - `a <= b` is simplified to `not(b < a)`
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ComparisonReducer;

impl AutoImplAnyExprTransformer for ComparisonReducer {}

impl Transformer for ComparisonReducer {
    fn transform_sge(&self, sge: expr::SignedGreaterEquals) -> TransformOutcome {
        TransformOutcome::transformed(reduce_sge_to_slt(sge))
    }

    fn transform_sgt(&self, sgt: expr::SignedGreaterThan) -> TransformOutcome {
        TransformOutcome::transformed(reduce_sgt_to_slt(sgt))
    }

    fn transform_sle(&self, sle: expr::SignedLessEquals) -> TransformOutcome {
        TransformOutcome::transformed(reduce_sle_to_slt(sle))
    }

    fn transform_uge(&self, uge: expr::UnsignedGreaterEquals) -> TransformOutcome {
        TransformOutcome::transformed(reduce_uge_to_ult(uge))
    }

    fn transform_ugt(&self, ugt: expr::UnsignedGreaterThan) -> TransformOutcome {
        TransformOutcome::transformed(reduce_ugt_to_ult(ugt))
    }

    fn transform_ule(&self, ule: expr::UnsignedLessEquals) -> TransformOutcome {
        TransformOutcome::transformed(reduce_ule_to_ult(ule))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simplifier::prelude::*;

    modular_ast_transformer! {
        struct ComparisonReducerTransformer {
            _0: ComparisonReducer
        }
    }
    type ComparisonReducerSimplifier = BaseSimplifier<ComparisonReducerTransformer>;

    fn create_simplifier() -> ComparisonReducerSimplifier {
        ComparisonReducerSimplifier::default()
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
    fn sge() {
        let b = new_builder();
        assert_simplified(
            b.bitvec_sge(
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_var(BitvecTy::w32(), "y")
            ),
            b.not(
                b.bitvec_slt(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "y")
                )
            )
        )
    }

    #[test]
    fn uge() {
        let b = new_builder();
        assert_simplified(
            b.bitvec_uge(
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_var(BitvecTy::w32(), "y")
            ),
            b.not(
                b.bitvec_ult(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "y")
                )
            )
        )
    }

    #[test]
    fn sgt() {
        let b = new_builder();
        assert_simplified(
            b.bitvec_sgt(
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_var(BitvecTy::w32(), "y")
            ),
            b.bitvec_slt(
                b.bitvec_var(BitvecTy::w32(), "y"),
                b.bitvec_var(BitvecTy::w32(), "x")
            )
        )
    }

    #[test]
    fn ugt() {
        let b = new_builder();
        assert_simplified(
            b.bitvec_ugt(
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_var(BitvecTy::w32(), "y")
            ),
            b.bitvec_ult(
                b.bitvec_var(BitvecTy::w32(), "y"),
                b.bitvec_var(BitvecTy::w32(), "x")
            )
        )
    }

    #[test]
    fn sle() {
        let b = new_builder();
        assert_simplified(
            b.bitvec_sle(
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_var(BitvecTy::w32(), "y")
            ),
            b.not(
                b.bitvec_slt(
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_var(BitvecTy::w32(), "x")
                )
            )
        )
    }

    #[test]
    fn ule() {
        let b = new_builder();
        assert_simplified(
            b.bitvec_ule(
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_var(BitvecTy::w32(), "y")
            ),
            b.not(
                b.bitvec_ult(
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_var(BitvecTy::w32(), "x")
                )
            )
        )
    }
}
