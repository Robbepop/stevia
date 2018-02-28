use ast::prelude::*;

use apint::ApInt;

pub mod prelude {
    pub use super::TermConstPropagator;
}

/// This simplification procedure propagates constant values through boolean expressions.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct TermConstPropagator;

impl AutoImplAnyTransformer for TermConstPropagator {}

impl Transformer for TermConstPropagator {
    fn transform_add(&self, add: expr::Add) -> TransformOutcome {
        // If all child expressions are constants we can compute the result
        // and simplify the entire add expression to it.
        if add.childs().all(|c| c.get_if_bitvec_const().is_some()) {
            let sum = add.childs()
                .filter_map(|c| c.get_if_bitvec_const())
                .fold(ApInt::zero(add.bitvec_ty.width().raw_width()), |mut acc, n| { acc += n; acc });
            return TransformOutcome::transformed(expr::BitvecConst::from(sum))
        }
        TransformOutcome::identity(add)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simplifier::prelude::*;

    create_modular_ast_transformer! {
        struct TermConstPropagatorTransformer;
        (_0, TermConstPropagator)
    }
    type TermConstPropagatorSimplifier = BaseSimplifier<TermConstPropagatorTransformer>;

    fn create_simplifier() -> TermConstPropagatorSimplifier {
        TermConstPropagatorSimplifier::default()
    }

    fn simplify(expr: &mut AnyExpr) -> TransformEffect {
        create_simplifier().simplify(expr)
    }

    mod add {
        use super::*;

        #[test]
        fn all_const() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_add_n(vec![
                b.bitvec_const(BitvecTy::w32(), 5),
                b.bitvec_const(BitvecTy::w32(), 7),
                b.bitvec_const(BitvecTy::w32(), 3)
            ]).unwrap();
            simplify(&mut expr);
            let expected = b.bitvec_const(BitvecTy::w32(), 15).unwrap();
            assert_eq!(expr, expected);
        }
    }
}
