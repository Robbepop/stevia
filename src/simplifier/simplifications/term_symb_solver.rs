use ast::prelude::*;

use apint::ApInt;

use std::collections::HashMap;
use std::collections::hash_map::Entry;

pub mod prelude {
    pub use super::TermSymbolicSolver;
}

/// This simplification procedure dissolves term expressions with symbolic simplifications.
/// 
/// This works best if used after an expression normalization transformation and
/// might be expensive for deeply nested expression trees that have many similarities.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct TermSymbolicSolver;

impl AutoImplAnyTransformer for TermSymbolicSolver {}

fn has_like_terms<'a>(add: &'a expr::Add) -> bool {
    let raw_width = add.bitvec_ty.width().raw_width();
    let mut seen_symbols: HashMap<&'a AnyExpr, ApInt> = HashMap::new();
    let mut mutated = false;
    let mut update_seen = |expr: &'a AnyExpr, occurence: ApInt| {
        match seen_symbols.entry(expr) {
            Entry::Occupied(mut occupied) => {
                occupied.get_mut()
                        .checked_add_assign(&occurence).unwrap();
                mutated = true;
            }
            Entry::Vacant(vacant) => {
                vacant.insert(occurence);
            }
        }
    };
    for child in add.childs() {
        match child {
            AnyExpr::Neg(neg) => update_seen(neg.single_child(), ApInt::all_set(raw_width)),
            AnyExpr::Mul(mul) => {
                if mul.arity() != 2 {
                    continue;
                }
                if mul.childs().filter(|c| c.kind() == ExprKind::BitvecConst).count() != 1 {
                    continue;
                }
                let mut mul_childs = mul.childs();
                let lhs = mul_childs.next().unwrap();
                let rhs = mul_childs.next().unwrap();
                match (lhs, rhs) {
                    (AnyExpr::BitvecConst(lhs), rhs) => update_seen(rhs, lhs.val.clone()),
                    (lhs, AnyExpr::BitvecConst(rhs)) => update_seen(lhs, rhs.val.clone()),
                    _ => ()
                }
            }
            other => update_seen(other, ApInt::one(raw_width))
        }
    }
    mutated
}

fn simplify_add(add: expr::Add) -> TransformOutcome {
    if has_like_terms(&add) {
        unimplemented!()
    }
    TransformOutcome::identity(add)
}

impl Transformer for TermSymbolicSolver {
    fn transform_add(&self, add: expr::Add) -> TransformOutcome {
        simplify_add(add)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simplifier::prelude::*;

    create_modular_ast_transformer! {
        struct TermSymbolicSolverTransformer;
        (_0, TermSymbolicSolver)
    }
    type TermSymbolicSolverSimplifier = BaseSimplifier<TermSymbolicSolverTransformer>;

    fn create_simplifier() -> TermSymbolicSolverSimplifier {
        TermSymbolicSolverSimplifier::default()
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
    #[ignore]
    fn complex() {
        let b = new_builder();
        assert_simplified(
            b.bitvec_add_n(vec![
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_neg(b.bitvec_var(BitvecTy::w32(), "x")),
                b.bitvec_mul(
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_const(BitvecTy::w32(), -3_i32)
                ),
                b.bitvec_var(BitvecTy::w32(), "y"),
                b.bitvec_mul(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 5_i32)
                ),
                b.bitvec_neg(b.bitvec_var(BitvecTy::w32(), "x"))
            ]),
            b.bitvec_add(
                b.bitvec_mul(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 4_i32)
                ),
                b.bitvec_mul(
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_const(BitvecTy::w32(), -2_i32)
                ),
            )
        )
    }
}
