use ast::prelude::*;

use apint::ApInt;
use itertools::Itertools;

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use either::Either;

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

fn has_like_terms(add: &expr::Add) -> bool {
    let width = add.bitvec_ty.width();
    let mut seen_symbols: HashMap<&AnyExpr, ApInt> = HashMap::new();
    let mut mutated = false;
    let (negs, rest): (Vec<_>, Vec<_>) = add.childs().partition_map(|c| {
        match c {
            AnyExpr::Neg(neg) => Either::Left(neg),
            other             => Either::Right(other)
        }
    });
    let (muls, rest): (Vec<_>, Vec<_>) = rest.into_iter().partition_map(|c| {
        match c {
            AnyExpr::Mul(mul) => Either::Left(mul),
            other             => Either::Right(other)
        }
    });
    for child in rest {
        match seen_symbols.entry(child) {
            Entry::Occupied(mut occupied) => {
                occupied.get_mut()
                        .checked_add_assign(
                            &ApInt::one(width.raw_width())).unwrap();
                mutated = true;
            }
            Entry::Vacant(vacant) => {
                vacant.insert(ApInt::one(width.raw_width()));
            }
        }
    }
    for neg in negs {
        match seen_symbols.entry(neg.single_child()) {
            Entry::Occupied(mut occupied) => {
                occupied.get_mut()
                        .checked_add_assign(
                            // `ApInt::all_set` behaves as if it was -1 in twos-complement
                            &ApInt::all_set(width.raw_width())).unwrap();
                mutated = true;
            }
            Entry::Vacant(vacant) => {
                vacant.insert(ApInt::all_set(width.raw_width()));
            }
        }
    }
    for mul in muls {
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
            (AnyExpr::BitvecConst(lhs), rhs) => {
                match seen_symbols.entry(rhs) {
                    Entry::Occupied(mut occupied) => {
                        occupied.get_mut()
                                .checked_add_assign(&lhs.val).unwrap();
                        mutated = true;
                    }
                    Entry::Vacant(vacant) => {
                        vacant.insert(lhs.val.clone());
                    }
                }
            }
            (lhs, AnyExpr::BitvecConst(rhs)) => {
                match seen_symbols.entry(lhs) {
                    Entry::Occupied(mut occupied) => {
                        occupied.get_mut()
                                .checked_add_assign(&rhs.val).unwrap();
                        mutated = true;
                    }
                    Entry::Vacant(vacant) => {
                        vacant.insert(rhs.val.clone());
                    }
                }
            }
            _ => ()
        }
    }
    return mutated;
}

fn simplify_add(add: expr::Add) -> TransformOutcome {
    if has_like_terms(&add) {
        // let (mut eqs, mut rest): (Vec<_>, Vec<_>) = and.into_childs().partition_map(|c| {
        //     match c {
        //         AnyExpr::$eq_type(eq) => Either::Left(eq),
        //         other                 => Either::Right(other)
        //     }
        // });
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
