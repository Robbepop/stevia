use ast::prelude::*;

use apint::ApInt;

use std::collections::{HashSet, HashMap};
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

/// Checks if there are like-terms that can and should be combined.
/// 
/// Compared to the real merging of like-terms this check is very light-weight
/// and thus should be performed to prevent unneeded expensive computations.
fn has_like_terms<'a>(add: &'a expr::Add) -> bool {
    let mut seen_symbols: HashSet<&'a AnyExpr> = HashSet::new();
    let mut mutated = false;
    let mut update_seen = |expr: &'a AnyExpr| {
        if seen_symbols.contains(expr) {
            mutated = true;
        } else {
            seen_symbols.insert(expr);
        }
    };
    for child in add.childs() {
        match child {
            AnyExpr::Neg(neg) => update_seen(neg.single_child()),
            AnyExpr::Mul(mul) => {
                // TODO: Extend the entire algorithm to work for n-ary multiplication.
                //       For example: `(+ (* 2 x y) (* 4 x y))` is currently not allowed while
                //       it could be theoretically simplified to `(* 6 x y)`.
                if mul.arity() != 2 {
                    continue;
                }
                // Only allow multiplications with exactly one constant part.
                // Otherwise run simplifications until only one constant part remains.
                if mul.childs().filter(|c| c.kind() == ExprKind::BitvecConst).count() != 1 {
                    continue;
                }
                let mut mul_childs = mul.childs();
                let lhs = mul_childs.next().unwrap();
                let rhs = mul_childs.next().unwrap();
                match (lhs, rhs) {
                    (AnyExpr::BitvecConst(_), rhs) => update_seen(rhs),
                    (lhs, AnyExpr::BitvecConst(_)) => update_seen(lhs),
                    _ => ()
                }
            }
            other => update_seen(other)
        }
    }
    mutated
}

fn collect_like_terms(add: expr::Add) -> HashMap<AnyExpr, ApInt> {
    let raw_width = add.bitvec_ty.width().raw_width();
    let mut like_terms: HashMap<AnyExpr, ApInt> = HashMap::new();
    let mut update_seen = |expr: AnyExpr, occurence: ApInt| {
        match like_terms.entry(expr) {
            Entry::Occupied(mut occupied) => {
                occupied.get_mut()
                        .checked_add_assign(&occurence)
                        .unwrap();
            }
            Entry::Vacant(vacant) => {
                vacant.insert(occurence);
            }
        }
    };
    for child in add.into_childs() {
        match child {
            AnyExpr::Neg(neg) => update_seen(neg.into_single_child(), ApInt::all_set(raw_width)),
            AnyExpr::Mul(mul) => {
                if (mul.arity() != 2) || (mul.childs().filter(|c| c.kind() == ExprKind::BitvecConst).count() != 1) {
                    update_seen(mul.into(), ApInt::one(raw_width));
                    continue;
                }
                let mut mul_childs = mul.into_childs();
                let lhs = mul_childs.next().unwrap();
                let rhs = mul_childs.next().unwrap();
                match (lhs, rhs) {
                    (AnyExpr::BitvecConst(lhs), rhs) => update_seen(rhs, lhs.val.clone()),
                    (lhs, AnyExpr::BitvecConst(rhs)) => update_seen(lhs, rhs.val.clone()),
                    _ => unreachable!()
                }
            }
            other => update_seen(other, ApInt::one(raw_width))
        }
    }
    like_terms
}

fn simplify_add(add: expr::Add) -> TransformOutcome {
    if has_like_terms(&add) {

        fn gen_node(bvty: BitvecTy, expr: AnyExpr, occurence: ApInt) -> AnyExpr {
            if occurence.is_zero() {
                return expr::BitvecConst::zero(bvty).into()
            }
            if occurence.is_one() {
                return expr
            }
            if occurence.is_all_set() {
                return expr::Neg::new(expr).unwrap().into()
            }
            expr::Mul::binary(
                expr::BitvecConst::from(occurence),
                expr
            ).unwrap().into()
        }
        let bvty = add.bitvec_ty;
        let like_terms = collect_like_terms(add);
        if like_terms.len() == 0 {
            unreachable!()
        }
        if like_terms.len() == 1 {
            let (expr, occurence) = like_terms.into_iter().next().unwrap();
            return TransformOutcome::transformed(gen_node(bvty, expr, occurence))
        }
        let like_terms = like_terms.into_iter()
                                   .map(|(expr, occurence)| gen_node(bvty, expr, occurence))
                                   .collect::<Vec<_>>();
        return TransformOutcome::transformed(expr::Add::nary(like_terms).unwrap())
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
                    b.bitvec_const(BitvecTy::w32(), 4_i32),
                    b.bitvec_var(BitvecTy::w32(), "x")
                ),
                b.bitvec_mul(
                    b.bitvec_const(BitvecTy::w32(), -2_i32),
                    b.bitvec_var(BitvecTy::w32(), "y")
                )
            )
        )
    }
}
