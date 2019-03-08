use crate::ast::prelude::*;

use crate::simplifications::Normalizer;

use std::collections::{HashSet, HashMap};
use std::collections::hash_map::Entry;

modular_ast_transformer! {
    /// This simplification identifies and joins like-terms in additive expressions.
    /// 
    /// Besides merging of like-terms this also simplifies terms like `(+ a (-a))` to `0`
    /// during the process and other similar processing.
    /// 
    /// Internally it depends on separating non-const children of multiplications from their
    /// only constant child expression. This may leave the resulting binary multiplication in 
    /// an unnormalized state thus also requiring an additional normalization preprocessing
    /// befor actually identifying and merging like-terms.
    #[derive(Default, Copy, PartialEq, Eq, Hash)]
    struct LikeTermJoiner {
        _0: MulConstSeperator,
        _1: Normalizer,
        _2: LikeTermMerger
    }
}

/// This simplification separates a single constant element within a multiplication
/// from the rest of the elements thus resulting in a binary top-level multiplication.
/// 
/// This is required as a pre-processing step for the `LikeTermMerger` in order to
/// identify non-binary multiplications that are like-term mergable.
/// 
/// This won't recurse since the child-level multiplication won't have any constant
/// values.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct MulConstSeperator;

impl<'ctx> From<&'ctx Context> for MulConstSeperator {
    fn from(_: &'ctx Context) -> Self {
        Self::default()
    }
}

impl AutoImplAnyExprTransformer for MulConstSeperator {}

/// Deflattens n-ary multiplications with exactly one constant value into their
/// constant part and the remaining elements.
/// 
/// This structural invariant is used in like-term detection and merging to merge n-ary multiplications.
/// 
/// The resulting multiplication (and its child elements) may be unnormalized after
/// this operation. An additional normalization step is important if following operations
/// depend on that structural invariant.
fn separate_const_from_mul(mul: expr::Mul) -> TransformOutcome {
    // Nothing to do for binary multiplications.
    //
    // Invariant: Arities lower than 2 are invalid for multiplication.
    if mul.arity() == 2 {
        return TransformOutcome::identity(mul)
    }
    // Nothing to do for multiplications that do not have exactly a single constant value.
    if mul.children().filter(|c| c.kind() == ExprKind::BitvecConst).count() != 1 {
        return TransformOutcome::identity(mul)
    }
    // Pop the only constant value from the mul and create a wrapping binary
    // multiplication for the popped constant and the remaining multiplication.
    let mut mul = mul;
    let const_val = mul.children.swap_remove(
        mul.children().position(|c| c.kind() == ExprKind::BitvecConst).unwrap());
    let result = expr::Mul::binary(const_val, mul).unwrap();
    TransformOutcome::transformed(result)
}

impl Transformer for MulConstSeperator {
    fn transform_mul(&self, mul: expr::Mul) -> TransformOutcome {
        separate_const_from_mul(mul)
    }
}

/// This simplification procedure detects and merges like-term expressions.
/// 
/// For optimal results this heavily depends on preprocessing its input by
/// the `MulConstSeparator` for identifying non-binary multiplications for like-term
/// merging which requires an additional normalization step in between.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct LikeTermMerger;

impl<'ctx> From<&'ctx Context> for LikeTermMerger {
    fn from(_: &'ctx Context) -> Self {
        Self::default()
    }
}

impl AutoImplAnyExprTransformer for LikeTermMerger {}

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
    for child in add.children() {
        match child {
            AnyExpr::Neg(neg) => update_seen(neg.single_child()),
            // TODO: Extend the entire algorithm to work for n-ary multiplication.
            //       For example: `(+ (* 2 x y) (* 4 x y))` is currently not allowed while
            //       it could be theoretically simplified to `(* 6 x y)`.
            AnyExpr::Mul(mul) if (mul.arity() == 2)
                              && (mul.children().filter(|c| c.kind() == ExprKind::BitvecConst).count() == 1) => {
                let mut mul_children = mul.children();
                let lhs = mul_children.next().unwrap();
                let rhs = mul_children.next().unwrap();
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

fn collect_like_terms(add: expr::Add) -> HashMap<AnyExpr, Bitvec> {
    let width = add.bitvec_ty.width();
    let mut like_terms: HashMap<AnyExpr, Bitvec> = HashMap::new();
    let mut update_seen = |expr: AnyExpr, occurence: Bitvec| {
        match like_terms.entry(expr) {
            Entry::Occupied(mut occupied) => {
                occupied.get_mut()
                        .add_mut(&occurence)
                        .unwrap();
            }
            Entry::Vacant(vacant) => {
                vacant.insert(occurence);
            }
        }
    };
    for child in add.into_children() {
        match child {
            AnyExpr::Neg(neg) => update_seen(neg.into_single_child(), Bitvec::all_set(width)),
            AnyExpr::Mul(mul) => {
                if (mul.arity() != 2) || (mul.children().filter(|c| c.kind() == ExprKind::BitvecConst).count() != 1) {
                    update_seen(mul.into(), Bitvec::one(width));
                    continue;
                }
                let mut mul_children = mul.into_children();
                let lhs = mul_children.next().unwrap();
                let rhs = mul_children.next().unwrap();
                match (lhs, rhs) {
                    (AnyExpr::BitvecConst(lhs), rhs) => update_seen(rhs, lhs.val.clone()),
                    (lhs, AnyExpr::BitvecConst(rhs)) => update_seen(lhs, rhs.val.clone()),
                    _ => unreachable!()
                }
            }
            other => update_seen(other, Bitvec::one(width))
        }
    }
    like_terms
}

fn simplify_add(add: expr::Add) -> TransformOutcome {
    if has_like_terms(&add) {
        fn gen_node(bvty: BitvecTy, expr: AnyExpr, occurence: Bitvec) -> AnyExpr {
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
        if like_terms.is_empty() {
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

impl Transformer for LikeTermMerger {
    fn transform_add(&self, add: expr::Add) -> TransformOutcome {
        simplify_add(add)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prelude::*;
    use crate::simplifications;

    modular_ast_transformer! {
        #[derive(Default)]
        struct LikeTermJoinerTransformer {
            _0: LikeTermJoiner,
            _1: simplifications::Normalizer // For testing purposes only!
        }
    }
    type LikeTermJoinerSimplifier = BaseSimplifier<LikeTermJoinerTransformer>;

    fn create_simplifier() -> LikeTermJoinerSimplifier {
        LikeTermJoinerSimplifier::default()
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

    #[test]
    fn neg_mul_to_zero() {
        let b = new_builder();
        assert_simplified(
            b.bitvec_add_n(vec![
                b.bitvec_mul(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "y")
                ),
                b.bitvec_neg(
                    b.bitvec_mul(
                        b.bitvec_var(BitvecTy::w32(), "x"),
                        b.bitvec_var(BitvecTy::w32(), "y")
                    )
                )
            ]),
            b.bitvec_const(BitvecTy::w32(), 0)
        )
    }

    #[test]
    fn add_neg_to_zero() {
        let b = new_builder();
        assert_simplified(
            b.bitvec_add_n(vec![
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_neg(
                    b.bitvec_var(BitvecTy::w32(), "x")
                )
            ]),
            b.bitvec_const(BitvecTy::w32(), 0)
        )
    }

    #[test]
    fn single_merge_all() {
        let b = new_builder();
        assert_simplified(
            b.bitvec_add_n(vec![
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_neg(
                    b.bitvec_var(BitvecTy::w32(), "x")
                ),
                b.bitvec_mul(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 2)
                ),
                b.bitvec_neg(
                    b.bitvec_var(BitvecTy::w32(), "x")
                )
            ]),
            b.bitvec_var(BitvecTy::w32(), "x")
        )
    }

    #[test]
    fn minus_one_occurence() {
        let b = new_builder();
        assert_simplified(
            b.bitvec_add_n(vec![
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_mul(
                    b.bitvec_const(BitvecTy::w32(), -2_i32),
                    b.bitvec_var(BitvecTy::w32(), "x")
                )
            ]),
            b.bitvec_neg(
                b.bitvec_var(BitvecTy::w32(), "x")
            )
        )
    }

    #[test]
    fn multi_sym_occurence() {
        let b = new_builder();
        assert_simplified(
            b.bitvec_add_n(vec![
                b.bitvec_mul_n(vec![
                    b.bitvec_const(BitvecTy::w32(), 2_i32),
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "y")
                ]),
                b.bitvec_mul(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "y")
                )
            ]),
            b.bitvec_mul_n(vec![
                    b.bitvec_const(BitvecTy::w32(), 3_i32),
                    b.bitvec_mul(
                        b.bitvec_var(BitvecTy::w32(), "x"),
                        b.bitvec_var(BitvecTy::w32(), "y")
                    )
            ])
        )
    }

    #[test]
    fn same_multi_sym_to_single() {
        let b = new_builder();
        assert_simplified(
            b.bitvec_add_n(vec![
                b.bitvec_mul_n(vec![
                    b.bitvec_const(BitvecTy::w32(), 2_i32),
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "x")
                ]),
                b.bitvec_neg(
                    b.bitvec_mul(
                        b.bitvec_var(BitvecTy::w32(), "x"),
                        b.bitvec_var(BitvecTy::w32(), "x")
                    )
                )
            ]),
            b.bitvec_mul(
                b.bitvec_var(BitvecTy::w32(), "x"),
                b.bitvec_var(BitvecTy::w32(), "x")
            )
        )
    }
}
