use ast::prelude::*;
use simplifier::prelude::*;

use itertools::Itertools;

use std::cmp::Ordering;

pub mod prelude {
    pub use super::Normalizer;
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Normalizer;

impl AutoImplAnyTransformer for Normalizer {}

fn normalization_cmp(lhs: &AnyExpr, rhs: &AnyExpr) -> Ordering {
    use self::AnyExpr::{
        Symbol,
        BoolConst,
        BitvecConst,
        Not,
        Neg,
        BitNot
    };
    match (lhs, rhs) {
        // Sort symbols by their name identifier
        (&Symbol(ref lhs), &Symbol(ref rhs)) => {
            lhs.name.cmp(&rhs.name)
        }

        // Sort bool constants by bool comparison
        (&BoolConst(ref lhs), &BoolConst(ref rhs)) => {
            lhs.val.cmp(&rhs.val)
        }

        // Sort bitvec constants by comparing their unsigned value.
        // This way all negative bitvector constants are always sorted
        // after all positive bitvector constants.
        (&BitvecConst(ref lhs), &BitvecConst(ref rhs)) => {
            if lhs.val.checked_ult(&rhs.val).unwrap() {
                Ordering::Less
            }
            else {
                Ordering::Greater
            }
        }

        // Sort not by forwarding comparison to its inner child expression.
        (&Not(ref lhs), &Not(ref rhs)) => {
            normalization_cmp(lhs.single_child(), rhs.single_child())
        }

        // Sort bitvec negation by forwarding comparison to its inner child expression.
        (&Neg(ref lhs), &Neg(ref rhs)) => {
            normalization_cmp(lhs.single_child(), rhs.single_child())
        }

        // Sort bitvec bit-not by forwarding comparison to its inner child expression.
        (&BitNot(ref lhs), &BitNot(ref rhs)) => {
            normalization_cmp(lhs.single_child(), rhs.single_child())
        }

        // Sort other expressions of the same kind generically.
        (lhs, rhs) if lhs.kind() == rhs.kind() => {
            use std::cmp::Ordering;
            match lhs.arity().cmp(&rhs.arity()) {
                Ordering::Less    => Ordering::Less,
                Ordering::Greater => Ordering::Greater,
                Ordering::Equal   => {
                    for (lchild, rchild) in lhs.childs().zip(rhs.childs()) {
                        match normalization_cmp(lchild, rchild) {
                            Ordering::Less    => return Ordering::Less,
                            Ordering::Greater => return Ordering::Greater,
                            Ordering::Equal   => continue
                        }
                    }
                    Ordering::Equal
                }
            }
        }

        // Different expression kinds are sorted by their kind based priority.
        _ => lhs.kind().priority().cmp(&rhs.kind().priority())
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
enum NormalizeFlag {
    /// States that the operation had nothing to do for normalization.
    Idle,
    /// States that the operation successfully normalized its input.
    Success
}

fn is_sorted_norm<'c, C>(childs: C) -> bool
    where C: IntoIterator<Item=&'c AnyExpr> + 'c
{
    childs.into_iter()
          .tuple_windows()
          .all(|(lhs, rhs)| {
              let order = normalization_cmp(lhs, rhs);
              order == Ordering::Less || order == Ordering::Equal
          })
}

fn establish_ordering<E>(expr: &mut E) -> NormalizeFlag
    where E: Childs + SortChildren
{
    if is_sorted_norm(expr.childs()) {
        return NormalizeFlag::Idle
    }
    expr.sort_children_by(normalization_cmp);
    // expr.childs_vec_mut()
    //     .sort_unstable_by(normalization_cmp);
    NormalizeFlag::Success
}

fn remove_duplicates<E>(expr: &mut E) -> NormalizeFlag
    where E: DedupChildren + HasArity
{
    let arity_before = expr.arity();
    // expr.childs_vec_mut().dedup();
    expr.dedup_children();
    let arity_after = expr.arity();
    assert!(arity_after <= arity_before);
    if arity_before != arity_after {
        return NormalizeFlag::Success
    }
    return NormalizeFlag::Idle
}

enum NormalizeOutcome {
    /// States that no normalization was applyable.
    Idle(AnyExpr),
    /// States that normalization deduplicated its input
    /// into an expression with only one child which is against
    /// the invariants of n-ary expressions and must be handled.
    DedupToSingle(AnyExpr),
    /// States that normalization occured and affected its
    /// input but deduplication did not result in a single child
    /// expression.
    DedupToMany(AnyExpr)
}

impl NormalizeOutcome {
    pub fn into_transform_outcome<F, E>(self, mapper: F) -> TransformOutcome
        where F: Fn(AnyExpr) -> E,
              E: Into<AnyExpr>
    {
        use self::NormalizeOutcome::*;
        match self {
            Idle(expr) => TransformOutcome::identity(expr),
            DedupToMany(expr) => TransformOutcome::transformed(expr),
            DedupToSingle(child) => TransformOutcome::transformed(mapper(child))
        }
    }
}

fn into_normalize<E>(expr: E) -> NormalizeOutcome
    where E: Childs + DedupChildren + SortChildren + HasArity + Into<AnyExpr>
{
    let mut expr = expr;
    let ordering = establish_ordering(&mut expr);
    let rm_duplicates = remove_duplicates(&mut expr);
    use self::NormalizeFlag::{Idle};
    if ordering == Idle && rm_duplicates == Idle {
        return NormalizeOutcome::Idle(expr.into())
    }
    match expr.arity() {
        0 => unreachable!(),
        1 => NormalizeOutcome::DedupToSingle(
                expr.into().into_childs().next().unwrap()),
        _ => NormalizeOutcome::DedupToMany(expr.into())
    }
}

impl Transformer for Normalizer {
    fn transform_bool_equals(&self, bool_equals: expr::BoolEquals) -> TransformOutcome {
        into_normalize(bool_equals)
            .into_transform_outcome(|_| expr::BoolConst::from(true))
    }

    fn transform_and(&self, and: expr::And) -> TransformOutcome {
        into_normalize(and)
            .into_transform_outcome(|child| child)
    }

    fn transform_or(&self, or: expr::Or) -> TransformOutcome {
        into_normalize(or)
            .into_transform_outcome(|child| child)
    }

    fn transform_add(&self, mut add: expr::Add) -> TransformOutcome {
        match establish_ordering(&mut add) {
            NormalizeFlag::Idle => TransformOutcome::identity(add),
            NormalizeFlag::Success => TransformOutcome::transformed(add)
        }
    }

    fn transform_mul(&self, mut mul: expr::Mul) -> TransformOutcome {
         match establish_ordering(&mut mul) {
            NormalizeFlag::Idle => TransformOutcome::identity(mul),
            NormalizeFlag::Success => TransformOutcome::transformed(mul)
        }
    }

    fn transform_bitand(&self, bitand: expr::BitAnd) -> TransformOutcome {
        into_normalize(bitand)
            .into_transform_outcome(|child| child)
    }

    fn transform_bitor(&self, bitor: expr::BitOr) -> TransformOutcome {
        into_normalize(bitor)
            .into_transform_outcome(|child| child)
    }

    fn transform_bitvec_equals(&self, bitvec_equals: expr::BitvecEquals) -> TransformOutcome {
        into_normalize(bitvec_equals)
            .into_transform_outcome(|_| expr::BoolConst::from(true))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn gen_dedup_bool_symbols() -> (AnyExpr, AnyExpr, AnyExpr) {
        let b = PlainExprTreeBuilder::default();
        let sym1 = b.bool_var("a").unwrap();
        let sym2 = b.bool_var("b").unwrap();
        let sym3 = b.bool_var("c").unwrap();
        (sym1, sym2, sym3)
    }

    fn dedup_many_bool_input() -> Vec<AnyExpr> {
        let (sym1, sym2, sym3) = gen_dedup_bool_symbols();
        vec![
            sym2.clone(),
            sym1.clone(),
            sym1.clone(),
            sym2.clone(),
            sym3.clone()
        ]
    }

    fn dedup_many_bool_expected() -> Vec<AnyExpr> {
        let (sym1, sym2, sym3) = gen_dedup_bool_symbols();
        vec![
            sym1.clone(),
            sym2.clone(),
            sym3.clone()
        ]
    }

    fn dedup_single_bool_input() -> Vec<AnyExpr> {
        let (sym1, _, _) = gen_dedup_bool_symbols();
        vec![
            sym1.clone(),
            sym1.clone(),
            sym1.clone()
        ]
    }

    fn gen_dedup_bitvec_symbols() -> (AnyExpr, AnyExpr, AnyExpr) {
        let b = PlainExprTreeBuilder::default();
        let sym1 = b.bitvec_var(BitvecTy::w32(), "x").unwrap();
        let sym2 = b.bitvec_var(BitvecTy::w32(), "y").unwrap();
        let sym3 = b.bitvec_var(BitvecTy::w32(), "z").unwrap();
        (sym1, sym2, sym3)
    }

    fn dedup_many_bitvec_input() -> Vec<AnyExpr> {
        let (sym1, sym2, sym3) = gen_dedup_bitvec_symbols();
        vec![
            sym2.clone(),
            sym1.clone(),
            sym1.clone(),
            sym2.clone(),
            sym3.clone()
        ]
    }

    fn dedup_many_bitvec_expected() -> Vec<AnyExpr> {
        let (sym1, sym2, sym3) = gen_dedup_bitvec_symbols();
        vec![
            sym1.clone(),
            sym2.clone(),
            sym3.clone()
        ]
    }

    fn dedup_single_bitvec_input() -> Vec<AnyExpr> {
        let (sym1, _, _) = gen_dedup_bitvec_symbols();
        vec![
            sym1.clone(),
            sym1.clone(),
            sym1.clone()
        ]
    }

    mod bool_equals {
        use super::*;

        #[test]
        fn ordering() {
            let b = PlainExprTreeBuilder::default();
            let sym1 = b.bool_var("a").unwrap();
            let sym2 = b.bool_var("b").unwrap();
            let mut expr = b.bool_equals(
                sym2.clone(),
                sym1.clone()
            ).unwrap();
            let expected = b.bool_equals(
                sym1.clone(),
                sym2.clone()
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, expected);
        }

        #[test]
        fn dedup_many() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bool_equals_n(
                dedup_many_bool_input()).unwrap();
            let expected = b.bool_equals_n(
                dedup_many_bool_expected()).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, expected);
        }

        #[test]
        fn dedup_single() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bool_equals_n(
                dedup_single_bool_input()).unwrap();
            let expected = b.bool_const(true).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, expected);
        }
    }

    mod and {
        use super::*;

        #[test]
        fn ordering() {
            let b = PlainExprTreeBuilder::default();
            let sym1 = b.bool_var("a").unwrap();
            let sym2 = b.bool_var("b").unwrap();
            let mut expr = b.and(
                sym2.clone(),
                sym1.clone()
            ).unwrap();
            let expected = b.and(
                sym1.clone(),
                sym2.clone()
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, expected);
        }

        #[test]
        fn dedup_many() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.and_n(
                dedup_many_bool_input()).unwrap();
            let expected = b.and_n(
                dedup_many_bool_expected()).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, expected);
        }

        #[test]
        fn dedup_single() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.and_n(
                dedup_single_bool_input()).unwrap();
            Simplifier::default().simplify(&mut expr);
            let (expected, ..) = gen_dedup_bool_symbols();
            assert_eq!(expr, expected);
        }
    }

    mod or {
        use super::*;

        #[test]
        fn ordering() {
            let b = PlainExprTreeBuilder::default();
            let sym1 = b.bool_var("a").unwrap();
            let sym2 = b.bool_var("b").unwrap();
            let mut expr = b.or(
                sym2.clone(),
                sym1.clone()
            ).unwrap();
            let expected = b.or(
                sym1.clone(),
                sym2.clone()
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, expected);
        }

        #[test]
        fn dedup_many() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.or_n(
                dedup_many_bool_input()).unwrap();
            let expected = b.or_n(
                dedup_many_bool_expected()).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, expected);
        }

        #[test]
        fn dedup_single() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.or_n(
                dedup_single_bool_input()).unwrap();
            Simplifier::default().simplify(&mut expr);
            let (expected, ..) = gen_dedup_bool_symbols();
            assert_eq!(expr, expected);
        }
    }

    mod add {
        use super::*;

        #[test]
        fn ordering() {
            let b = PlainExprTreeBuilder::default();
            let sym1 = b.bitvec_var(BitvecTy::w32(), "x").unwrap();
            let sym2 = b.bitvec_var(BitvecTy::w32(), "y").unwrap();
            let mut expr = b.bitvec_add(
                sym2.clone(),
                sym1.clone()
            ).unwrap();
            let expected = b.bitvec_add(
                sym1.clone(),
                sym2.clone()
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, expected);
        }
    }

    mod mul {
        use super::*;

        #[test]
        fn ordering() {
            let b = PlainExprTreeBuilder::default();
            let sym1 = b.bitvec_var(BitvecTy::w32(), "x").unwrap();
            let sym2 = b.bitvec_var(BitvecTy::w32(), "y").unwrap();
            let mut expr = b.bitvec_mul(
                sym2.clone(),
                sym1.clone()
            ).unwrap();
            let expected = b.bitvec_mul(
                sym1.clone(),
                sym2.clone()
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, expected);
        }
    }

    mod bitand {
        use super::*;

        #[test]
        fn ordering() {
            let b = PlainExprTreeBuilder::default();
            let sym1 = b.bitvec_var(BitvecTy::w32(), "x").unwrap();
            let sym2 = b.bitvec_var(BitvecTy::w32(), "y").unwrap();
            let mut expr = b.bitvec_and(
                sym2.clone(),
                sym1.clone()
            ).unwrap();
            let expected = b.bitvec_and(
                sym1.clone(),
                sym2.clone()
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, expected);
        }

        #[test]
        fn dedup_many() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_and_n(
                dedup_many_bitvec_input()).unwrap();
            let expected = b.bitvec_and_n(
                dedup_many_bitvec_expected()).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, expected);
        }

        #[test]
        fn dedup_single() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_and_n(
                dedup_single_bitvec_input()).unwrap();
            Simplifier::default().simplify(&mut expr);
            let (expected, ..) = gen_dedup_bitvec_symbols();
            assert_eq!(expr, expected);
        }
    }

    mod bitor {
        use super::*;

        #[test]
        fn ordering() {
            let b = PlainExprTreeBuilder::default();
            let sym1 = b.bitvec_var(BitvecTy::w32(), "x").unwrap();
            let sym2 = b.bitvec_var(BitvecTy::w32(), "y").unwrap();
            let mut expr = b.bitvec_or(
                sym2.clone(),
                sym1.clone()
            ).unwrap();
            let expected = b.bitvec_or(
                sym1.clone(),
                sym2.clone()
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, expected);
        }

        #[test]
        fn dedup_many() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_or_n(
                dedup_many_bitvec_input()).unwrap();
            let expected = b.bitvec_or_n(
                dedup_many_bitvec_expected()).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, expected);
        }

        #[test]
        fn dedup_single() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_or_n(
                dedup_single_bitvec_input()).unwrap();
            Simplifier::default().simplify(&mut expr);
            let (expected, ..) = gen_dedup_bitvec_symbols();
            assert_eq!(expr, expected);
        }
    }

    mod bitvec_equals {
        use super::*;

        #[test]
        fn ordering() {
            let b = PlainExprTreeBuilder::default();
            let sym1 = b.bitvec_var(BitvecTy::w32(), "x").unwrap();
            let sym2 = b.bitvec_var(BitvecTy::w32(), "y").unwrap();
            let mut expr = b.bitvec_equals(
                sym2.clone(),
                sym1.clone()
            ).unwrap();
            let expected = b.bitvec_equals(
                sym1.clone(),
                sym2.clone()
            ).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, expected);
        }

        #[test]
        fn dedup_many() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_equals_n(
                dedup_many_bitvec_input()).unwrap();
            let expected = b.bitvec_equals_n(
                dedup_many_bitvec_expected()).unwrap();
            Simplifier::default().simplify(&mut expr);
            assert_eq!(expr, expected);
        }

        #[test]
        fn dedup_single() {
            let b = PlainExprTreeBuilder::default();
            let mut expr = b.bitvec_equals_n(
                dedup_single_bitvec_input()).unwrap();
            Simplifier::default().simplify(&mut expr);
            let expected = b.bool_const(true).unwrap();
            assert_eq!(expr, expected);
        }
    }
}
