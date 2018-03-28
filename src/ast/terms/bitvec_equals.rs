use ast::prelude::*;

use std::iter::FromIterator;
use std::cmp::Ordering;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        BitvecEquals
    };
}

/// N-ary equality expression for bitvectors.
/// 
/// Evaluates to `true` if all child bitvec expressions evalute
/// to the same value, else evaluates to `false`.
/// 
/// # Note
/// 
/// - All child bitvec expressions must have the same bit width.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitvecEquals {
    /// The child expressions.
    pub children: Vec<AnyExpr>,
    /// The common bit width of all child bitvec expressions.
    pub children_bitvec_ty: BitvecTy
}

impl BitvecEquals {
    /// Returns a new binary `BitvecEquals` expression for the given two child expressions.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` are not of bitvec type.
    /// - If `lhs` or `rhs` are of bitvec type but do not have matching bit widths.
    pub fn binary_with_type<E1, E2>(bitvec_ty: BitvecTy, lhs: E1, rhs: E2) -> Result<BitvecEquals, String>
        where E1: Into<AnyExpr>,
              E2: Into<AnyExpr>
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        Ok(BitvecEquals{ children_bitvec_ty: bitvec_ty, children: vec![lhs, rhs] })
    }

    /// Returns a new binary `BitvecEquals` expression for the given two child expressions.
    /// 
    /// # Note
    /// 
    /// Infers the concrete bitvector type of the resulting expression from its children.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` do not share a common bitvec type.
    pub fn binary<E1, E2>(lhs: E1, rhs: E2) -> Result<BitvecEquals, String>
        where E1: Into<AnyExpr>,
              E2: Into<AnyExpr>
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        let common_ty = expect_common_bitvec_ty(&lhs, &rhs)?;
        Ok(BitvecEquals{ children_bitvec_ty: common_ty, children: vec![lhs, rhs] })
    }

    /// Creates a new n-ary `BitvecEquals` expression from the given iterator over expressions.
    /// 
    /// # Errors
    /// 
    /// - If the given iterator iterates over less than two expressions.
    /// - If not all iterated expressions are of bitvec type with the given bit width.
    pub fn nary_with_type<E>(bitvec_ty: BitvecTy, exprs: E) -> Result<BitvecEquals, String>
        where E: IntoIterator<Item=AnyExpr>
    {
        let children = Vec::from_iter(exprs);
        if children.len() < 2 {
            return Err("Require at least 2 child expressions to create a new BitvecEquals expression.".into())
        }
        for child in &children {
            expect_concrete_bitvec_ty(child, bitvec_ty)?;
        }
        Ok(BitvecEquals{ children_bitvec_ty: bitvec_ty, children })
    }

    /// Creates a new n-ary `BitvecEquals` expression from the given iterator over expressions.
    /// 
    /// This automatically infers the common bitvector type of its given child expressions.
    /// 
    /// # Errors
    /// 
    /// - If the given iterator yields less than two expressions.
    /// - If not all yielded expressions are of the same bitvec type.
    pub fn nary<E>(exprs: E) -> Result<BitvecEquals, String>
        where E: IntoIterator<Item=AnyExpr>
    {
        let children = exprs.into_iter().collect::<Vec<_>>();
        if children.len() < 2 {
            return Err("Require at least 2 child expressions to create a new BitvecEquals expression.".into())
        }
        let children_bitvec_ty = expect_common_bitvec_ty_n(&children)?;
        Ok(BitvecEquals{ children_bitvec_ty, children })
    }
}

impl HasType for BitvecEquals {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl HasKind for BitvecEquals {
    fn kind(&self) -> ExprKind {
        ExprKind::BitvecEquals
    }
}

impl HasArity for BitvecEquals {
    fn arity(&self) -> usize {
        self.children.len()
    }
}

impl From<BitvecEquals> for AnyExpr {
    fn from(bitvec_equals: BitvecEquals) -> AnyExpr {
        AnyExpr::BitvecEquals(bitvec_equals)
    }
}

impl Children for BitvecEquals {
    fn children(&self) -> ChildrenIter {
        ChildrenIter::nary(&self.children)
    }
}

impl ChildrenMut for BitvecEquals {
    fn children_mut(&mut self) -> ChildrenIterMut {
        ChildrenIterMut::nary(&mut self.children)
    }
}

impl IntoChildren for BitvecEquals {
    fn into_children(self) -> IntoChildrenIter {
        IntoChildrenIter::nary(self.children)
    }
}

impl DedupChildren for BitvecEquals {
    fn dedup_children(&mut self) {
        self.children.dedup()
    }
}

impl SortChildren for BitvecEquals {
    fn sort_children_by<F>(&mut self, comparator: F)
        where F: FnMut(&AnyExpr, &AnyExpr) -> Ordering
    {
        self.children.sort_unstable_by(comparator)
    }
}

impl RetainChildren for BitvecEquals {
    fn retain_children<P>(&mut self, predicate: P)
        where P: FnMut(&AnyExpr) -> bool
    {
        self.children.retain(predicate);
    }
}
