use ast::prelude::*;
use ast::terms::checks;
use ast::terms::ExprMarker;

use std::marker::PhantomData;
use std::cmp::Ordering;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::NaryTermExpr;
}

/// Generic n-ary term expression.
/// 
/// Used by concrete binary term expressions as base template.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NaryTermExpr<M> {
    /// The child term expressions.
    pub childs: Vec<AnyExpr>,
    /// The bit width of this expression.
    ///
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub bitvec_ty: BitvecTy,
    /// Marker to differentiate term expressions from each
    /// other using the type system.
    marker: PhantomData<M>
}

impl<M> NaryTermExpr<M> {
    /// Returns a new n-ary term expression for the given two child expressions.
    /// 
    /// # Notes
    /// 
    /// Since the given two child expressions are the child expressions of the resulting
    /// n-ary term expression it will actually be a binary term expression upon construction.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` are not of bitvec type.
    /// - If `lhs` or `rhs` are of bitvec type but do not have matching bit widths.
    pub fn binary_with_type<E1, E2>(bitvec_ty: BitvecTy, lhs: E1, rhs: E2) -> Result<Self, String>
        where E1: Into<AnyExpr>,
              E2: Into<AnyExpr>
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        checks::expect_concrete_bitvec_ty(&lhs, bitvec_ty)?;
        checks::expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        Ok(Self{ bitvec_ty, childs: vec![lhs, rhs], marker: PhantomData })
    }

    /// Returns a new n-ary term expression for the given two child expressions.
    /// 
    /// # Note
    /// 
    /// - Infers the concrete bitvector type of the resulting expression from its childs.
    /// - Since the given two child expressions are the child expressions of the resulting
    ///   n-ary term expression it will actually be a binary term expression upon construction.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` do not share a common bitvec type.
    pub fn binary<E1, E2>(lhs: E1, rhs: E2) -> Result<Self, String>
        where E1: Into<AnyExpr>,
              E2: Into<AnyExpr>
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        let common_ty = checks::expect_common_bitvec_ty(&lhs, &rhs)?;
        Ok(Self{ bitvec_ty: common_ty, childs: vec![lhs, rhs], marker: PhantomData })
    }

    /// Creates a new n-ary term expression for all of the child
    /// expressions yielded by the given iterator and with the given bit width.
    ///
    /// # Errors
    ///
    /// - If the given iterator yields less than two child expressions.
    /// - If not all yielded child expressions are of bitvec type with
    ///   the required bit width.
    pub fn nary_with_type<I>(bitvec_ty: BitvecTy, childs: I) -> Result<Self, String>
        where I: IntoIterator<Item = AnyExpr>,
    {
        let childs = childs.into_iter().collect::<Vec<_>>();
        if childs.len() < 2 {
            return Err(
                "Requires at least two child expressions to create an n-ary term expression.".into(),
            );
        }
        if childs
            .iter()
            .any(|c| checks::expect_concrete_bitvec_ty(c, bitvec_ty).is_err())
        {
            return Err(
                "Requires all child expressions to be of bitvec type with the expected bit width."
                    .into(),
            );
        }
        Ok(Self{ bitvec_ty, childs, marker: PhantomData })
    }

    /// Creates a new n-ary term expression from the given iterator over expressions.
    /// 
    /// # Notes
    /// 
    /// This automatically infers the common bitvector type of its given child expressions.
    /// 
    /// # Errors
    /// 
    /// - If the given iterator yields less than two expressions.
    /// - If not all yielded expressions are of the same bitvec type.
    pub fn nary<E>(exprs: E) -> Result<Self, String>
        where E: IntoIterator<Item=AnyExpr>
    {
        let childs = exprs.into_iter().collect::<Vec<_>>();
        if childs.len() < 2 {
            return Err("Require at least 2 child expressions to create a new n-ary term expression.".into())
        }
        let bitvec_ty = checks::expect_common_bitvec_ty_n(&childs)?;
        Ok(Self{ bitvec_ty, childs, marker: PhantomData })
    }
}

impl<M> Childs for NaryTermExpr<M> {
    fn childs(&self) -> ChildsIter {
        ChildsIter::nary(&self.childs)
    }
}

impl<M> ChildsMut for NaryTermExpr<M> {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::nary(&mut self.childs)
    }
}

impl<M> IntoChilds for NaryTermExpr<M> {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::nary(self.childs)
    }
}

impl<M> HasType for NaryTermExpr<M> {
    fn ty(&self) -> Type {
        self.bitvec_ty.ty()
    }
}

impl<M> HasKind for NaryTermExpr<M>
    where M: ExprMarker
{
    fn kind(&self) -> ExprKind {
        M::EXPR_KIND
    }
}

impl<M> HasArity for NaryTermExpr<M> {
    fn arity(&self) -> usize {
        self.childs.len()
    }
}

impl<M> DedupChildren for NaryTermExpr<M> {
    fn dedup_children(&mut self) {
        self.childs.dedup()
    }
}

impl<M> SortChildren for NaryTermExpr<M> {
    fn sort_children_by<F>(&mut self, comparator: F)
        where F: FnMut(&AnyExpr, &AnyExpr) -> Ordering
    {
        self.childs.sort_unstable_by(comparator)
    }
}
