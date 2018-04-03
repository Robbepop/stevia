use ast::prelude::*;
use ast::ExprMarker;

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
    pub children: Vec<AnyExpr>,
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
    /// # Note
    /// 
    /// - Infers the concrete bitvector type of the resulting expression from its children.
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
        let common_ty = expect_common_bitvec_ty(&lhs, &rhs)?;
        Ok(Self{ bitvec_ty: common_ty, children: vec![lhs, rhs], marker: PhantomData })
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
        let children = exprs.into_iter().collect::<Vec<_>>();
        if children.len() < 2 {
            return Err("Require at least 2 child expressions to create a new n-ary term expression.".into())
        }
        let bitvec_ty = expect_common_bitvec_ty_n(&children)?;
        Ok(Self{ bitvec_ty, children, marker: PhantomData })
    }
}

impl<M> Children for NaryTermExpr<M> {
    fn children(&self) -> ChildrenIter {
        ChildrenIter::nary(&self.children)
    }
}

impl<M> ChildrenMut for NaryTermExpr<M> {
    fn children_mut(&mut self) -> ChildrenIterMut {
        ChildrenIterMut::nary(&mut self.children)
    }
}

impl<M> IntoChildren for NaryTermExpr<M> {
    fn into_children(self) -> IntoChildrenIter {
        IntoChildrenIter::nary(self.children)
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
        self.children.len()
    }
}

impl<M> DedupChildren for NaryTermExpr<M> {
    fn dedup_children(&mut self) {
        self.children.dedup()
    }
}

impl<M> SortChildren for NaryTermExpr<M> {
    fn sort_children_by<F>(&mut self, comparator: F)
        where F: FnMut(&AnyExpr, &AnyExpr) -> Ordering
    {
        self.children.sort_unstable_by(comparator)
    }
}

impl<M> RetainChildren for NaryTermExpr<M> {
    fn retain_children<P>(&mut self, predicate: P)
        where P: FnMut(&AnyExpr) -> bool
    {
        self.children.retain(predicate);
    }
}
