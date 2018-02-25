use ast::prelude::*;
use ast::terms::checks;
use ast::terms::ExprMarker;

use std::marker::PhantomData;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        BinTermExpr
    };
}

/// Generic binary term expression.
/// 
/// Used by concrete binary term expressions as base template.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BinTermExpr<M> {
    /// The two child term expressions.
    pub childs: P<BinExprChilds>,
    /// The bit width of this expression.
    /// 
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub bitvec_ty: BitvecTy,
    /// Marker to differentiate term expressions from each
    /// other using the type system.
    marker: PhantomData<M>
}

impl<M> BinTermExpr<M> {
    /// Returns a new binary term expression with the given child term expressions.
    /// 
    /// # Errors
    /// 
    /// - If any of the two given child expressions is not of bitvec type or
    ///   has an unmatching bit width to the given bit width.
    pub fn new<E1, E2>(bitvec_ty: BitvecTy, lhs: E1, rhs: E2) -> Result<Self, String>
        where E1: Into<AnyExpr>,
              E2: Into<AnyExpr>
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        checks::expect_concrete_bitvec_ty(&lhs, bitvec_ty)?;
        checks::expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        Ok(Self{ bitvec_ty, childs: BinExprChilds::new_boxed(lhs, rhs), marker: PhantomData })
    }

    /// Returns a new binary term expression for the two given child term expressions.
    /// 
    /// # Note
    /// 
    /// Infers the concrete bitvector type of the resulting expression from the
    /// given child expressions.
    /// 
    /// # Errors
    /// 
    /// - If the given `lhs` or `rhs` do not share a common bitvec type.
    pub fn new_infer<E1, E2>(lhs: E1, rhs: E2) -> Result<Self, String>
        where E1: Into<AnyExpr>,
              E2: Into<AnyExpr>
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        let common_ty = checks::expect_common_bitvec_ty(&lhs, &rhs)?;
        Ok(Self{ bitvec_ty: common_ty, childs: BinExprChilds::new_boxed(lhs, rhs), marker: PhantomData })
    }
}

impl<M> Childs for BinTermExpr<M> {
    fn childs(&self) -> ChildsIter {
        self.childs.childs()
    }
}

impl<M> ChildsMut for BinTermExpr<M> {
    fn childs_mut(&mut self) -> ChildsIterMut {
        self.childs.childs_mut()
    }
}

impl<M> IntoChilds for BinTermExpr<M> {
    fn into_childs(self) -> IntoChildsIter {
        self.childs.into_childs()
    }
}

impl<M> HasType for BinTermExpr<M> {
    fn ty(&self) -> Type {
        self.bitvec_ty.ty()
    }
}

impl<M> HasKind for BinTermExpr<M>
    where M: ExprMarker
{
    fn kind(&self) -> ExprKind {
        M::EXPR_KIND
    }
}

impl<M> HasArity for BinTermExpr<M> {
    fn arity(&self) -> usize {
        2
    }
}
