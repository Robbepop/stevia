use crate::prelude::*;
use crate::ExprMarker;

use std::marker::PhantomData;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::BinTermExpr;
}

/// Generic binary term expression.
///
/// Used by concrete binary term expressions as base template.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BinTermExpr<M> {
    /// The two child term expressions.
    pub children: P<BinExprChildren>,
    /// The bit width of this expression.
    ///
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub bitvec_ty: BitvecTy,
    /// Marker to differentiate term expressions from each
    /// other using the type system.
    marker: PhantomData<M>,
}

impl<M> BinTermExpr<M>
where
    M: ExprMarker,
{
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
    pub fn new<E1, E2>(lhs: E1, rhs: E2) -> ExprResult<Self>
    where
        E1: Into<AnyExpr>,
        E2: Into<AnyExpr>,
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        let common_ty = expect_common_bitvec_ty(&lhs, &rhs)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(format!(
                    "Expected both child expressions of the binary {} expression \
                    to be of the same bitvector type.",
                    M::EXPR_KIND.camel_name()
                ))
            })?;
        Ok(Self {
            bitvec_ty: common_ty,
            children: BinExprChildren::new_boxed(lhs, rhs),
            marker: PhantomData,
        })
    }
}

impl<M> Children for BinTermExpr<M> {
    fn children(&self) -> ChildrenIter {
        self.children.children()
    }
}

impl<M> ChildrenMut for BinTermExpr<M> {
    fn children_mut(&mut self) -> ChildrenIterMut {
        self.children.children_mut()
    }
}

impl<M> IntoChildren for BinTermExpr<M> {
    fn into_children(self) -> IntoChildrenIter {
        self.children.into_children()
    }
}

impl<M> HasType for BinTermExpr<M> {
    fn ty(&self) -> Type {
        self.bitvec_ty.ty()
    }
}

impl<M> HasKind for BinTermExpr<M>
where
    M: ExprMarker,
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

impl<M> BinaryExpr for BinTermExpr<M> {
    fn lhs_child(&self) -> &AnyExpr {
        self.children.lhs_child()
    }
    fn rhs_child(&self) -> &AnyExpr {
        self.children.rhs_child()
    }
}
