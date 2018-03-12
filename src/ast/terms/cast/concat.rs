use ast::prelude::*;
use ast::terms::checks;

pub mod prelude {
    pub use super::{
        Concat
    };
}

/// Binary concatenate term expression.
/// 
/// Concatenates the given bitvec term expressions together.
/// The resulting term expression has a width that is equal to
/// the sum of the bit width of both child term expressions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Concat {
    /// The two child term expressions.
    pub children: P<BinExprChildren>,
    /// The resulting bit width.
    /// 
    /// The purpose of this is to cache the bitwidth so that
    /// it does not have to be recomputed all the time over.
    /// 
    /// Caching this value is useful since the bit width cannot
    /// change during the lifetime of this expression.
    pub bitvec_ty: BitvecTy
}

impl Concat {
    /// Returns a new `Concat` (concatenate) term expression with the
    /// given child term expressions.
    /// 
    /// # Errors
    /// 
    /// - If any of the two given child expressions is not of bitvec type.
    pub fn new<E1, E2>(lhs: E1, rhs: E2) -> Result<Concat, String>
        where E1: Into<AnyExpr>,
              E2: Into<AnyExpr>
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        let lhs_bvty = checks::expect_bitvec_ty(&lhs)?;
        let rhs_bvty = checks::expect_bitvec_ty(&rhs)?;
        let concat_bvty = BitvecTy::from(
            lhs_bvty.width().to_usize() + rhs_bvty.width().to_usize());
        Ok(Concat{
            bitvec_ty: concat_bvty,
            children: BinExprChildren::new_boxed(lhs, rhs)
        })
    }
}

impl Children for Concat {
    fn children(&self) -> ChildrenIter {
        self.children.children()
    }
}

impl ChildrenMut for Concat {
    fn children_mut(&mut self) -> ChildrenIterMut {
        self.children.children_mut()
    }
}

impl IntoChildren for Concat {
    fn into_children(self) -> IntoChildrenIter {
        self.children.into_children()
    }
}

impl HasType for Concat {
    fn ty(&self) -> Type {
        self.bitvec_ty.ty()
    }
}

impl HasKind for Concat {
    fn kind(&self) -> ExprKind {
        ExprKind::Concat
    }
}

impl HasArity for Concat {
    fn arity(&self) -> usize {
        2
    }
}

impl From<Concat> for AnyExpr {
    fn from(expr: Concat) -> AnyExpr {
        AnyExpr::Concat(expr)
    }
}
