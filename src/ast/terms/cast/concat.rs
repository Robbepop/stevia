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
    pub childs: P<BinExprChilds>,
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
            childs: BinExprChilds::new_boxed(lhs, rhs)
        })
    }
}

impl Childs for Concat {
    fn childs(&self) -> ChildsIter {
        self.childs.childs()
    }
}

impl ChildsMut for Concat {
    fn childs_mut(&mut self) -> ChildsIterMut {
        self.childs.childs_mut()
    }
}

impl IntoChilds for Concat {
    fn into_childs(self) -> IntoChildsIter {
        self.childs.into_childs()
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
