use ast2::prelude::*;
use ast2::terms::checks;

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

impl_traits_for_binary_term_expr!(Concat);
