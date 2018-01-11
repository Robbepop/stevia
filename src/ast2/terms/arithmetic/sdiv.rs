use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::{
        SignedDiv
    };
}

/// Binary `SignedDiv` (signed division) term expression.
/// 
/// Divides the left child by the right: left / right
/// 
/// # Note
/// 
/// - On machine level signed and unsigned division are
///   two different operations and have to be treated differently.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SignedDiv {
    /// The two child term expressions.
    pub childs: P<BinExprChilds>,
    /// The bit width of this expression.
    /// 
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub bitvec_ty: BitvecTy
}

impl SignedDiv {
    /// Returns a new `SignedDiv` (signed division) term expression with the given
    /// child term expressions.
    /// 
    /// # Errors
    /// 
    /// - If any of the two given child expressions is not of bitvec type or
    ///   has an unmatching bit width to the given bit width.
    pub fn new(bitvec_ty: BitvecTy, lhs: AnyExpr, rhs: AnyExpr) -> Result<SignedDiv, String> {
        checks::expect_concrete_bitvec_ty(&lhs, bitvec_ty)?;
        checks::expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        Ok(SignedDiv{ bitvec_ty, childs: BinExprChilds::new_boxed(lhs, rhs) })
    }
}

impl_traits_for_binary_term_expr!(SignedDiv);
