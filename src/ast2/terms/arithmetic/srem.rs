use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::{
        SignedRemainder
    };
}

/// Binary `SignedRemainder` term expression.
/// 
/// # Example
/// 
/// -21 divided by 4 gives -5 with a remainder of -1.
/// 
/// # Note
/// 
/// - On machine level signed and unsigned division are
///   two different operations and have to be treated differently.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SignedRemainder {
    /// The two child term expressions.
    pub childs: P<BinExprChilds>,
    /// The bit width of this expression.
    /// 
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub bitvec_ty: BitvecTy
}

impl SignedRemainder {
    /// Returns a new `SignedRemainder` term expression with the given
    /// child term expressions.
    /// 
    /// # Errors
    /// 
    /// - If any of the two given child expressions is not of bitvec type or
    ///   has an unmatching bit width to the given bit width.
    pub fn new(bitvec_ty: BitvecTy, lhs: AnyExpr, rhs: AnyExpr) -> Result<SignedRemainder, String> {
        checks::expect_concrete_bitvec_ty(&lhs, bitvec_ty)?;
        checks::expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        Ok(SignedRemainder{ bitvec_ty, childs: BinExprChilds::new_boxed(lhs, rhs) })
    }

    /// Returns a new binary `SignedRemainder` (signed remainder) expression for the
    /// given two child expressions.
    /// 
    /// # Note
    /// 
    /// Infers the concrete bitvector type of the resulting expression from its childs.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` do not share a common bitvec type.
    pub fn new_infer(lhs: AnyExpr, rhs: AnyExpr) -> Result<SignedRemainder, String> {
        let common_ty = checks::expect_common_bitvec_ty(&lhs, &rhs)?;
        Ok(SignedRemainder{ bitvec_ty: common_ty, childs: vec![lhs, rhs] })
    }

}

impl_traits_for_binary_term_expr!(SignedRemainder);
