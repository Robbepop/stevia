use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::SignedGreaterEquals;
}

/// Binary signed greater-than-or-equals term expression.
///
/// # Note
///
/// Greater equals comparison is different for signed and unsigned parameters.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SignedGreaterEquals {
    /// The two child term expressions.
    pub childs: P<BinExprChilds>,
    /// The bit width of this expression.
    ///
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub childs_bitvec_ty: BitvecTy,
}

impl SignedGreaterEquals {
    /// Returns a new `SignedGreaterEquals` term expression with the
    /// given child term expressions.
    ///
    /// # Errors
    ///
    /// - If any of the two given child expressions is not of bitvec type or
    ///   has an unmatching bit width to the given bit width.
    pub fn new(
        bitvec_ty: BitvecTy,
        lhs: AnyExpr,
        rhs: AnyExpr,
    ) -> Result<SignedGreaterEquals, String> {
        checks::expect_concrete_bitvec_ty(&lhs, bitvec_ty)?;
        checks::expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        Ok(SignedGreaterEquals {
            childs_bitvec_ty: bitvec_ty,
            childs: BinExprChilds::new_boxed(lhs, rhs),
        })
    }

    /// Returns a new binary `SignedGreaterEquals` expression for the given two child expressions.
    /// 
    /// # Note
    /// 
    /// Infers the concrete bitvector type of the resulting expression from its childs.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` do not share a common bitvec type.
    pub fn new_infer(lhs: AnyExpr, rhs: AnyExpr) -> Result<SignedGreaterEquals, String> {
        let common_ty = checks::expect_common_bitvec_ty(&lhs, &rhs)?;
        Ok(SignedGreaterEquals{ childs_bitvec_ty: common_ty, childs: BinExprChilds::new_boxed(lhs, rhs) })
    }
}

impl_traits_for_binary_comparison_expr!(SignedGreaterEquals);
