use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::{
        UnsignedGreaterEquals
    };
}

/// Binary unsigned greater-than-or-equals term expression.
/// 
/// # Note
/// 
/// Greater equals comparison is different for signed and unsigned parameters.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UnsignedGreaterEquals {
    /// The two child term expressions.
    pub childs: P<BinExprChilds>,
    /// The bit width of this expression.
    /// 
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub childs_bitvec_ty: BitvecTy
}

impl UnsignedGreaterEquals {
    /// Returns a new `UnsignedGreaterEquals` term expression with the
    /// given child term expressions.
    /// 
    /// # Errors
    /// 
    /// - If any of the two given child expressions is not of bitvec type or
    ///   has an unmatching bit width to the given bit width.
    pub fn new(bitvec_ty: BitvecTy, lhs: AnyExpr, rhs: AnyExpr) -> Result<UnsignedGreaterEquals, String> {
        checks::expect_concrete_bitvec_ty(&lhs, bitvec_ty)?;
        checks::expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        Ok(UnsignedGreaterEquals{ childs_bitvec_ty: bitvec_ty, childs: BinExprChilds::new_boxed(lhs, rhs) })
    }
}

impl_traits_for_binary_comparison_expr!(UnsignedGreaterEquals);
