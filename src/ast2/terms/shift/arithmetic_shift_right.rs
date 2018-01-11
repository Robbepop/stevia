use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::{
        ArithmeticShiftRight
    };
}

/// Binary arithmetic-shift-right term expression.
/// 
/// # Note
/// 
/// - Arithmetic shift-right respects the sign bit of the term expression.
/// - Shifting to left means shifting the bits of the term expression from
///   the most significant position to the least significant position.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArithmeticShiftRight {
    /// The two child term expressions.
    pub childs: P<BinExprChilds>,
    /// The bit width of this expression.
    /// 
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub bitvec_ty: BitvecTy
}

impl ArithmeticShiftRight {
    /// Returns a new `ArithmeticShiftRight` term expression with the
    /// given child term expressions.
    /// 
    /// # Errors
    /// 
    /// - If any of the two given child expressions is not of bitvec type or
    ///   has an unmatching bit width to the given bit width.
    pub fn new(bitvec_ty: BitvecTy, lhs: AnyExpr, rhs: AnyExpr) -> Result<ArithmeticShiftRight, String> {
        checks::expect_concrete_bitvec_ty(&lhs, bitvec_ty)?;
        checks::expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        Ok(ArithmeticShiftRight{ bitvec_ty, childs: BinExprChilds::new_boxed(lhs, rhs) })
    }
}

impl_traits_for_binary_term_expr!(ArithmeticShiftRight);
