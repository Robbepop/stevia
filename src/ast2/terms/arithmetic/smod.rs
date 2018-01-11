use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::{
        SignedModulo
    };
}

/// Binary `SignedModulo` (signed remainder) where its sign matches the sign of the divisor.
/// 
/// # Example
/// 
/// -21 mod 4 is 3 because -21 + 4 x 6 is 3.
/// 
/// # Note
/// 
/// - There purposely is no `Umod` term expression since it has no difference to
///   the `Urem` term expression. Use this instead.
/// - On machine level signed and unsigned division are
///   two different operations and have to be treated differently.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SignedModulo {
    /// The two child term expressions.
    pub childs: P<BinExprChilds>,
    /// The bit width of this expression.
    /// 
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub width: BitWidth
}

impl SignedModulo {
    /// Returns a new `SignedModulo` (signed remaainder) term expression with the given
    /// child term expressions where its sign matches the sign of the divisor.
    /// 
    /// # Errors
    /// 
    /// - If any of the two given child expressions is not of bitvec type or
    ///   has an unmatching bit width to the given bit width.
    pub fn new(width: BitWidth, lhs: AnyExpr, rhs: AnyExpr) -> Result<SignedModulo, String> {
        checks::expect_bitvec_ty_and_width(&lhs, width)?;
        checks::expect_bitvec_ty_and_width(&rhs, width)?;
        Ok(SignedModulo{ width, childs: BinExprChilds::new_boxed(lhs, rhs) })
    }
}

impl_traits_for_binary_term_expr!(SignedModulo);
