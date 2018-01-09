use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::{
        Srem
    };
}

/// Binary Srem (signed remainder) term expression.
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
pub struct Srem {
    /// The two child term expressions.
    pub childs: P<BinExprChilds>,
    /// The bit width of this expression.
    /// 
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub width: BitWidth
}

impl Srem {
    /// Returns a new `Srem` (signed remaainder) term expression with the given
    /// child term expressions.
    /// 
    /// # Errors
    /// 
    /// - If any of the two given child expressions is not of bitvec type or
    ///   has an unmatching bit width to the given bit width.
    pub fn new(width: BitWidth, lhs: Expr, rhs: Expr) -> Result<Srem, String> {
        checks::expect_bitvec_ty_and_width(&lhs, width)?;
        checks::expect_bitvec_ty_and_width(&rhs, width)?;
        Ok(Srem{ width, childs: BinExprChilds::new_boxed(lhs, rhs) })
    }
}

impl_traits_for_binary_term_expr!(Srem);
