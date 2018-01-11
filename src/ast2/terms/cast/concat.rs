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
    pub width: BitWidth
}

impl Concat {
    /// Returns a new `Concat` (concatenate) term expression with the
    /// given child term expressions.
    /// 
    /// # Errors
    /// 
    /// - If any of the two given child expressions is not of bitvec type or
    ///   has an unmatching bit width to the given bit width.
    pub fn new(lhs: AnyExpr, rhs: AnyExpr) -> Result<Concat, String> {
        let width = checks::expect_bitvec_ty(&lhs)?;
        checks::expect_bitvec_ty_and_width(&rhs, width)?;
        Ok(Concat{ width, childs: BinExprChilds::new_boxed(lhs, rhs) })
    }
}

impl_traits_for_binary_term_expr!(Concat);
