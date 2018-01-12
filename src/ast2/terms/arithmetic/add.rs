use ast2::prelude::*;
use ast2::terms::checks;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::Add;
}

/// Add term expression for adding a number of bitvector expressions.
///
/// Arithmetically sums up all child term expressions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Add {
    /// The child bitvector expressions.
    pub childs: Vec<AnyExpr>,
    /// The bit width of this expression.
    ///
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub bitvec_ty: BitvecTy,
}

impl Add {
    /// Returns a new binary `Add` expression for the given two child expressions.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` are not of bitvec type.
    /// - If `lhs` or `rhs` are of bitvec type but do not have matching bit widths.
    pub fn binary(bitvec_ty: BitvecTy, lhs: AnyExpr, rhs: AnyExpr) -> Result<Add, String> {
        checks::expect_concrete_bitvec_ty(&lhs, bitvec_ty)?;
        checks::expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        Ok(Add{ bitvec_ty, childs: vec![lhs, rhs] })
    }

    /// Creates a new n-ary Add term expression for all of the child
    /// expressions yielded by the given iterator and with the given bit width.
    ///
    /// # Errors
    ///
    /// - If the given iterator yields less than two child expressions.
    /// - If not all yielded child expressions are of bitvec type with
    ///   the required bit width.
    pub fn nary<I>(bitvec_ty: BitvecTy, childs: I) -> Result<Add, String>
    where
        I: IntoIterator<Item = AnyExpr>,
    {
        let childs = childs.into_iter().collect::<Vec<_>>();
        if childs.len() < 2 {
            return Err(
                "Requires at least two child expressions to create an Add term expression.".into(),
            );
        }
        if childs
            .iter()
            .any(|c| checks::expect_concrete_bitvec_ty(c, bitvec_ty).is_err())
        {
            return Err(
                "Requires all child expressions to be of bitvec type with the expected bit width."
                    .into(),
            );
        }
        Ok(Add { bitvec_ty, childs })
    }
}

impl_traits_for_nary_term_expr!(Add);
