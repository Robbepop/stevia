use ast2::prelude::*;
use ast2::terms::checks;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::Mul;
}

/// N-ary Mul term expression.
///
/// Arithmetically multiplies all child term expressions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Mul {
    /// The child formula expressions.
    pub childs: Vec<AnyExpr>,
    /// The bit width of this expression.
    ///
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub bitvec_ty: BitvecTy,
}

impl Mul {
    /// Returns a new binary `Mul` expression for the given two child expressions.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` are not of bitvec type.
    /// - If `lhs` or `rhs` are of bitvec type but do not have matching bit widths.
    pub fn binary(bitvec_ty: BitvecTy, lhs: AnyExpr, rhs: AnyExpr) -> Result<Mul, String> {
        checks::expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        checks::expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        Ok(Mul{ bitvec_ty, childs: vec![lhs, rhs] })
    }

    /// Creates a new n-ary `Mul` formula expression.
    ///
    /// # Errors
    ///
    /// - If the given iterator has less than two elements.
    /// - If not all expressions yielded by the given iteration are of boolean type.
    pub fn nary<I>(bitvec_ty: BitvecTy, childs: I) -> Result<Mul, String>
    where
        I: IntoIterator<Item = AnyExpr>,
    {
        let childs = childs.into_iter().collect::<Vec<_>>();
        if childs.len() < 2 {
            return Err(
                "Requires at least two child expressions to create an Mul term expression.".into(),
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
        Ok(Mul{ bitvec_ty, childs })
    }
}

impl_traits_for_nary_term_expr!(Mul);
