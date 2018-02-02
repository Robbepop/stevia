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
    pub fn binary<E1, E2>(bitvec_ty: BitvecTy, lhs: E1, rhs: E2) -> Result<Add, String>
        where E1: Into<AnyExpr>,
              E2: Into<AnyExpr>
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        checks::expect_concrete_bitvec_ty(&lhs, bitvec_ty)?;
        checks::expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        Ok(Add{ bitvec_ty, childs: vec![lhs, rhs] })
    }

    /// Returns a new binary `Add` expression for the given two child expressions.
    /// 
    /// # Note
    /// 
    /// Infers the concrete bitvector type of the resulting expression from its childs.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` do not share a common bitvec type.
    pub fn binary_infer(lhs: AnyExpr, rhs: AnyExpr) -> Result<Add, String> {
        let common_ty = checks::expect_common_bitvec_ty(&lhs, &rhs)?;
        Ok(Add{ bitvec_ty: common_ty, childs: vec![lhs, rhs] })
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

    /// Creates a new n-ary `Add` expression from the given iterator over expressions.
    /// 
    /// This automatically infers the common bitvector type of its given child expressions.
    /// 
    /// # Errors
    /// 
    /// - If the given iterator yields less than two expressions.
    /// - If not all yielded expressions are of the same bitvec type.
    pub fn nary_infer<E>(exprs: E) -> Result<Add, String>
        where E: IntoIterator<Item=AnyExpr>
    {
        let childs = exprs.into_iter().collect::<Vec<_>>();
        if childs.len() < 2 {
            return Err("Require at least 2 child expressions to create a new Add expression.".into())
        }
        let bitvec_ty = checks::expect_common_bitvec_ty_n(&childs)?;
        Ok(Add{ bitvec_ty, childs })
    }
}

impl_traits_for_nary_term_expr!(Add);
