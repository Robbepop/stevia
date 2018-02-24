use ast2::prelude::*;
use ast2::terms::checks;

use std::iter::FromIterator;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        BitvecEquals
    };
}

/// N-ary equality expression for bitvectors.
/// 
/// Evaluates to `true` if all child bitvec expressions evalute
/// to the same value, else evaluates to `false`.
/// 
/// # Note
/// 
/// - All child bitvec expressions must have the same bit width.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitvecEquals {
    /// The child expressions.
    pub childs: Vec<AnyExpr>,
    /// The common bit width of all child bitvec expressions.
    pub childs_bitvec_ty: BitvecTy
}

impl BitvecEquals {
    /// Returns a new binary `BitvecEquals` expression for the given two child expressions.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` are not of bitvec type.
    /// - If `lhs` or `rhs` are of bitvec type but do not have matching bit widths.
    pub fn binary<E1, E2>(bitvec_ty: BitvecTy, lhs: E1, rhs: E2) -> Result<BitvecEquals, String>
        where E1: Into<AnyExpr>,
              E2: Into<AnyExpr>
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        checks::expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        checks::expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        Ok(BitvecEquals{ childs_bitvec_ty: bitvec_ty, childs: vec![lhs, rhs] })
    }

    /// Returns a new binary `BitvecEquals` expression for the given two child expressions.
    /// 
    /// # Note
    /// 
    /// Infers the concrete bitvector type of the resulting expression from its childs.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` do not share a common bitvec type.
    pub fn binary_infer<E1, E2>(lhs: E1, rhs: E2) -> Result<BitvecEquals, String>
        where E1: Into<AnyExpr>,
              E2: Into<AnyExpr>
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        let common_ty = checks::expect_common_bitvec_ty(&lhs, &rhs)?;
        Ok(BitvecEquals{ childs_bitvec_ty: common_ty, childs: vec![lhs, rhs] })
    }

    /// Creates a new n-ary `BitvecEquals` expression from the given iterator over expressions.
    /// 
    /// # Errors
    /// 
    /// - If the given iterator iterates over less than two expressions.
    /// - If not all iterated expressions are of bitvec type with the given bit width.
    pub fn nary<E>(bitvec_ty: BitvecTy, exprs: E) -> Result<BitvecEquals, String>
        where E: IntoIterator<Item=AnyExpr>
    {
        let childs = Vec::from_iter(exprs);
        if childs.len() < 2 {
            return Err("Require at least 2 child expressions to create a new BitvecEquals expression.".into())
        }
        for child in &childs {
            checks::expect_concrete_bitvec_ty(child, bitvec_ty)?;
        }
        Ok(BitvecEquals{ childs_bitvec_ty: bitvec_ty, childs })
    }

    /// Creates a new n-ary `BitvecEquals` expression from the given iterator over expressions.
    /// 
    /// This automatically infers the common bitvector type of its given child expressions.
    /// 
    /// # Errors
    /// 
    /// - If the given iterator yields less than two expressions.
    /// - If not all yielded expressions are of the same bitvec type.
    pub fn nary_infer<E>(exprs: E) -> Result<BitvecEquals, String>
        where E: IntoIterator<Item=AnyExpr>
    {
        let childs = exprs.into_iter().collect::<Vec<_>>();
        if childs.len() < 2 {
            return Err("Require at least 2 child expressions to create a new BitvecEquals expression.".into())
        }
        let childs_bitvec_ty = checks::expect_common_bitvec_ty_n(&childs)?;
        Ok(BitvecEquals{ childs_bitvec_ty, childs })
    }
}

impl HasType for BitvecEquals {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl HasKind for BitvecEquals {
    fn kind(&self) -> ExprKind {
        ExprKind::BitvecEquals
    }
}

impl HasArity for BitvecEquals {
    fn arity(&self) -> usize {
        self.childs.len()
    }
}

impl From<BitvecEquals> for AnyExpr {
    fn from(bitvec_equals: BitvecEquals) -> AnyExpr {
        AnyExpr::BitvecEquals(bitvec_equals)
    }
}

impl Childs for BitvecEquals {
    fn childs(&self) -> ChildsIter {
        ChildsIter::nary(&self.childs)
    }
}

impl ChildsMut for BitvecEquals {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::nary(&mut self.childs)
    }
}

impl IntoChilds for BitvecEquals {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::nary(self.childs)
    }
}

impl ChildsVec for BitvecEquals {
    fn childs_vec(&self) -> &Vec<AnyExpr> {
        &self.childs
    }
}

impl ChildsVecMut for BitvecEquals {
    fn childs_vec_mut(&mut self) -> &mut Vec<AnyExpr> {
        &mut self.childs
    }
}

impl IntoChildsVec for BitvecEquals {
    fn into_childs_vec(self) -> Vec<AnyExpr> {
        self.childs
    }
}
