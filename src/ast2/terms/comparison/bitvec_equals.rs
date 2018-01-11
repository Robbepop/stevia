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
    pub fn binary(bitvec_ty: BitvecTy, lhs: AnyExpr, rhs: AnyExpr) -> Result<BitvecEquals, String> {
        checks::expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        checks::expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        Ok(BitvecEquals{ childs_bitvec_ty: bitvec_ty, childs: vec![lhs, rhs] })
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
        for child in childs.iter() {
            checks::expect_concrete_bitvec_ty(child, bitvec_ty)?;
        }
        Ok(BitvecEquals{ childs_bitvec_ty: bitvec_ty, childs })
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
