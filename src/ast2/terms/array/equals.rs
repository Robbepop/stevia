use ast2::prelude::*;
use ast2::terms::checks;

use std::iter::FromIterator;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        ArrayEquals
    };
}

/// N-ary equality expression for arrays.
/// 
/// Evaluates to `true` if all child array expressions evalute
/// to the same value, else evaluates to `false`.
/// 
/// # Note
/// 
/// - All child array expressions must have the same index bit width
///   and value bit width.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArrayEquals {
    /// The child expressions.
    pub childs: Vec<AnyExpr>,
    /// The common array type of all child array expressions.
    pub childs_ty: ArrayTy
}

impl ArrayEquals {
    /// Returns a new binary `ArrayEquals` expression for the given two child expressions.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` are not of array type.
    /// - If `lhs` or `rhs` are of array type but do not have matching index or value bit widths.
    pub fn binary(array_ty: ArrayTy, lhs: AnyExpr, rhs: AnyExpr) -> Result<ArrayEquals, String> {
        checks::expect_concrete_array_ty(&rhs, array_ty)?;
        checks::expect_concrete_array_ty(&rhs, array_ty)?;
        Ok(ArrayEquals{ childs_ty: array_ty, childs: vec![lhs, rhs] })
    }

    /// Creates a new `ArrayEquals` expression from the given iterator over expressions.
    /// 
    /// # Errors
    /// 
    /// - If the given iterator iterates over less than two expressions.
    /// - If not all iterated expressions are of bitvec type with the given bit width.
    pub fn nary<E>(array_ty: ArrayTy, exprs: E) -> Result<ArrayEquals, String>
        where E: IntoIterator<Item=AnyExpr>
    {
        let childs = Vec::from_iter(exprs);
        if childs.len() < 2 {
            return Err("Require at least 2 child expressions to create a new ArrayEquals expression.".into())
        }
        for child in childs.iter() {
            checks::expect_concrete_array_ty(child, array_ty)?;
        }
        Ok(ArrayEquals{ childs_ty: array_ty, childs })
    }
}

impl HasType for ArrayEquals {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl HasKind for ArrayEquals {
    fn kind(&self) -> ExprKind {
        ExprKind::ArrayEquals
    }
}

impl HasArity for ArrayEquals {
    fn arity(&self) -> usize {
        self.childs.len()
    }
}

impl From<ArrayEquals> for AnyExpr {
    fn from(array_equals: ArrayEquals) -> AnyExpr {
        AnyExpr::ArrayEquals(array_equals)
    }
}

impl Childs for ArrayEquals {
    fn childs(&self) -> ChildsIter {
        ChildsIter::nary(&self.childs)
    }
}

impl ChildsMut for ArrayEquals {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::nary(&mut self.childs)
    }
}

impl IntoChilds for ArrayEquals {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::nary(self.childs)
    }
}
