use ast2::prelude::*;

use std::iter::FromIterator;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        Equals
    };
}

/// Represents an n-ary equality expression.
/// 
/// # Note
/// 
/// - The type of this expression is depending on the type of
///   its children.
/// - Its children must all have the same type as this equality
///   expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Equals {
    /// The child expressions.
    childs: Vec<AnyExpr>,
    /// The type of the childs expression.
    childs_ty: Type
}

impl Equals {
    /// Creates a new `Equals` expression from the given iterator over expressions.
    /// 
    /// # Errors
    /// 
    /// - If the given iterator iterates over less than two expressions.
    /// - If not all iterated expressions share the same type.
    pub fn new<E>(exprs: E) -> Result<Equals, String>
        where E: IntoIterator<Item=AnyExpr>
    {
        let childs = Vec::from_iter(exprs);
        if childs.len() < 2 {
            return Err("Require at least 2 child expressions to create a new Equals expression.".into())
        }
        let common_ty = childs.first().unwrap().ty();
        if childs.iter().any(|e| e.ty() != common_ty) {
            return Err("Requires all child expressions to have the same type to create a new Equals expression".into())
        }
        Ok(Equals{childs_ty: common_ty, childs})
    }
}

impl HasType for Equals {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl HasKind for Equals {
    fn kind(&self) -> ExprKind {
        ExprKind::Equals
    }
}

impl HasArity for Equals {
    fn arity(&self) -> usize {
        self.childs.len()
    }
}

impl From<Equals> for AnyExpr {
    fn from(equals: Equals) -> AnyExpr {
        AnyExpr::Equals(equals)
    }
}

impl Childs for Equals {
    fn childs(&self) -> ChildsIter {
        ChildsIter::nary(&self.childs)
    }
}

impl ChildsMut for Equals {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::nary(&mut self.childs)
    }
}

impl IntoChilds for Equals {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::nary(self.childs)
    }
}
