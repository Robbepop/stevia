use ast2::prelude::*;

pub mod prelude {
    pub use super::{
        Not
    };
}

/// The logical Not formula expression.
/// 
/// This negate the inner boolean expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Not {
    child: P<Expr>
}

impl Not {
    /// Creates a new `Not` formula expression for the given child expression.
    /// 
    /// # Errors
    /// 
    /// - If the given child expression is not of boolean type.
    pub fn new<E>(child: E) -> Result<Not, String>
        where E: IntoBoxExpr
    {
        let child = child.into_box_expr();
        if child.ty() != Type::Bool {
            return Err("Requires inner expression to be of boolean type for Not formula expression.".into())
        }
        Ok(Not{child})
    }
}

impl Childs for Not {
    fn childs(&self) -> ChildsIter {
        ChildsIter::unary(&self.child)
    }
}

impl ChildsMut for Not {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::unary(&mut self.child)
    }
}

impl IntoChilds for Not {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::unary(*self.child)
    }
}

impl HasType for Not {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl HasKind for Not {
    fn kind(&self) -> ExprKind {
        ExprKind::Not
    }
}

impl HasArity for Not {
    fn arity(&self) -> usize {
        1
    }
}

impl From<Not> for Expr {
    fn from(not: Not) -> Expr {
        Expr::Not(not)
    }
}
