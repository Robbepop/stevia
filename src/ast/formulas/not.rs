use ast::prelude::*;

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
    /// The inner child formula expression.
    pub child: P<AnyExpr>
}

impl Not {
    /// Creates a new `Not` formula expression for the given child expression.
    /// 
    /// # Errors
    /// 
    /// - If the given child expression is not of boolean type.
    pub fn new<E>(child: E) -> Result<Not, String>
        where E: IntoBoxedAnyExpr
    {
        let child = child.into_boxed_any_expr();
        if child.ty() != Type::Bool {
            return Err("Requires inner expression to be of boolean type for Not formula expression.".into())
        }
        Ok(Not{child})
    }

    /// Creates a new `Not` formula expression for the given child expression.
    /// 
    /// # Unsafe
    /// 
    /// This is unsafe since it does not type-check its argument.
    pub unsafe fn new_unchecked<E>(child: E) -> Not
        where E: IntoBoxedAnyExpr
    {
        Not{child: child.into_boxed_any_expr()}
    }
}

impl BoolExpr for Not {}

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

impl From<Not> for AnyExpr {
    fn from(not: Not) -> AnyExpr {
        AnyExpr::Not(not)
    }
}

impl UnaryExpr for Not {}

impl SingleChild for Not {
    fn single_child(&self) -> &AnyExpr {
        &*self.child
    }

    fn single_child_mut(&mut self) -> &mut AnyExpr {
        &mut *self.child
    }

    fn into_single_child(self) -> AnyExpr {
        *self.child
    }

    fn into_boxed_single_child(self) -> Box<AnyExpr> {
        self.child
    }
}
