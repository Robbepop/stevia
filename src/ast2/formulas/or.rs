use ast2::prelude::*;

pub mod prelude {
    pub use super::{
        Or
    };
}

/// N-ary Or formula expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Or {
    /// The child formula expressions.
    pub childs: Vec<Expr>,
}

impl Or {
    /// Creates a new `Or` formula expression.
    /// 
    /// # Errors
    /// 
    /// - If the given iterator has less than two elements.
    /// - If not all expressions yielded by the given iteration are of boolean type.
    pub fn new<I>(childs: I) -> Result<Or, String>
        where I: IntoIterator<Item = Expr>
    {
        let childs = childs.into_iter().collect::<Vec<_>>();
        if childs.len() < 2 {
            return Err("Requires at least 2 child expressions to create Or formula expression.".into())
        }
        if childs.iter().any(|e| e.ty() != Type::Bool) {
            return Err("Requires all child expressions to be of boolean type.".into())
        }
        Ok(Or{childs})
    }
}

impl Childs for Or {
    fn childs(&self) -> ChildsIter {
        ChildsIter::nary(&self.childs)
    }
}

impl ChildsMut for Or {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::nary(&mut self.childs)
    }
}

impl IntoChilds for Or {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::nary(self.childs)
    }
}

impl HasType for Or {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl HasKind for Or {
    fn kind(&self) -> ExprKind {
        ExprKind::Or
    }
}

impl HasArity for Or {
    fn arity(&self) -> usize {
        self.childs.len()
    }
}

impl From<Or> for Expr {
    fn from(or: Or) -> Expr {
        Expr::Or(or)
    }
}
