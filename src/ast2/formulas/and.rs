use ast2::prelude::*;

pub mod prelude {
    pub use super::{
        And
    };
}

/// N-ary And formula expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct And {
    /// The child formula expressions.
    pub childs: Vec<Expr>,
}

impl And {
    /// Creates a new `And` formula expression.
    /// 
    /// # Errors
    /// 
    /// - If the given iterator has less than two elements.
    /// - If not all expressions yielded by the given iteration are of boolean type.
    pub fn new<I>(childs: I) -> Result<And, String>
        where I: IntoIterator<Item = Expr>
    {
        let childs = childs.into_iter().collect::<Vec<_>>();
        if childs.len() < 2 {
            return Err("Requires at least 2 child expressions to create And formula expression.".into())
        }
        if childs.iter().any(|e| e.ty() != Type::Bool) {
            return Err("Requires all child expressions to be of boolean type.".into())
        }
        Ok(And{childs})
    }
}

impl Childs for And {
    fn childs(&self) -> ChildsIter {
        ChildsIter::nary(&self.childs)
    }
}

impl ChildsMut for And {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::nary(&mut self.childs)
    }
}

impl IntoChilds for And {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::nary(self.childs)
    }
}

impl HasType for And {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl HasKind for And {
    fn kind(&self) -> ExprKind {
        ExprKind::And
    }
}

impl HasArity for And {
    fn arity(&self) -> usize {
        self.childs.len()
    }
}

impl From<And> for Expr {
    fn from(and: And) -> Expr {
        Expr::And(and)
    }
}
