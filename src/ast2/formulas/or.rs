use ast2::prelude::*;
use ast2::formulas::checks;

pub mod prelude {
    pub use super::{
        Or
    };
}

/// N-ary Or formula expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Or {
    /// The child formula expressions.
    pub childs: Vec<AnyExpr>,
}

impl Or {
    /// Returns a new binary `Or` formula expression with the given child expressions.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` are not of bool type.
    pub fn binary(lhs: AnyExpr, rhs: AnyExpr) -> Result<Or, String> {
        checks::expect_bool_ty(&lhs)?;
        checks::expect_bool_ty(&rhs)?;
        Ok(Or{ childs: vec![lhs, rhs] })
    }

    /// Creates a new n-ary `Or` formula expression.
    /// 
    /// # Errors
    /// 
    /// - If the given iterator has less than two elements.
    /// - If not all expressions yielded by the given iteration are of boolean type.
    pub fn nary<I>(childs: I) -> Result<Or, String>
        where I: IntoIterator<Item = AnyExpr>
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

impl BoolExpr for Or {}

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

impl From<Or> for AnyExpr {
    fn from(or: Or) -> AnyExpr {
        AnyExpr::Or(or)
    }
}
