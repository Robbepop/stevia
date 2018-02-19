use ast2::prelude::*;
use ast2::formulas::checks;

pub mod prelude {
    pub use super::{
        And
    };
}

/// N-ary And formula expression.
/// 
/// This does a boolean conjunction for all child formula expressions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct And {
    /// The child formula expressions.
    pub childs: Vec<AnyExpr>,
}

impl And {
    /// Returns a new binary `And` formula expression with the given child expressions.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` are not of bool type.
    pub fn binary<E1, E2>(lhs: E1, rhs: E2) -> Result<And, String>
        where E1: Into<AnyExpr>,
              E2: Into<AnyExpr>
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        checks::expect_bool_ty(&lhs)?;
        checks::expect_bool_ty(&rhs)?;
        Ok(And{ childs: vec![lhs, rhs] })
    }

    /// Returns a new binary `And` formula expression with the given child expressions.
    /// 
    /// # Safety
    /// 
    /// This is unsafe since it does not check the type requirements for the given child expressions.
    pub unsafe fn binary_unchecked<E1, E2>(lhs: E1, rhs: E2) -> And
        where E1: Into<AnyExpr>,
              E2: Into<AnyExpr>
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        And{ childs: vec![lhs, rhs] }
    }

    /// Creates a new n-ary `And` formula expression.
    /// 
    /// # Errors
    /// 
    /// - If the given iterator has less than two elements.
    /// - If not all expressions yielded by the given iteration are of boolean type.
    pub fn nary<I>(childs: I) -> Result<And, String>
        where I: IntoIterator<Item = AnyExpr>
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

impl BoolExpr for And {}

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

impl From<And> for AnyExpr {
    fn from(and: And) -> AnyExpr {
        AnyExpr::And(and)
    }
}

impl ChildsVec for And {
    fn childs_vec(&self) -> &Vec<AnyExpr> {
        &self.childs
    }
}

impl ChildsVecMut for And {
    fn childs_vec_mut(&mut self) -> &mut Vec<AnyExpr> {
        &mut self.childs
    }
}

impl IntoChildsVec for And {
    fn into_childs_vec(self) -> Vec<AnyExpr> {
        self.childs
    }
}
