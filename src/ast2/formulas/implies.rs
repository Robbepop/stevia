use ast2::prelude::*;
use ast2::formulas::checks;

pub mod prelude {
    pub use super::{
        Implies
    };
}

/// The implies formula binary expression.
/// 
/// This is equal to the implication of the boolean logic.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Implies {
    /// The two child expressions.
    pub childs: P<BinExprChilds>
}

impl Implies {
    /// Returns a new `Implies` formula expression with the given child expressions.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` are not of bool type.
    pub fn new(lhs: AnyExpr, rhs: AnyExpr) -> Result<Implies, String> {
        checks::expect_bool_ty(&lhs)?;
        checks::expect_bool_ty(&rhs)?;
        Ok(Implies{ childs: BinExprChilds::new_boxed(lhs, rhs) })
    }
}

impl Childs for Implies {
    fn childs(&self) -> ChildsIter {
        self.childs.childs()
    }
}

impl ChildsMut for Implies {
    fn childs_mut(&mut self) -> ChildsIterMut {
        self.childs.childs_mut()
    }
}

impl IntoChilds for Implies {
    fn into_childs(self) -> IntoChildsIter {
        self.childs.into_childs()
    }
}

impl HasType for Implies {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl HasKind for Implies {
    fn kind(&self) -> ExprKind {
        ExprKind::Implies
    }
}

impl HasArity for Implies {
    fn arity(&self) -> usize {
        2
    }
}

impl From<Implies> for AnyExpr {
    fn from(implies: Implies) -> AnyExpr {
        AnyExpr::Implies(implies)
    }
}
