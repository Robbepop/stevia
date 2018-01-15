use ast2::prelude::*;
use ast2::formulas::checks;

pub mod prelude {
    pub use super::{
        Xor
    };
}

/// An XOR (either or) formula binary expression.
/// 
/// # Note
/// 
/// - This evaluates to true whenever exactly one of its child
///   expressions evaluates to `true`.
/// - This can be understood as the boolean not-equals.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Xor {
    /// The two child expressions.
    pub childs: P<BinExprChilds>
}

impl Xor {
    /// Returns a new `Xor` formula expression with the given child expressions.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` are not of bool type.
    pub fn new(lhs: AnyExpr, rhs: AnyExpr) -> Result<Xor, String> {
        checks::expect_bool_ty(&lhs)?;
        checks::expect_bool_ty(&rhs)?;
        Ok(Xor{ childs: BinExprChilds::new_boxed(lhs, rhs) })
    }
}

impl BoolExpr for Xor {}

impl Childs for Xor {
    fn childs(&self) -> ChildsIter {
        self.childs.childs()
    }
}

impl ChildsMut for Xor {
    fn childs_mut(&mut self) -> ChildsIterMut {
        self.childs.childs_mut()
    }
}

impl IntoChilds for Xor {
    fn into_childs(self) -> IntoChildsIter {
        self.childs.into_childs()
    }
}

impl HasType for Xor {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl HasKind for Xor {
    fn kind(&self) -> ExprKind {
        ExprKind::Xor
    }
}

impl HasArity for Xor {
    fn arity(&self) -> usize {
        2
    }
}

impl From<Xor> for AnyExpr {
    fn from(xor: Xor) -> AnyExpr {
        AnyExpr::Xor(xor)
    }
}
