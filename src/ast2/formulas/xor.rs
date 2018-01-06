use ast2::prelude::*;

pub mod prelude {
    pub use super::{
        Xor
    };
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Xor {
    pub childs: P<BinExprChilds>
}

impl Xor {
    pub fn new(lhs: Expr, rhs: Expr) -> Xor {
        Xor{ childs: BinExprChilds::new_boxed(lhs, rhs) }
    }
}

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
