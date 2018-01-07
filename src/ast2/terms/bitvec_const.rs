use ast2::prelude::*;

use apint::{ApInt, Width};

pub mod prelude {
    pub use super::{
        BitvecConst
    };
}

/// A constant bitvec term expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitvecConst {
    /// The constant bitvec value.
    pub val: ApInt,
    /// The type and bit width of the const value.
    pub ty: Type
}

impl From<ApInt> for BitvecConst {
    /// Creates a new `BitvecConst` from the given `ApInt`.
    fn from(apint: ApInt) -> BitvecConst {
        BitvecConst{
            ty: Type::Bitvec(apint.width()),
            val: apint
        }
    }
}

impl Childs for BitvecConst {
    fn childs(&self) -> ChildsIter {
        ChildsIter::none()
    }
}

impl ChildsMut for BitvecConst {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::none()
    }
}

impl IntoChilds for BitvecConst {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::none()
    }
}

impl HasType for BitvecConst {
    fn ty(&self) -> Type {
        self.ty
    }
}

impl HasKind for BitvecConst {
    fn kind(&self) -> ExprKind {
        ExprKind::BitvecConst
    }
}

impl HasArity for BitvecConst {
    fn arity(&self) -> usize {
        0
    }
}

impl From<BitvecConst> for Expr {
    fn from(bitvec_const: BitvecConst) -> Expr {
        Expr::BitvecConst(bitvec_const)
    }
}
