use ast2::prelude::*;

pub mod prelude {
    pub use super::{
        Iff
    };
}

/// An Iff (if-and-only-if) formula binary expression.
/// 
/// # Note
/// 
/// - This evaluates to true whenever exactly both of its child
///   expressions evaluates to the same value.
/// - This can be understood as the boolean equals.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Iff {
    /// The two child expressions.
    pub childs: P<BinExprChilds>
}

impl Iff {
    /// Returns a new `Iff` formula expression with the given child expressions.
    pub fn new(lhs: Expr, rhs: Expr) -> Xor {
        Xor{ childs: BinExprChilds::new_boxed(lhs, rhs) }
    }
}

impl Childs for Iff {
    fn childs(&self) -> ChildsIter {
        self.childs.childs()
    }
}

impl ChildsMut for Iff {
    fn childs_mut(&mut self) -> ChildsIterMut {
        self.childs.childs_mut()
    }
}

impl IntoChilds for Iff {
    fn into_childs(self) -> IntoChildsIter {
        self.childs.into_childs()
    }
}

impl HasType for Iff {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl HasKind for Iff {
    fn kind(&self) -> ExprKind {
        ExprKind::Iff
    }
}

impl HasArity for Iff {
    fn arity(&self) -> usize {
        2
    }
}

impl From<Iff> for Expr {
    fn from(iff: Iff) -> Expr {
        Expr::Iff(iff)
    }
}
