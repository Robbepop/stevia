use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::{
        Sub
    };
}

/// Binary Sub term expression.
/// 
/// Subtracts the right child from the left: left - right
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sub {
    /// The two child term expressions.
    pub childs: P<BinExprChilds>,
    /// The bit width of this expression.
    /// 
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub width: BitWidth
}

impl Sub {
    /// Returns a new `Sub` term expression with the given child term expressions.
    /// 
    /// # Errors
    /// 
    /// - If any of the two given child expressions is not of bitvec type or
    ///   has an unmatching bit width to the given bit width.
    pub fn new(width: BitWidth, lhs: Expr, rhs: Expr) -> Result<Sub, String> {
        checks::expect_bitvec_ty_and_width(&lhs, width)?;
        checks::expect_bitvec_ty_and_width(&rhs, width)?;
        Ok(Sub{ width, childs: BinExprChilds::new_boxed(lhs, rhs) })
    }
}

impl Childs for Sub {
    fn childs(&self) -> ChildsIter {
        self.childs.childs()
    }
}

impl ChildsMut for Sub {
    fn childs_mut(&mut self) -> ChildsIterMut {
        self.childs.childs_mut()
    }
}

impl IntoChilds for Sub {
    fn into_childs(self) -> IntoChildsIter {
        self.childs.into_childs()
    }
}

impl HasType for Sub {
    fn ty(&self) -> Type {
        self.width.ty()
    }
}

impl HasKind for Sub {
    fn kind(&self) -> ExprKind {
        ExprKind::Sub
    }
}

impl HasArity for Sub {
    fn arity(&self) -> usize {
        2
    }
}

impl From<Sub> for Expr {
    fn from(sub: Sub) -> Expr {
        Expr::Sub(sub)
    }
}
