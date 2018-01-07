use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::{
        Udiv
    };
}

/// Binary Udiv (unsigned division) term expression.
/// 
/// Divides the left child by the right: left / right
/// 
/// # Note
/// 
/// - On machine level signed and unsigned division are
///   two different operations and have to be treated differently.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Udiv {
    /// The two child term expressions.
    pub childs: P<BinExprChilds>,
    /// The bit width of this expression.
    /// 
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub width: BitWidth
}

impl Udiv {
    /// Returns a new `Udiv` (unsigned division) term expression with the
    /// given child term expressions.
    /// 
    /// # Errors
    /// 
    /// - If any of the two given child expressions is not of bitvec type or
    ///   has an unmatching bit width to the given bit width.
    pub fn new(width: BitWidth, lhs: Expr, rhs: Expr) -> Result<Udiv, String> {
        checks::expect_bitvec_ty_and_width(&lhs, width)?;
        checks::expect_bitvec_ty_and_width(&rhs, width)?;
        Ok(Udiv{ width, childs: BinExprChilds::new_boxed(lhs, rhs) })
    }
}

impl Childs for Udiv {
    fn childs(&self) -> ChildsIter {
        self.childs.childs()
    }
}

impl ChildsMut for Udiv {
    fn childs_mut(&mut self) -> ChildsIterMut {
        self.childs.childs_mut()
    }
}

impl IntoChilds for Udiv {
    fn into_childs(self) -> IntoChildsIter {
        self.childs.into_childs()
    }
}

impl HasType for Udiv {
    fn ty(&self) -> Type {
        self.width.ty()
    }
}

impl HasKind for Udiv {
    fn kind(&self) -> ExprKind {
        ExprKind::Udiv
    }
}

impl HasArity for Udiv {
    fn arity(&self) -> usize {
        2
    }
}

impl From<Udiv> for Expr {
    fn from(udiv: Udiv) -> Expr {
        Expr::Udiv(udiv)
    }
}
