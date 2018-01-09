use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::{
        Urem
    };
}

/// Binary Urem (unsigned remainder) term expression.
/// 
/// # Note
/// 
/// - On machine level signed and unsigned division are
///   two different operations and have to be treated differently.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Urem {
    /// The two child term expressions.
    pub childs: P<BinExprChilds>,
    /// The bit width of this expression.
    /// 
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub width: BitWidth
}

impl Urem {
    /// Returns a new `Urem` (unsigned remaainder) term expression with the given
    /// child term expressions.
    /// 
    /// # Errors
    /// 
    /// - If any of the two given child expressions is not of bitvec type or
    ///   has an unmatching bit width to the given bit width.
    pub fn new(width: BitWidth, lhs: Expr, rhs: Expr) -> Result<Urem, String> {
        checks::expect_bitvec_ty_and_width(&lhs, width)?;
        checks::expect_bitvec_ty_and_width(&rhs, width)?;
        Ok(Urem{ width, childs: BinExprChilds::new_boxed(lhs, rhs) })
    }
}

impl Childs for Urem {
    fn childs(&self) -> ChildsIter {
        self.childs.childs()
    }
}

impl ChildsMut for Urem {
    fn childs_mut(&mut self) -> ChildsIterMut {
        self.childs.childs_mut()
    }
}

impl IntoChilds for Urem {
    fn into_childs(self) -> IntoChildsIter {
        self.childs.into_childs()
    }
}

impl HasType for Urem {
    fn ty(&self) -> Type {
        self.width.ty()
    }
}

impl HasKind for Urem {
    fn kind(&self) -> ExprKind {
        ExprKind::Urem
    }
}

impl HasArity for Urem {
    fn arity(&self) -> usize {
        2
    }
}

impl From<Urem> for Expr {
    fn from(urem: Urem) -> Expr {
        Expr::Urem(urem)
    }
}
