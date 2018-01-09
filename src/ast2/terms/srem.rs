use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::{
        Srem
    };
}

/// Binary Srem (signed remainder) term expression.
/// 
/// # Example
/// 
/// -21 divided by 4 gives -5 with a remainder of -1.
/// 
/// # Note
/// 
/// - On machine level signed and unsigned division are
///   two different operations and have to be treated differently.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Srem {
    /// The two child term expressions.
    pub childs: P<BinExprChilds>,
    /// The bit width of this expression.
    /// 
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub width: BitWidth
}

impl Srem {
    /// Returns a new `Srem` (signed remaainder) term expression with the given
    /// child term expressions.
    /// 
    /// # Errors
    /// 
    /// - If any of the two given child expressions is not of bitvec type or
    ///   has an unmatching bit width to the given bit width.
    pub fn new(width: BitWidth, lhs: Expr, rhs: Expr) -> Result<Srem, String> {
        checks::expect_bitvec_ty_and_width(&lhs, width)?;
        checks::expect_bitvec_ty_and_width(&rhs, width)?;
        Ok(Srem{ width, childs: BinExprChilds::new_boxed(lhs, rhs) })
    }
}

impl Childs for Srem {
    fn childs(&self) -> ChildsIter {
        self.childs.childs()
    }
}

impl ChildsMut for Srem {
    fn childs_mut(&mut self) -> ChildsIterMut {
        self.childs.childs_mut()
    }
}

impl IntoChilds for Srem {
    fn into_childs(self) -> IntoChildsIter {
        self.childs.into_childs()
    }
}

impl HasType for Srem {
    fn ty(&self) -> Type {
        self.width.ty()
    }
}

impl HasKind for Srem {
    fn kind(&self) -> ExprKind {
        ExprKind::Srem
    }
}

impl HasArity for Srem {
    fn arity(&self) -> usize {
        2
    }
}

impl From<Srem> for Expr {
    fn from(srem: Srem) -> Expr {
        Expr::Srem(srem)
    }
}
