use ast2::prelude::*;
use ast2::terms::prelude::*;
use ast2::terms::checks;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        BitOr
    };
}

/// N-ary bitwise-or term expression for bitvector expressions.
/// 
/// Bitwise-or for all child term expressions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitOr {
    /// The child bitvector expressions.
    pub childs: Vec<Expr>,
    /// The bit width of this expression.
    /// 
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub width: BitWidth
}

impl BitOr {
    /// Creates a new bitvector BitOr term expression for all of the child
    /// expressions yielded by the given iterator and with the given bit width.
    /// 
    /// # Errors
    /// 
    /// - If the given iterator yields less than two child expressions.
    /// - If not all yielded child expressions are of bitvec type with
    ///   the required bit width.
    pub fn new<I>(width: BitWidth, childs: I) -> Result<BitOr, String>
        where I: IntoIterator<Item = Expr>
    {
        let childs = childs.into_iter().collect::<Vec<_>>();
        if childs.len() < 2 {
            return Err("Requires at least two child expressions to create an BitOr term expression.".into())
        }
        if childs.iter().any(|c| checks::expect_bitvec_ty_and_width(c, width).is_err()) {
            return Err("Requires all child expressions to be of bitvec type with the expected bit width.".into())
        }
        Ok(BitOr{width, childs})
    }
}

impl Childs for BitOr {
    fn childs(&self) -> ChildsIter {
        ChildsIter::nary(&self.childs)
    }
}

impl ChildsMut for BitOr {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::nary(&mut self.childs)
    }
}

impl IntoChilds for BitOr {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::nary(self.childs)
    }
}

impl HasType for BitOr {
    fn ty(&self) -> Type {
        self.width.ty()
    }
}

impl HasKind for BitOr {
    fn kind(&self) -> ExprKind {
        ExprKind::BitAnd
    }
}

impl HasArity for BitOr {
    fn arity(&self) -> usize {
        self.childs.len()
    }
}

impl From<BitOr> for Expr {
    fn from(bitor: BitOr) -> Expr {
        Expr::BitOr(bitor)
    }
}
