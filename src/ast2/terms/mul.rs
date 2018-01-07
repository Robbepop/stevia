use ast2::prelude::*;
use ast2::terms::checks;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        Mul
    };
}

/// N-ary Mul formula expression.
/// 
/// Arithmetically multiplies all child term expressions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Mul {
    /// The child formula expressions.
    pub childs: Vec<Expr>,
    /// The bit width of this expression.
    /// 
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub width: BitWidth
}

impl Mul {
    /// Creates a new `Mul` formula expression.
    /// 
    /// # Errors
    /// 
    /// - If the given iterator has less than two elements.
    /// - If not all expressions yielded by the given iteration are of boolean type.
    pub fn new<I>(width: BitWidth, childs: I) -> Result<Mul, String>
        where I: IntoIterator<Item = Expr>
    {
        let childs = childs.into_iter().collect::<Vec<_>>();
        if childs.len() < 2 {
            return Err("Requires at least two child expressions to create an Mul term expression.".into())
        }
        if childs.iter().any(|c| checks::expect_bitvec_ty_and_width(c, width).is_err()) {
            return Err("Requires all child expressions to be of bitvec type with the expected bit width.".into())
        }
        Ok(Mul{width, childs})
    }
}

impl Childs for Mul {
    fn childs(&self) -> ChildsIter {
        ChildsIter::nary(&self.childs)
    }
}

impl ChildsMut for Mul {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::nary(&mut self.childs)
    }
}

impl IntoChilds for Mul {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::nary(self.childs)
    }
}

impl HasType for Mul {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl HasKind for Mul {
    fn kind(&self) -> ExprKind {
        ExprKind::Mul
    }
}

impl HasArity for Mul {
    fn arity(&self) -> usize {
        self.childs.len()
    }
}

impl From<Mul> for Expr {
    fn from(mul: Mul) -> Expr {
        Expr::Mul(mul)
    }
}
