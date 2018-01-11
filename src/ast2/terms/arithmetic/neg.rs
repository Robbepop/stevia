use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::{
        Neg
    };
}

/// The arithmetic negation term expression.
/// 
/// This negate the inner term expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Neg {
    /// The inner child formula expression.
    pub child: P<AnyExpr>,
    /// The bit width of this term expression.
    pub width: BitWidth
}

impl Neg {
    /// Creates a new `Neg` term expression for the given child expression.
    /// 
    /// # Errors
    /// 
    /// - If the given child expression is not of bitvec type with the
    ///   proper given bit width specified.
    pub fn new<E>(width: BitWidth, child: E) -> Result<Neg, String>
        where E: IntoBoxedAnyExpr
    {
        let child = child.into_boxed_any_expr();
        let bvw = checks::expect_bitvec_ty(&*child)
            .map_err(|_| String::from(
                "Requires inner expression to be of bitvec type for Neg term expression."))?;
        if bvw != width {
            return Err("Required inner bitvec to have the same bitwidth as specified.".into())
        }
        Ok(Neg{width, child})
    }
}

impl Childs for Neg {
    fn childs(&self) -> ChildsIter {
        ChildsIter::unary(&self.child)
    }
}

impl ChildsMut for Neg {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::unary(&mut self.child)
    }
}

impl IntoChilds for Neg {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::unary(*self.child)
    }
}

impl HasType for Neg {
    fn ty(&self) -> Type {
        self.width.ty()
    }
}

impl HasKind for Neg {
    fn kind(&self) -> ExprKind {
        ExprKind::Neg
    }
}

impl HasArity for Neg {
    fn arity(&self) -> usize {
        1
    }
}

impl From<Neg> for AnyExpr {
    fn from(neg: Neg) -> AnyExpr {
        AnyExpr::Neg(neg)
    }
}
