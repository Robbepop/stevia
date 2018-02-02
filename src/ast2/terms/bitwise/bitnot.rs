use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::{
        BitNot
    };
}

/// The bitwise not term expression.
/// 
/// This flips all bits of the inner term expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitNot {
    /// The inner child formula expression.
    pub child: P<AnyExpr>,
    /// The bit width of this term expression.
    pub bitvec_ty: BitvecTy
}

impl BitNot {
    /// Creates a new `BitNot` term expression for the given child expression.
    /// 
    /// # Errors
    /// 
    /// - If the given child expression is not of bitvec type with the
    ///   proper given bit width specified.
    pub fn new<E>(bitvec_ty: BitvecTy, child: E) -> Result<BitNot, String>
        where E: IntoBoxedAnyExpr
    {
        let child = child.into_boxed_any_expr();
        checks::expect_concrete_bitvec_ty(&*child, bitvec_ty)?;
        Ok(BitNot{bitvec_ty, child})
    }

    /// Creates a new `BitNot` term expression for the given child expression.
    /// 
    /// # Note
    /// 
    /// Infers the bitvector type for this expression from its child expression.
    /// 
    /// # Errors
    /// 
    /// - If the given child expression is not of bitvec type.
    pub fn new_infer<E>(child: E) -> Result<BitNot, String>
        where E: IntoBoxedAnyExpr
    {
        let child = child.into_boxed_any_expr();
        let bitvec_ty = checks::expect_bitvec_ty(&*child)?;
        Ok(BitNot{bitvec_ty, child})
    }
}

impl Childs for BitNot {
    fn childs(&self) -> ChildsIter {
        ChildsIter::unary(&self.child)
    }
}

impl ChildsMut for BitNot {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::unary(&mut self.child)
    }
}

impl IntoChilds for BitNot {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::unary(*self.child)
    }
}

impl HasType for BitNot {
    fn ty(&self) -> Type {
        self.bitvec_ty.ty()
    }
}

impl HasKind for BitNot {
    fn kind(&self) -> ExprKind {
        ExprKind::BitNot
    }
}

impl HasArity for BitNot {
    fn arity(&self) -> usize {
        1
    }
}

impl From<BitNot> for AnyExpr {
    fn from(bitnot: BitNot) -> AnyExpr {
        AnyExpr::BitNot(bitnot)
    }
}

impl UnaryExpr for BitNot {}

impl SingleChild for BitNot {
    fn single_child(&self) -> &AnyExpr {
        &*self.child
    }

    fn single_child_mut(&mut self) -> &mut AnyExpr {
        &mut *self.child
    }

    fn into_single_child(self) -> AnyExpr {
        *self.child
    }

    fn into_boxed_single_child(self) -> Box<AnyExpr> {
        self.child
    }
}
