use ast::prelude::*;

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
    pub fn new_with_type<E>(bitvec_ty: BitvecTy, child: E) -> Result<BitNot, String>
        where E: IntoBoxedAnyExpr
    {
        let child = child.into_boxed_any_expr();
        expect_concrete_bitvec_ty(&*child, bitvec_ty)?;
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
    pub fn new<E>(child: E) -> Result<BitNot, String>
        where E: IntoBoxedAnyExpr
    {
        let child = child.into_boxed_any_expr();
        let bitvec_ty = expect_bitvec_ty(&*child)?;
        Ok(BitNot{bitvec_ty, child})
    }
}

impl Children for BitNot {
    fn children(&self) -> ChildrenIter {
        ChildrenIter::unary(&self.child)
    }
}

impl ChildrenMut for BitNot {
    fn children_mut(&mut self) -> ChildrenIterMut {
        ChildrenIterMut::unary(&mut self.child)
    }
}

impl IntoChildren for BitNot {
    fn into_children(self) -> IntoChildrenIter {
        IntoChildrenIter::unary(*self.child)
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
