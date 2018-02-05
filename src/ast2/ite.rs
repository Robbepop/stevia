use ast2::prelude::*;

/// Exports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        IfThenElse,
        IfThenElseChilds
    };
}

/// The If-Then-Else expression.
/// 
/// # Note
/// 
/// - This has a `Type` that is dependend on its childs.
/// - Its condition is always of boolean type.
/// - Its `then_case` and `else_case` childs are asserted
///   to be of same `Type` as their parent `IfThenElse` expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IfThenElse{
    /// The children of this expression.
	pub childs: P<IfThenElseChilds>,
    /// The type of this expression.
	pub ty: Type
}

/// The data of an `IfThenElse` expression.
/// 
/// # Detail
/// 
/// This is an implementation detail for the `IfThenElse`
/// expression and required to create an indirection to
/// its child expressions to break infinite dependency.
/// This also has the positive effect of storing all child
/// expressions densely in the memory.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IfThenElseChilds {
    /// The condition of the parent `IfThenElse` expression.
    /// 
    /// This must always be of boolean type.
	pub cond: AnyExpr,
    /// The then case of the parent `IfThenElse` expression.
    /// 
    /// This must always have the same type as its parent
    /// `IfThenElse` expresssion and thus the sibling
    /// `else_case` expression.
	pub then_case: AnyExpr,
    /// The else case of the parent `IfThenElse` expression.
    /// 
    /// This must always have the same type as its parent
    /// `IfThenElse` expresssion and thus the sibling
    /// `then_case` expression.
	pub else_case: AnyExpr
}

impl IfThenElseChilds {
    /// Consumes `self` and returns both of its childs as tuple.
    pub fn into_childs_tuple(self) -> (AnyExpr, AnyExpr, AnyExpr) {
        (self.cond, self.then_case, self.else_case)
    }
}

impl IfThenElse {
    /// Returns a new `IfThenElse` expression from the given condition, then-case and else-case.
    /// 
    /// # Errors
    /// 
    /// - If the given condition is not of boolean type.
    /// - If the given then-case and else-case do not have a common type.
    pub fn new(cond: AnyExpr, then_case: AnyExpr, else_case: AnyExpr) -> Result<IfThenElse, String> {
        if cond.ty() != Type::Bool {
            return Err("The condition of an if-then-else expression must be of boolean type.".into())
        }
        if !have_common_ty(&then_case, &else_case) {
            return Err("The types of the then-case and else-case of an if-then-else expression must be the same.".into())
        }
        Ok(unsafe{IfThenElse::new_unchecked(cond, then_case, else_case)})
    }

    /// Returns a new `IfThenElse` expression from the given condition, then-case and else-case.
    /// 
    /// # Note
    /// 
    /// This function is unsafe since it does not perform some checks to secure invariants.
    /// Use it if you already asserted the nessecary invariants.
    /// 
    /// # Panics
    /// 
    /// - If the given then-case and else-case do not have a common type.
    pub unsafe fn new_unchecked(cond: AnyExpr, then_case: AnyExpr, else_case: AnyExpr) -> IfThenElse {
        let common_ty = common_ty(&then_case, &else_case).unwrap();
        IfThenElse{
            ty: common_ty,
            childs: P::new(IfThenElseChilds{cond, then_case, else_case})
        }
    }
}

impl Childs for IfThenElseChilds {
    fn childs(&self) -> ChildsIter {
        ChildsIter::ternary(&self.cond, &self.then_case, &self.else_case)
    }
}

impl ChildsMut for IfThenElseChilds {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::ternary(&mut self.cond, &mut self.then_case, &mut self.else_case)
    }
}

impl IntoChilds for IfThenElseChilds {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::ternary(self.cond, self.then_case, self.else_case)
    }
}

impl HasType for IfThenElse {
    fn ty(&self) -> Type {
        self.ty
    }
}

impl HasKind for IfThenElse {
    fn kind(&self) -> ExprKind {
        ExprKind::IfThenElse
    }
}

impl HasArity for IfThenElse {
    fn arity(&self) -> usize {
        3
    }
}

impl From<IfThenElse> for AnyExpr {
    fn from(ite: IfThenElse) -> AnyExpr {
        AnyExpr::IfThenElse(ite)
    }
}

impl Childs for IfThenElse {
    fn childs(&self) -> ChildsIter {
        self.childs.childs()
    }
}

impl ChildsMut for IfThenElse {
    fn childs_mut(&mut self) -> ChildsIterMut {
        self.childs.childs_mut()
    }
}

impl IntoChilds for IfThenElse {
    fn into_childs(self) -> IntoChildsIter {
        self.childs.into_childs()
    }
}
