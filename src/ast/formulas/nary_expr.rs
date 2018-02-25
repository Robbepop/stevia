use ast::prelude::*;
use ast::formulas::checks;
use ast::terms::ExprMarker;

use std::marker::PhantomData;

pub mod prelude {
    pub use super::{
        NaryBoolExpr
    };
}

/// Generic n-ary formula expression.
/// 
/// Used by concrete n-ary formula expressions as base template.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NaryBoolExpr<M> {
    /// The child formula expressions.
    pub childs: Vec<AnyExpr>,
    /// Marker to differentiate bool expressions from each
    /// other using the type system.
    marker: PhantomData<M>
}

impl<M> NaryBoolExpr<M> {
    /// Returns a new n-ary formula expression from the given vector of child expressions.
    /// 
    /// # Note
    /// 
    /// This is just a convenience method and performs no type checking on its arguments.
    fn from_vec(children: Vec<AnyExpr>) -> Self {
        Self{ childs: children, marker: PhantomData }
    }

    /// Returns a new n-ary formula expression with the given child expressions.
    /// 
    /// # Note
    /// 
    /// Since the given child expressions are the only child expressions this
    /// n-ary formula expression is actually a binary formula expression upon
    /// construction.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` are not of bool type.
    pub fn binary<E1, E2>(lhs: E1, rhs: E2) -> Result<Self, String>
        where E1: Into<AnyExpr>,
              E2: Into<AnyExpr>
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        checks::expect_bool_ty(&lhs)?;
        checks::expect_bool_ty(&rhs)?;
        Ok(Self::from_vec(vec![lhs, rhs]))
    }

    /// Returns a new n-ary formula expression with the given child expressions.
    /// 
    /// # Note
    /// 
    /// Since the given child expressions are the only child expressions this
    /// n-ary formula expression is actually a binary formula expression upon
    /// construction.
    /// 
    /// # Safety
    /// 
    /// This is unsafe since it does not check the type requirements for the given child expressions.
    pub unsafe fn binary_unchecked<E1, E2>(lhs: E1, rhs: E2) -> Self
        where E1: Into<AnyExpr>,
              E2: Into<AnyExpr>
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        Self::from_vec(vec![lhs, rhs])
    }

    /// Returns a new n-ary formula expression.
    /// 
    /// # Errors
    /// 
    /// - If the given iterator has less than two elements.
    /// - If not all expressions yielded by the given iteration are of boolean type.
    pub fn nary<I>(childs: I) -> Result<Self, String>
        where I: IntoIterator<Item = AnyExpr>
    {
        let childs = childs.into_iter().collect::<Vec<_>>();
        if childs.len() < 2 {
            return Err("Requires at least 2 child expressions to create an n-ary formula expression.".into())
        }
        if childs.iter().any(|e| e.ty() != Type::Bool) {
            return Err("Requires all child expressions to be of boolean type.".into())
        }
        Ok(Self::from_vec(childs))
    }
}

impl<M> BoolExpr for NaryBoolExpr<M>
    where Self: Into<AnyExpr>
{}

impl<M> Childs for NaryBoolExpr<M> {
    fn childs(&self) -> ChildsIter {
        ChildsIter::nary(&self.childs)
    }
}

impl<M> ChildsMut for NaryBoolExpr<M> {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::nary(&mut self.childs)
    }
}

impl<M> IntoChilds for NaryBoolExpr<M> {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::nary(self.childs)
    }
}

impl<M> HasType for NaryBoolExpr<M> {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl<M> HasKind for NaryBoolExpr<M>
    where M: ExprMarker
{
    fn kind(&self) -> ExprKind {
        M::EXPR_KIND
    }
}

impl<M> HasArity for NaryBoolExpr<M> {
    fn arity(&self) -> usize {
        self.childs.len()
    }
}

impl<M> ChildsVec for NaryBoolExpr<M> {
    fn childs_vec(&self) -> &Vec<AnyExpr> {
        &self.childs
    }
}

impl<M> ChildsVecMut for NaryBoolExpr<M> {
    fn childs_vec_mut(&mut self) -> &mut Vec<AnyExpr> {
        &mut self.childs
    }
}

impl<M> IntoChildsVec for NaryBoolExpr<M> {
    fn into_childs_vec(self) -> Vec<AnyExpr> {
        self.childs
    }
}
