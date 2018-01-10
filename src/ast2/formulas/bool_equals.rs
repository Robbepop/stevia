use ast2::prelude::*;
use ast2::formulas::checks;

pub mod prelude {
    pub use super::{
        BoolEquals
    };
}

/// An `BoolEquals` (also known as n-ary if-and-only-if) formula n-ary expression.
/// 
/// # Note
/// 
/// - This evaluates to true whenever exactly all of its child
///   expressions either evaluate to `true` or `false`.
/// - This can be understood as the logical equality.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BoolEquals {
    /// The child expressions.
    pub childs: Vec<Expr>
}

impl BoolEquals {
    /// Returns a new binary `BoolEquals` formula expression with the given child expressions.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` are not of bool type.
    pub fn binary(lhs: Expr, rhs: Expr) -> Result<BoolEquals, String> {
        checks::expect_bool_ty(&lhs)?;
        checks::expect_bool_ty(&rhs)?;
        Ok(BoolEquals{ childs: vec![lhs, rhs] })
    }

    /// Creates a new n-ary `BoolEquals` formula expression.
    /// 
    /// # Errors
    /// 
    /// - If the given iterator has less than two elements.
    /// - If not all expressions yielded by the given iteration are of boolean type.
    pub fn nary<I>(childs: I) -> Result<BoolEquals, String>
        where I: IntoIterator<Item = Expr>
    {
        let childs = childs.into_iter().collect::<Vec<_>>();
        if childs.len() < 2 {
            return Err("Requires at least 2 child expressions to create BoolEquals formula expression.".into())
        }
        if childs.iter().any(|e| e.ty() != Type::Bool) {
            return Err("Requires all child expressions to be of boolean type.".into())
        }
        Ok(BoolEquals{childs})
    }
}

impl Childs for BoolEquals {
    fn childs(&self) -> ChildsIter {
        ChildsIter::nary(&self.childs)
    }
}

impl ChildsMut for BoolEquals {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::nary(&mut self.childs)
    }
}

impl IntoChilds for BoolEquals {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::nary(self.childs)
    }
}

impl HasType for BoolEquals {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl HasKind for BoolEquals {
    fn kind(&self) -> ExprKind {
        ExprKind::BoolEquals
    }
}

impl HasArity for BoolEquals {
    fn arity(&self) -> usize {
        self.childs.len()
    }
}

impl From<BoolEquals> for Expr {
    fn from(bool_equals: BoolEquals) -> Expr {
        Expr::BoolEquals(bool_equals)
    }
}
