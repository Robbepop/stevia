use ast::prelude::*;

pub mod prelude {
    pub use super::Not;
}

/// The logical Not formula expression.
///
/// This negate the inner boolean expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Not {
    /// The inner child formula expression.
    pub child: P<AnyExpr>,
}

impl Not {
    /// Creates a new `Not` formula expression for the given child expression.
    ///
    /// # Errors
    ///
    /// - If the given child expression is not of boolean type.
    pub fn new<E>(child: E) -> ExprResult<Not>
    where
        E: IntoBoxedAnyExpr,
    {
        let child = child.into_boxed_any_expr();
        expect_type(Type::Bool, &*child)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(
                    "Expected boolean type for the single child expression of this Not expression.",
                )
            })?;
        Ok(Not { child })
    }

    /// Creates a new `Not` formula expression for the given child expression.
    ///
    /// # Unsafe
    ///
    /// This is unsafe since it does not type-check its argument.
    pub unsafe fn new_unchecked<E>(child: E) -> Not
    where
        E: IntoBoxedAnyExpr,
    {
        Not {
            child: child.into_boxed_any_expr(),
        }
    }
}

impl BoolExpr for Not {}

impl Children for Not {
    fn children(&self) -> ChildrenIter {
        ChildrenIter::unary(&self.child)
    }
}

impl ChildrenMut for Not {
    fn children_mut(&mut self) -> ChildrenIterMut {
        ChildrenIterMut::unary(&mut self.child)
    }
}

impl IntoChildren for Not {
    fn into_children(self) -> IntoChildrenIter {
        IntoChildrenIter::unary(*self.child)
    }
}

impl HasType for Not {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl HasKind for Not {
    fn kind(&self) -> ExprKind {
        ExprKind::Not
    }
}

impl HasArity for Not {
    fn arity(&self) -> usize {
        1
    }
}

impl From<Not> for AnyExpr {
    fn from(not: Not) -> AnyExpr {
        AnyExpr::Not(not)
    }
}

impl UnaryExpr for Not {}

impl SingleChild for Not {
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
