use crate::{
    prelude::*,
    ty::{
        expect_type,
        Type,
        HasType,
    },
    iter::{
        Children,
        ChildrenMut,
        IntoChildren,
    },
};

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
        let child = child.into_boxed_any_expr();
        debug_assert!(expect_type(Type::Bool, &*child).is_ok());
        Not{ child }
    }
}

impl BoolExpr for Not {}

impl Children for Not {
	#[inline]
	fn children_slice(&self) -> &[AnyExpr] {
		unsafe {
			std::slice::from_raw_parts(&*self.child as *const AnyExpr, 1)
		}
	}
}

impl ChildrenMut for Not {
	#[inline]
	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		unsafe {
			std::slice::from_raw_parts_mut(&mut *self.child as *mut AnyExpr, 1)
		}
	}
}

impl IntoChildren for Not {
    fn into_children_vec(self) -> Vec<AnyExpr> {
		let ptr = Box::leak(self.child) as *mut AnyExpr;
		unsafe {
			Vec::from_raw_parts(ptr, 1, 1)
		}
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
