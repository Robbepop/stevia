use ast2::prelude::*;

/// Reexports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        AnyExpr,
        IntoBoxedAnyExpr
    };
}

/// Utility trait to transform `AnyExpr` or `Box<AnyExpr>` into `Box<AnyExpr>` and
/// without unboxing the input in the `Box<AnyExpr>` case.
pub trait IntoBoxedAnyExpr {
    /// Puts `self` into a `Box` if it isn't already boxed.
    fn into_boxed_any_expr(self) -> Box<AnyExpr>;
}

impl IntoBoxedAnyExpr for Box<AnyExpr> {
    /// Simply forwards the boxed `T`.
    /// 
    /// This is the "cheap" static case.
    fn into_boxed_any_expr(self) -> Box<AnyExpr> {
        self
    }
}

impl IntoBoxedAnyExpr for AnyExpr {
    /// Puts `T` into a box.
    /// 
    /// This is the "expensive" static case.
    fn into_boxed_any_expr(self) -> Box<AnyExpr> {
        Box::new(self)
    }
}

macro_rules! forall_expr_kinds {
	( $mac:ident ) => {
		$mac!{
            IfThenElse,
            Symbol,

            BoolConst,
            BoolEquals,
            Not,
            And,
            Or,
            Implies,
            Xor,

            BitvecConst,
            BitvecEquals,
            Neg,
            Add,
            Mul,
            Sub,
            UnsignedDiv,
            SignedDiv,
            SignedModulo,
            UnsignedRemainder,
            SignedRemainder,

            BitNot,
            BitAnd,
            BitOr,
            BitXor,

            SignedGreaterEquals,
            SignedGreaterThan,
            SignedLessEquals,
            SignedLessThan,
            UnsignedGreaterEquals,
            UnsignedGreaterThan,
            UnsignedLessEquals,
            UnsignedLessThan,

            ShiftLeft,
            LogicalShiftRight,
            ArithmeticShiftRight,

            Concat,
            Extract,
            SignExtend,
            ZeroExtend,

            ArrayEquals,
            ArrayRead,
            ArrayWrite
        }
    }
}

macro_rules! impl_expr_kinds {
	( $($names:ident),* ) => {
        /// Any expression.
        /// 
        /// There are different kinds of expressions and `AnyExpr`
        /// represents any one of them.
		#[derive(Debug, Clone, PartialEq, Eq, Hash)]
		pub enum AnyExpr {
			$($names(expr::$names)),*
		}

        impl HasType for AnyExpr {
            fn ty(&self) -> Type {
				use self::AnyExpr::*;
				match *self {
					$($names(ref expr) => expr.ty()),*
                }
            }
        }

        impl HasArity for AnyExpr {
            fn arity(&self) -> usize {
				use self::AnyExpr::*;
				match *self {
					$($names(ref expr) => expr.arity()),*
                }
            }
        }

        impl HasKind for AnyExpr {
            fn kind(&self) -> ExprKind {
				use self::AnyExpr::*;
				match *self {
					$($names(ref expr) => expr.kind()),*
                }
            }
        }

        impl Childs for AnyExpr {
            fn childs(&self) -> ChildsIter {
				use self::AnyExpr::*;
				match *self {
					$($names(ref expr) => expr.childs()),*
                }
            }
        }

        impl ChildsMut for AnyExpr {
            fn childs_mut(&mut self) -> ChildsIterMut {
				use self::AnyExpr::*;
				match *self {
					$($names(ref mut expr) => expr.childs_mut()),*
                }
            }
        }

        impl IntoChilds for AnyExpr {
            fn into_childs(self) -> IntoChildsIter {
				use self::AnyExpr::*;
				match self {
					$($names(expr) => expr.into_childs()),*
                }
            }
        }
    }
}

forall_expr_kinds!(impl_expr_kinds);
