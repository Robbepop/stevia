use ast2::prelude::*;

/// Reexports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        Expr
    };
}

macro_rules! forall_expr_kinds {
	( $mac:ident ) => {
		$mac!{
            IfThenElse,
            Symbol,
            Equals,

            BoolConst,
            Not,
            And,
            Or,
            Implies,
            Xor,
            Iff,

            BitvecConst,
            Neg,
            Add,
            Mul,
            Sub,
            Udiv,
            Sdiv,
            Smod,
            Urem,
            Srem,

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
            ZeroExtend
        }
    }
}

macro_rules! impl_expr_kinds {
	( $($names:ident),* ) => {
        /// Any expression.
        /// 
        /// There are different kinds of expressions and `Expr`
        /// represents any one of them.
		#[derive(Debug, Clone, PartialEq, Eq, Hash)]
		pub enum Expr {
			$($names(expr::$names)),*
		}

        impl HasType for Expr {
            fn ty(&self) -> Type {
				use self::Expr::*;
				match *self {
					$($names(ref expr) => expr.ty()),*
                }
            }
        }

        impl HasArity for Expr {
            fn arity(&self) -> usize {
				use self::Expr::*;
				match *self {
					$($names(ref expr) => expr.arity()),*
                }
            }
        }

        impl HasKind for Expr {
            fn kind(&self) -> ExprKind {
				use self::Expr::*;
				match *self {
					$($names(ref expr) => expr.kind()),*
                }
            }
        }

        impl Childs for Expr {
            fn childs(&self) -> ChildsIter {
				use self::Expr::*;
				match *self {
					$($names(ref expr) => expr.childs()),*
                }
            }
        }

        impl ChildsMut for Expr {
            fn childs_mut(&mut self) -> ChildsIterMut {
				use self::Expr::*;
				match *self {
					$($names(ref mut expr) => expr.childs_mut()),*
                }
            }
        }

        impl IntoChilds for Expr {
            fn into_childs(self) -> IntoChildsIter {
				use self::Expr::*;
				match self {
					$($names(expr) => expr.into_childs()),*
                }
            }
        }
    }
}

forall_expr_kinds!(impl_expr_kinds);
