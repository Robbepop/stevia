
use ast::Type;
use ast::formulas::*;
use ast::terms::*;
use ast::traits::ExprTrait;
use ast::iterators::{Childs, ChildsMut, IntoChilds};
use ast::{Equals, IfThenElse, Symbol};

macro_rules! forall_expr_kinds {
	( $mac:ident ) => {
		$mac!{

			// TERM EXPRESSIONS

			BitVecConst,
			Neg,
			Add,
			Mul,
			Sub,
			Div,
			Mod,
			SignedDiv,
			SignedMod,
			SignedRem,

			BitNot,
			BitAnd,
			BitOr,
			BitXor,
			BitNand,
			BitNor,
			BitXnor,

			Lt,
			Le,
			Gt,
			Ge,
			SignedLt,
			SignedLe,
			SignedGt,
			SignedGe,

			Shl,
			Shr,
			SignedShr,

			Concat,
			Extract,
			Extend,
			SignedExtend,

			Read,
			Write,

			// FORMULA EXPRESSIONS

			BoolConst,

			Not,

			And,
			Or,
			Xor,
			Iff,
			Implies,

			ParamBool,

			// GENERIC EXPRESSIONS

			Equals,
			IfThenElse,
			Symbol
		}
	}
}

//=============================================================================
// Implementation of base methods for all expression kinds.
//=============================================================================

macro_rules! impl_expr_kinds {
	( $($names:ident),* ) => {
		#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
		pub enum ExprKind {
			$($names),*
		}

		#[derive(Debug, Clone, PartialEq, Eq, Hash)]
		pub enum Expr {
			$($names($names)),*
		}

		impl Expr {
			pub fn as_trait(&self) -> &ExprTrait {
				use self::Expr::*;
				match *self {
					$($names(ref expr) => expr),*
				}
			}

			pub fn as_trait_mut(&mut self) -> &mut ExprTrait {
				use self::Expr::*;
				match *self {
					$($names(ref mut expr) => expr),*
				}
			}
		}
	}
}

forall_expr_kinds!(impl_expr_kinds);

//=============================================================================
// Implementation of expression trait methods for all expression kinds.
//=============================================================================

macro_rules! impl_into_childs {
    ( $($names:ident),* ) => {
		fn into_childs(self) -> IntoChilds {
			use self::Expr::*;
			match self {
				$( $names(expr) => expr.into_childs() ),*
			}
		}
    }
}

impl ExprTrait for Expr {
	#[inline]
	fn childs(&self) -> Childs {
		self.as_trait().childs()
	}

	#[inline]
	fn childs_mut(&mut self) -> ChildsMut {
		self.as_trait_mut().childs_mut()
	}

	forall_expr_kinds!(impl_into_childs);

	#[inline]
	fn kind(&self) -> ExprKind {
		self.as_trait().kind()
	}

	#[inline]
	fn ty(&self) -> Type {
		self.as_trait().ty()
	}

	#[inline(always)]
	fn into_variant(self) -> Expr {
		self
	}
}
