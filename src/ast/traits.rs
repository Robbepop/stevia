use ast::Type;
use ast::iterators::{Childs, ChildsMut, IntoChilds};
use ast::variants::{Expr, ExprKind};

/// TODO: Maybe rename to `IExpr` or `GenericExpr`
pub trait ExprTrait {
	/// Returns the kind of this expression.
	/// 
	/// This may prove useful in the context of non-variant expression comparisons.
	fn kind(&self) -> ExprKind;
	/// Returns the cached type of this expression.
	/// 
	/// Types are cached mainly for performance reasons to check for type safety.
	fn ty(&self) -> Type;
	/// Returns the arity of this expression.
	/// 
	/// The arity is the number of child expressions of this expression.
	fn arity(&self) -> usize;
	/// Returns an iterator over read-only child expressions (if any) of this expression.
	fn childs(&self) -> Childs;
	/// Returns an iterator over mutable child expressions (if any) of this expression.
	fn childs_mut(&mut self) -> ChildsMut;
	/// Consumes this expression and returns an owning iterator over the child expressions
	/// (if any) of the consumed expression.
	fn into_childs(self) -> IntoChilds;
	/// Consumes this expression and returns its identity as variant type.
	/// 
	/// This is useful for conversions between non-variant and variant expression objects
	/// and mainly prevents boilerplate code.
	/// 
	/// Maybe remove this trait method again in favor of `impl From<impl ExprTrait> for Expr`.
	fn into_variant(self) -> Expr;
}

pub trait GenericExpr: Kinded + Typed + ChildsIter + IntoExpr {
	/// Returns the arity of this expression.
	/// 
	/// The arity is the number of child expressions of this expression.
	fn arity(&self) -> usize;
}

pub trait ChildsIter {
	/// Returns an iterator over read-only child expressions (if any) of this expression.
	fn childs(&self) -> Childs;
	/// Returns an iterator over mutable child expressions (if any) of this expression.
	fn childs_mut(&mut self) -> ChildsMut;
	/// Consumes this expression and returns an owning iterator over the child expressions
	/// (if any) of the consumed expression.
	fn into_childs(self) -> IntoChilds;
}

pub trait Kinded {
	/// Returns the kind of this expression.
	/// 
	/// This may prove useful in the context of non-variant expression comparisons.
	fn kind(&self) -> ExprKind;
}

impl<T> Kinded for T where T: ExprTrait {
	#[inline]
	fn kind(&self) -> ExprKind {
		<Self as ExprTrait>::kind(self)
	}
}

pub trait Typed {
	/// Returns the cached type of this expression.
	/// 
	/// Types are cached mainly for performance reasons to check for type safety.
	fn ty(&self) -> Type;
}

impl<T> Typed for T where T: ExprTrait {
	#[inline]
	fn ty(&self) -> Type {
		<Self as ExprTrait>::ty(self)
	}
}

pub trait IntoExpr {
	/// Consumes this entity and returns its identity as variant `Expr` type.
	/// 
	/// This is useful for conversions between non-variant and variant expression objects
	/// and mainly prevents boilerplate code.
	/// 
	/// Note: Maybe remove this trait method again in favor of `impl From<impl ExprTrait> for Expr`.
	fn into_expr(self) -> Expr;
}

impl<T> IntoExpr for T where T: ExprTrait {
	#[inline]
	fn into_expr(self) -> Expr {
		<Self as ExprTrait>::into_variant(self)
	}
}
