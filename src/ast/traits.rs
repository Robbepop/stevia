
use ast::iterators::{Childs, ChildsMut, IntoChilds};
use ast::variants::{ExprVariant, ExprKind};
use ast::Type;

pub trait ExprTrait {
	/// Returns the kind of this expression.
	/// 
	/// This may prove useful in the context of non-variant expression comparisons.
	fn kind(&self) -> ExprKind;
	/// Returns the cached type of this expression.
	/// 
	/// Types are cached mainly for performance reasons to check for type safety.
	fn ty(&self) -> Type;
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
	/// Maybe remove this trait method again in favor of `impl From<impl ExprTrait> for ExprVariant`.
	fn into_variant(self) -> ExprVariant;
}
