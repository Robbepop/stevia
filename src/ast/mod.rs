
mod ty;
mod errors;
pub mod expr;
mod variants;
mod traits;
mod iterators;
mod factory;

#[allow(unused_variables)]
mod naive_factory;
mod visitor;
mod pretty_printer;
pub mod prelude;

pub use self::ty::{Type, TypeKind};
pub use self::variants::{Expr, ExprKind};
pub use self::traits::ExprTrait;
pub use self::iterators::{Childs, ChildsMut, IntoChilds};
pub use self::errors::{Result, AstError, ErrorKind};
pub use self::factory::ExprFactory;
pub use self::naive_factory::NaiveExprFactory;

pub use self::pretty_printer::pretty_print_expr;

impl From<Expr> for Result<Expr> {
	fn from(expr: Expr) -> Result<Expr> {
		Ok(expr)
	}
}

/// An abstraction over an indirection to an entitiy `T`.
pub type P<T> = Box<T>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SymName(usize);

// #[cfg(test)]
// mod tests {
	// use super::*;

	// #[test]
	// fn simple_macro() {
		// use ast::factory::ExprFactory;
		// let fab = NaiveExprFactory::new();

		// let expr1 = fab.eq(
		// 	fab.bvmul(
		// 		fab.bitvec("x", 32),
		// 		fab.bvconst(2)
		// 	),
		// 	fab.bvadd(
		// 		fab.bitvec("x", 32),
		// 		fab.bitvec("x", 32)
		// 	)
		// ).unwrap();

		// pretty_print_expr(&mut ::std::io::stdout(), &expr1);

		// let expr2 = expr_tree!(fab, expr!{
		// 	(=
		// 		(bvmul
		// 			(bitvec "x")
		// 		    (bvconst 2)
		// 	    )
		// 		(bvadd
		// 			(bitvec "x")
		// 			(bitvec "x")
		// 		)
		// 	)
		// });

		// assert_eq!(expr1, expr2);
	// }
// }
