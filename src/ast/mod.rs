
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
#[macro_use]
mod transformer;
mod simplifier;

pub use self::ty::{Bits, Type, TypeKind};
pub use self::variants::{Expr, ExprKind};
pub use self::traits::ExprTrait;
pub use self::iterators::{Childs, ChildsMut, IntoChilds};
pub use self::errors::{Result, AstError, ErrorKind};
pub use self::factory::ExprFactory;
pub use self::naive_factory::NaiveExprFactory;

use self::transformer::{Transformer, TransformerImpl};

pub use self::pretty_printer::pretty_print_expr;

impl From<Expr> for Result<Expr> {
	fn from(expr: Expr) -> Result<Expr> {
		Ok(expr)
	}
}

/// An abstraction over an indirection to an entitiy `T`.
pub type P<T> = Box<T>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct SymName(usize);

// smt_cmd! {
// 	(set-logic QF_LIA)
// 	(declare-fun x () Int) // declare some constants
// 	(declare-fun y () Int)
// 	(declare-fun z () Int)
// 	(push 1)
// 	(assert (= (+ x y) 10))
// 	(assert (= (+ x (* 2 y)) 20))
// 	(check-sat)
// 	// sat ; there is a solution
// 	(pop 1) ; clear the assertions
// 	(push 1) ; ready for another problem
// 	(assert (= (+ (* 3 x) y) 10))
// 	(assert (= (+ (* 2 x) (* 2 y)) 21))
// 	(check-sat)
// 	// unsat ; no solution
// 	(declare-fun p () Bool)
// 	(pop 1)
// 	(assert p)
// 	// ( error "p is not declared") ; the declaration of p was popped
// }

// expr_tree!{
// 	(= (+ (* 3 x) y) 10))
// }

// expr_tree!{
// 	(= (+ (* 2 x) (* 2 y)) 21))
// }

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn simple_macro() {
		use ast::factory::ExprFactory;
		let fab = NaiveExprFactory::new();

		let expr1 = fab.eq(
			fab.bvmul(
				fab.bitvec("x", Bits(32)),
				fab.bvconst(Bits(32), 2)
			),
			fab.bvadd(
				fab.bitvec("x", Bits(32)),
				fab.bitvec("x", Bits(32))
			)
		).unwrap();

		pretty_print_expr(&mut ::std::io::stdout(), &expr1);

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
	}
}
