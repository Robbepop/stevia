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

use string_interner::Symbol as InternerSymbol;

pub use self::ty::{Bits, Type, TypeKind, CommonBitwidth, CommonBitVec, CommonType};
pub use self::variants::{Expr, ExprKind};
pub use self::traits::{
	GenericExpr,
	ChildsIter,
	Kinded,
	Typed,
	IntoExpr
};
pub use self::iterators::{Childs, ChildsMut, IntoChilds};
pub use self::errors::{Result, AstError, ErrorKind};
pub use self::factory::ExprFactory;
pub use self::naive_factory::NaiveExprFactory;

use self::transformer::{Transformer, TransformerImpl};

pub use self::pretty_printer::pretty_print_expr;
pub use self::simplifier::simplify;

impl From<Expr> for Result<Expr> {
	fn from(expr: Expr) -> Result<Expr> {
		Ok(expr)
	}
}

/// An abstraction over an indirection to an entitiy `T`.
pub type P<T> = Box<T>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SymName(usize);

impl InternerSymbol for SymName {
	#[inline]
	fn to_usize(self) -> usize { self.0 }
	#[inline]
	fn from_usize(val: usize) -> SymName { SymName(val) }
}

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
	fn test_pretty_printer() {
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

		let mut buf = vec![];
		pretty_print_expr(&mut buf, &expr1);
		let printed  = String::from_utf8(buf).unwrap();
		let expected = "\
(=
	(bvmul
		( symbol SymName(0) )
		( bvconst :32 2 )
	)
	(bvadd
		( symbol SymName(0) )
		( symbol SymName(0) )
	)
)
";
		// println!("{:?}", printed);
		// println!("{:?}", expected);
		// pretty_print_expr(&mut ::std::io::stdout(), &expr1);
		assert_eq!(printed, expected);
	}
}
