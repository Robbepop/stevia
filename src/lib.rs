#![feature(box_patterns)]
#![feature(conservative_impl_trait)]

extern crate apint;
extern crate num;
extern crate smallvec;
extern crate unreachable;
extern crate itertools;
extern crate string_interner;

#[macro_use]
extern crate lazy_static;

#[macro_use]
extern crate smt_expr_derive;

/// The old and deprecated AST (Abstract Syntax Tree) module.
pub mod ast;

/// The new and shiny experimental future AST (Abstract Syntax Tree) module.
pub mod ast2;
pub mod simplifier;
