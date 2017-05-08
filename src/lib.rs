#![recursion_limit = "256"]

extern crate smallvec;

#[macro_use]
extern crate smt_expr_derive;

mod bitvec;
pub mod ast;

pub use bitvec::BitVec;
