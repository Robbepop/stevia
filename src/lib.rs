#![feature(box_patterns)]

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

mod bitvec;
pub mod ast;
pub mod ast2;

pub use bitvec::BitVec;
