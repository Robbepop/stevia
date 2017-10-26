#![feature(box_patterns)]

extern crate num;
extern crate smallvec;
extern crate unreachable;
extern crate itertools;
extern crate string_interner;

#[macro_use]
extern crate smt_expr_derive;

extern crate apint;

mod bitvec;
pub mod ast;

pub use bitvec::BitVec;
