#![feature(box_patterns)]
#![feature(conservative_impl_trait)]
#![feature(nll)]
#![feature(copy_closures)]
#![feature(clone_closures)]
#![feature(match_default_bindings)]

#![allow(missing_docs)]
#![allow(dead_code)]

extern crate apint;
extern crate num;
extern crate smallvec;
extern crate unreachable;
extern crate itertools;
extern crate string_interner;
extern crate vec_map;
extern crate either;
extern crate chashmap;

#[macro_use]
extern crate lazy_static;

#[macro_use]
extern crate log;

#[macro_use]
pub mod ast;

mod simplifier;

pub use ast::prelude::{
    TransformEffect
};
pub use simplifier::prelude::{
    Simplifier
};
