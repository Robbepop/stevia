#![feature(box_patterns)]
#![feature(conservative_impl_trait)]
#![feature(nll)]

extern crate apint;
extern crate num;
extern crate smallvec;
extern crate unreachable;
extern crate itertools;
extern crate string_interner;
extern crate vec_map;

#[macro_use]
extern crate lazy_static;

pub mod ast;
mod simplifier;

pub use simplifier::prelude::{
    TransformEffect,
    Simplifier
};
