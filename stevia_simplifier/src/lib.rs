//! Simplifies stevia expression trees via word-level transformations.

#![feature(crate_in_paths)]
#![feature(box_patterns)]
#![feature(nll)]

// #![allow(missing_docs)]
// #![allow(dead_code)]

#[macro_use]
extern crate stevia_ast as ast;

extern crate apint;
extern crate num;
extern crate smallvec;
extern crate unreachable;
extern crate itertools;
extern crate string_interner;
extern crate vec_map;
extern crate either;

#[macro_use]
extern crate log;

#[macro_use]
extern crate indoc;

#[macro_use]
mod base;
mod simplifications;

pub mod prelude {
    pub use super::{
        Simplifier,
        BaseSimplifier,
        simplify
    };
}

pub use self::base::prelude::*;
