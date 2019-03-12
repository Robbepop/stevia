//! Simplifies stevia expression trees via word-level transformations.

#![doc(html_root_url = "https://docs.rs/stevia_simplifier/0.1.0")]

#![feature(box_patterns)]

// #![allow(missing_docs)]
// #![allow(dead_code)]

extern crate apint;
extern crate itertools;
extern crate either;

#[macro_use]
extern crate log;

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
