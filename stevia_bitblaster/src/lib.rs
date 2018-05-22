//! Simplifies stevia expression trees via word-level transformations.

#![doc(html_root_url = "https://docs.rs/stevia_utils/0.1.0")]

#![feature(fn_traits)]
#![feature(unboxed_closures)]

// #![allow(missing_docs)]
#![allow(dead_code)]

extern crate stevia_ast as ast;

mod bitblaster;
mod gate_encoder;
mod repr;
