//! Simplifies stevia expression trees via word-level transformations.

#![doc(html_root_url = "https://docs.rs/stevia_utils/0.1.0")]

// #![allow(missing_docs)]
#![allow(dead_code)]

extern crate stevia_ast as ast;

mod repr;
mod bit_encoder;
mod bitblaster;
