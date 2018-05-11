//! Simplifies stevia expression trees via word-level transformations.

// #![allow(missing_docs)]
// #![allow(dead_code)]

extern crate stevia_ast as ast;

#[macro_use]
extern crate indoc;

mod writer;

pub use writer::write_smtlib2;
