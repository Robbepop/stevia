//! This library provides an implementation for bitvectors in the context of SMT solving.
//!
//! Bitvectors in the context of SMT solving are fixed-sized signed or unsigned integer representatives.
//! They are needed to express and propagate constant values within an SMT procedure and are required
//! to be very fast and have low memory overhead since their quantity on a common run might be very high.
//!
//! Bitvectors in the context of SMT solving must not be confused with bitvectors that act as storage
//! for bits as in C++'s `<bitset>`. Although they also allow to operate on them via the typical bitset-based
//! methods as `intersect`, `union` and `difference`.
//!
//! This data structure was designed to be especially fast for smaller instances.
//! As of now small instances are instances that represent numbers that fit into 64 bits of memory.
//!
//! Since bitvector instances might store a variadic and potentially large amount of data they might
//! require heap allocation and thus are no `Copy` types.
//! This also eliminates the possibilities to overload operators on them in the current Rust design.
//!
//! Instances of bitvectors cannot grow or shrink as normal vectors and are fixed upon construction.
//! This allows further optimizations and even less memory overhead since no capacity field is required.
//! 
//! There are some methods that do not result in a new bitvector instance but that mutate the given
//! instance and most often are suffixed with `_assign`.
//!

#![feature(untagged_unions)]
#![feature(unique)]

#![allow(dead_code)]
#![allow(unused_variables)]

extern crate num;

mod errors;
mod items;
mod iterators;
mod impls;

pub use items::FixInt;
pub use errors::{
	Error,
	ErrorKind
};
