#![feature(box_patterns)]

extern crate num;
extern crate smallvec;
extern crate unreachable;
extern crate itertools;
extern crate string_interner;

#[macro_use]
extern crate smt_expr_derive;

mod bitvec;
pub mod ast;

pub use bitvec::BitVec;


#[cfg(test)]
mod tests {
	// use super::*;

	// #[test]
	// fn test_01() {
	// 	let s0: u64 = 200;
	// 	let s1: u64 =  60;
	// 	let r0: u64 = (s0 as u8).wrapping_add(s1 as u8) as u64; // 200 + 60 % 256 = 4
	// 	assert_eq!(r0, 4);
	// }

	// #[test]
	// fn test_02() {
	// 	let s0: i32 = -200;
	// 	let s1: u32 =  300;
	// 	let r0: u32 = (s0 as u32).wrapping_add(s1 as u32) as u32;
	// 	let r1: i32 = (s0 as i32).wrapping_add(s1 as i32) as i32;
	// 	assert_eq!(r0, 100);
	// 	assert_eq!(r1, 100);
	// 	assert_eq!(s0 as u32, 4294967096);
	// }

	#[test]
	fn test_03s() {
		let s0: i64 = 0xFFFF_FFFF_FFFF;
		let s1: i16 = s0 as i16;
		let s2: i64 = s1 as i64;
		assert_eq!(s1, 0xFFFF_u16 as i16);
		assert_eq!(s2, 0x0000_0000_0000_FFFF);
	}

	#[test]
	fn test_03u() {
		let s0: u64 = 0xFFFF_FFFF_FFFF;
		let s1: u16 = s0 as u16;
		let s2: u64 = s1 as u64;
		assert_eq!(s1, 0xFFFF_u16 as u16);
		assert_eq!(s2, 0x0000_0000_0000_FFFF);
	}
}
