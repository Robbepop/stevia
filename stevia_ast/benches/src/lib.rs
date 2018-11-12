#![cfg(test)]
#![feature(test)]

extern crate test;
extern crate stevia_ast as stevia;

use test::{black_box, Bencher};

mod children {
	use super::*;
	use stevia::Children;

	#[bench]
	fn unary(bencher: &mut Bencher) {
		let not_expr = stevia::expr::Not::new(stevia::expr::BoolConst::t()).unwrap();
		bencher.iter(|| {
			black_box(
				for child in not_expr.children() {
					black_box(child);
				}
			)
		});
	}

	#[bench]
	fn binary(bencher: &mut Bencher) {
		let xor_expr = stevia::expr::Xor::new(
			stevia::expr::BoolConst::t(),
			stevia::expr::BoolConst::f()
		).unwrap();
		bencher.iter(|| {
			black_box(
				for child in black_box(xor_expr.children()) {
					black_box(child);
				}
			)
		});
	}

	#[bench]
	fn ternary(bencher: &mut Bencher) {
		let ite_expr = stevia::expr::IfThenElse::new(
			stevia::expr::BoolConst::t(),
			stevia::expr::BoolConst::f(),
			stevia::expr::BoolConst::t()
		).unwrap();
		bencher.iter(|| {
			black_box(
				for child in black_box(ite_expr.children()) {
					black_box(child);
				}
			)
		});
	}

	#[bench]
	fn nary(bencher: &mut Bencher) {
		let and_expr = stevia::expr::And::nary(vec![
			stevia::expr::BoolConst::t(),
			stevia::expr::BoolConst::f(),
			stevia::expr::BoolConst::t(),
			stevia::expr::BoolConst::f()
		]).unwrap();
		bencher.iter(|| {
			black_box(
				for child in black_box(and_expr.children()) {
					black_box(child);
				}
			)
		});
	}
}

mod into_children {
	use super::*;
	use stevia::IntoChildren;

	#[bench]
	fn unary(bencher: &mut Bencher) {
		let not_expr = stevia::expr::Not::new(stevia::expr::BoolConst::t()).unwrap();
		bencher.iter(|| {
			black_box(
				for child in not_expr.clone().into_children() {
					black_box(child);
				}
			)
		});
	}

	#[bench]
	fn binary(bencher: &mut Bencher) {
		let xor_expr = stevia::expr::Xor::new(
			stevia::expr::BoolConst::t(),
			stevia::expr::BoolConst::f()
		).unwrap();
		bencher.iter(|| {
			black_box(
				for child in black_box(xor_expr.clone().into_children()) {
					black_box(child);
				}
			)
		});
	}

	#[bench]
	fn ternary(bencher: &mut Bencher) {
		let ite_expr = stevia::expr::IfThenElse::new(
			stevia::expr::BoolConst::t(),
			stevia::expr::BoolConst::f(),
			stevia::expr::BoolConst::t()
		).unwrap();
		bencher.iter(|| {
			black_box(
				for child in black_box(ite_expr.clone().into_children()) {
					black_box(child);
				}
			)
		});
	}

	#[bench]
	fn nary(bencher: &mut Bencher) {
		let and_expr = stevia::expr::And::nary(vec![
			stevia::expr::BoolConst::t(),
			stevia::expr::BoolConst::f(),
			stevia::expr::BoolConst::t(),
			stevia::expr::BoolConst::f()
		]).unwrap();
		bencher.iter(|| {
			black_box(
				for child in black_box(and_expr.clone().into_children()) {
					black_box(child);
				}
			)
		});
	}
}

mod clone {
	use super::*;

	#[bench]
	fn unary(bencher: &mut Bencher) {
		let not_expr = stevia::expr::Not::new(stevia::expr::BoolConst::t()).unwrap();
		bencher.iter(|| black_box(not_expr.clone()))
	}

	#[bench]
	fn binary(bencher: &mut Bencher) {
		let xor_expr = stevia::expr::Xor::new(
			stevia::expr::BoolConst::t(),
			stevia::expr::BoolConst::f()
		).unwrap();
		bencher.iter(|| black_box(xor_expr.clone()))
	}

	#[bench]
	fn ternary(bencher: &mut Bencher) {
		let ite_expr = stevia::expr::IfThenElse::new(
			stevia::expr::BoolConst::t(),
			stevia::expr::BoolConst::f(),
			stevia::expr::BoolConst::t()
		).unwrap();
		bencher.iter(|| black_box(ite_expr.clone()))
	}

	#[bench]
	fn nary(bencher: &mut Bencher) {
		let and_expr = stevia::expr::And::nary(vec![
			stevia::expr::BoolConst::t(),
			stevia::expr::BoolConst::f(),
			stevia::expr::BoolConst::t(),
			stevia::expr::BoolConst::f()
		]).unwrap();
		bencher.iter(|| black_box(and_expr.clone()))
	}
}
