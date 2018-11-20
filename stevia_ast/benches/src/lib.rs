#![cfg(test)]
#![feature(test)]

extern crate test;
extern crate stevia_ast as stevia;

use test::{black_box, Bencher};

mod children {
	use super::*;
	use stevia::Children;

	#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
	enum ExprClass {
		Unary,
		Binary,
		Ternary,
		Nary
	}

	fn create_expr(nodes: usize, max_class: ExprClass) -> stevia::AnyExpr {
		if max_class == ExprClass::Nary && nodes >= 2 {
			let mut children = Vec::new();
			let mut remaining = nodes;
			while remaining != 0 {
				let cur_nodes = std::cmp::max(remaining / 2, 1);
				remaining -= cur_nodes;
				children.push(create_expr(cur_nodes, max_class))
			}
			return stevia::expr::And::nary(children).unwrap().into()
		}
		if max_class == ExprClass::Ternary && nodes >= 4 {
			let nodes_cond = (nodes - 1) / 3;
			let nodes_else = (nodes - 1) / 3;
			let nodes_then = (nodes - 1) - nodes_cond - nodes_else;
			return stevia::expr::IfThenElse::new(
				create_expr(nodes_cond, max_class),
				create_expr(nodes_then, max_class),
				create_expr(nodes_then, max_class)
			).unwrap().into()
		}
		if max_class == ExprClass::Binary && nodes >= 3 {
			let nodes_rhs = (nodes - 1) / 2;
			let nodes_lhs = (nodes - 1) - nodes_rhs;
			return stevia::expr::Xor::new(
				create_expr(nodes_lhs, max_class),
				create_expr(nodes_rhs, max_class)
			).unwrap().into()
		}
		if max_class == ExprClass::Unary && nodes >= 2 {
			return stevia::expr::Not::new(
				create_expr(nodes - 1, max_class)
			).unwrap().into()
		}
		stevia::expr::BoolConst::t().into()
	}

	#[bench]
	fn unary(bencher: &mut Bencher) {
		let not_expr = stevia::expr::Not::new(stevia::expr::BoolConst::t()).unwrap();
		bencher.iter(|| {
			black_box(
				for child in black_box(not_expr.children()) {
					black_box(child);
				}
			)
		});
	}

	#[bench]
	fn rec_unary_big(bencher: &mut Bencher) {
		let ite_expr = create_expr(100, ExprClass::Unary);
		bencher.iter(|| {
			black_box(
				for child in black_box(stevia::children_recursive_with_event(&ite_expr)) {
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
	fn rec_binary_big(bencher: &mut Bencher) {
		let ite_expr = create_expr(100, ExprClass::Binary);
		bencher.iter(|| {
			black_box(
				for child in black_box(stevia::children_recursive_with_event(&ite_expr)) {
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
	fn rec_ternary_big(bencher: &mut Bencher) {
		let ite_expr = create_expr(100, ExprClass::Ternary);
		bencher.iter(|| {
			black_box(
				for child in black_box(stevia::children_recursive_with_event(&ite_expr)) {
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

	#[bench]
	fn rec_nary_big(bencher: &mut Bencher) {
		let ite_expr = create_expr(100, ExprClass::Nary);
		bencher.iter(|| {
			black_box(
				for child in black_box(stevia::children_recursive_with_event(&ite_expr)) {
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
				for child in black_box(not_expr.clone().into_children()) {
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
