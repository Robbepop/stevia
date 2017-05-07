use ast_walker::Visitor;
use ast::ExprNode;

pub struct PrintingVisitor<'buf> {
	indent: String,
	buf   : &'buf mut ::std::io::Write
}

impl<'buf> PrintingVisitor<'buf> {
	pub fn new(write: &'buf mut ::std::io::Write) -> PrintingVisitor {
		PrintingVisitor{
			indent: String::new(),
			buf   : write
		}
	}
}

impl<'buf> PrintingVisitor<'buf> {
	fn open_block(&mut self, content: &str) {
		writeln!(self.buf, "{}({}", &self.indent, content).unwrap();
		self.indent.push('\t');
	}

	fn close_block(&mut self) {
		self.indent.pop();
		writeln!(self.buf, "{})", self.indent).unwrap();
	}
}

impl<'ast, 'buf> Visitor<'ast> for PrintingVisitor<'buf> {
	fn pre_visit_expr(&mut self, expr: &'ast ExprNode) {
		use ast::ExprKind::*;
		match expr.kind {

			Undefined  => {
				writeln!(self.buf, "{}(undefined)", self.indent).unwrap();
			},
			Symbol{name, ty} => {
				writeln!(self.buf, "{}(symbol :{:?} {:?})", self.indent, ty, name).unwrap();
			},

			Term(ref term) => {
				use ast::Term::*;
				match *term {
					BitVecConst(bitvec) => {
						writeln!(self.buf, "{}(bitvec-const {:?})", self.indent, bitvec.into_u64()).unwrap();
					},
					Arithmetic(ref calc) => {
						use ast::Arithmetic::*;
						match *calc {
							Neg(_) => {
								self.open_block("neg");
							},
							Add{..} => {
								self.open_block("add");
							},
							Mul{..} => {
								self.open_block("mul");
							},
							Sub{..} => {
								self.open_block("sub");
							},
							Div{..} => {
								self.open_block("div");
							},
							Mod{..} => {
								self.open_block("mod");
							},
							SignedDiv{..} => {
								self.open_block("sdiv");
							},
							SignedMod{..} => {
								self.open_block("smod");
							},
							SignedRem{..} => {
								self.open_block("srem");
							}
						}
					},

					Bitwise(..) => {
						self.open_block("bitwise-op<?>");
					},
					Shift(..) => {
						self.open_block("shift<?>");
					},
					Ordering(..) => {
						self.open_block("relation<?>");
					},
					Concat{..} => {
						self.open_block("concat");
					},
					Extract{..} => {
						self.open_block("extract");
					},
					Extend{..} => {
						self.open_block("extend");
					},
					SignedExtend{..} => {
						self.open_block("signed-extend");
					},
					Read{..} => {
						self.open_block("array-read");
					},
					Write{..} => {
						self.open_block("array-write");
					}
				}
			},

			Formula(ref formula) => {
				use ast::Formula::*;
				match *formula {
					BoolConst(value) => {
						writeln!(self.buf, "{}(boolean-const {:?})", self.indent, value).unwrap();
					},
					Not(..) => {
						self.open_block("not");
					},
					And{..} => {
						self.open_block("and");
					},
					Or{..} => {
						self.open_block("or");
					},
					Binary(..) => {
						self.open_block("binary-formula<?>");
					},
					ParamBool{..} => {
						self.open_block("parametric-bool");
					}
				}
			},

			Equals{..} => {
				self.open_block("equals");
			},

			IfThenElse{..} => {
				self.open_block("if-then-else");
			},

			Array{ref name, ref index_type, ref value_type} => {
				writeln!(self.buf, "{}(array :{:?} :{:?} {:?})", self.indent, index_type, value_type, name).unwrap();
			},
			Bitvec{name, bit_width} => {
				writeln!(self.buf, "{}(bitvec :{:?} {:?})", self.indent, bit_width, name).unwrap();
			},
			Boolean{name} => {
				writeln!(self.buf, "{}(boolean {:?})", self.indent, name).unwrap();
			}
		}
	}

	fn post_visit_expr(&mut self, expr: &'ast ExprNode) {
		use ast::ExprKind::*;
		match expr.kind {

			Term(ref term) => {
				use ast::Term::*;
				match *term {
					BitVecConst(_) => {},
					_ => {
						self.close_block();
					}
				}
			},

			Formula(ref formula) => {
				use ast::Formula::*;
				match *formula {
					BoolConst(_) => {},
					_ => {
						self.close_block();
					}
				}
			},

			Equals{..} => {
				self.close_block();
			},

			IfThenElse{..} => {
				self.close_block();
			},

			_ => {}
		}
	}
}
