#![recursion_limit="96"]

extern crate proc_macro;
extern crate syn;
#[macro_use]
extern crate quote;

use proc_macro::TokenStream;

#[proc_macro_derive(SmtExpr, attributes(stevia))]
pub fn smt_expr(input: TokenStream) -> TokenStream {
	// Construct a string representation of the type definition
	let s = input.to_string();

	// Parse the string representation
	let ast = syn::parse_macro_input(&s).unwrap();

	// Build the impl
	let gen = impl_smt_expr(&ast);

	// Return the generated impl
	gen.parse().unwrap()
}

struct ChildsIterTokens {
	arity      : quote::Tokens,
	childs     : quote::Tokens,
	childs_mut : quote::Tokens,
	into_childs: quote::Tokens
}

fn unpack_field_ident(field: &syn::Field) -> &syn::Ident {
	field.ident
		.as_ref()
		.expect("#[derive(SmtExpr)] error: Expected a named field for the inner \
		         child expression while unpacking an unary expression!")
}

impl ChildsIterTokens {
	fn leaf() -> ChildsIterTokens {
		ChildsIterTokens{
			arity      : quote!{ 0 },
			childs     : quote!{ Childs::none() },
			childs_mut : quote!{ ChildsMut::none() },
			into_childs: quote!{ IntoChilds::none() }
		}
	}

	fn unary(inner: &syn::Field) -> ChildsIterTokens {
		let inner_name = unpack_field_ident(inner);
		ChildsIterTokens{
			arity      : quote!{ 1 },
			childs     : quote!{ Childs::unary(&self.#inner_name) },
			childs_mut : quote!{ ChildsMut::unary(&mut self.#inner_name) },
			into_childs: quote!{ IntoChilds::unary(*self.#inner_name) }
		}
	}

	fn binary(left: &syn::Field, right: &syn::Field) -> ChildsIterTokens {
		let left_name = unpack_field_ident(left);
		let right_name = unpack_field_ident(right);
		ChildsIterTokens{
			arity      : quote!{ 2 },
			childs     : quote!{ Childs::binary(&self.#left_name, &self.#right_name) },
			childs_mut : quote!{ ChildsMut::binary(&mut self.#left_name, &mut self.#right_name) },
			into_childs: quote!{ IntoChilds::binary(*self.#left_name, *self.#right_name) }
		}
	}

	fn ternary(fst: &syn::Field, snd: &syn::Field, trd: &syn::Field) -> ChildsIterTokens {
		let fst_name = unpack_field_ident(fst);
		let snd_name = unpack_field_ident(snd);
		let trd_name = unpack_field_ident(trd);
		ChildsIterTokens{
			arity      : quote!{ 3 },
			childs     : quote!{ Childs::ternary(&self.#fst_name, &self.#snd_name, &self.#trd_name) },
			childs_mut : quote!{ ChildsMut::ternary(&mut self.#fst_name, &mut self.#snd_name, &mut self.#trd_name) },
			into_childs: quote!{ IntoChilds::ternary(*self.#fst_name, *self.#snd_name, *self.#trd_name) }
		}
	}

	fn nary(compound: &syn::Field) -> ChildsIterTokens {
		let compound_name = unpack_field_ident(compound);
		ChildsIterTokens{
			arity      : quote!{ self.#compound_name.len() },
			childs     : quote!{ Childs::nary(self.#compound_name.as_slice()) },
			childs_mut : quote!{ ChildsMut::nary(self.#compound_name.as_mut_slice()) },
			into_childs: quote!{ IntoChilds::nary(self.#compound_name) }
		}
	}
}

fn collect_fields_by<'ast, P>(fields: &'ast[syn::Field], pred: P) -> Vec<&'ast syn::Field>
	where P: Fn(&syn::Field)->bool
{
	fields
		.iter()
		.filter(|ref field| pred(field))
		.collect::<Vec<_>>()
}

fn collect_fields_with_typename<'ast>(fields: &'ast[syn::Field], typename: &str) -> Vec<&'ast syn::Field> {
	collect_fields_by(fields, |ref field| field.ty == syn::parse_type(typename).unwrap())
}

fn collect_single_childs(fields: &[syn::Field]) -> Vec<&syn::Field> {
	collect_fields_with_typename(fields, "P<Expr>")
}

fn collect_compound_childs(fields: &[syn::Field]) -> Vec<&syn::Field> {
	collect_fields_with_typename(fields, "Vec<Expr>")
}

fn extract_iterator_components(fields: &[syn::Field]) -> ChildsIterTokens {
	let singles   = collect_single_childs(fields);
	let compounds = collect_compound_childs(fields);
	match (singles.len(), compounds.len()) {
		(0, 0) => ChildsIterTokens::leaf(),
		(1, 0) => ChildsIterTokens::unary(singles[0]),
		(2, 0) => ChildsIterTokens::binary(singles[0], singles[1]),
		(3, 0) => ChildsIterTokens::ternary(singles[0], singles[1], singles[2]),
		(0, 1) => ChildsIterTokens::nary(compounds[0]),
		(s, 0) => panic!("#[derive(SmtExpr)] error: Found {} single child expressions in this SMT expression. \
		                  The currently maximum supported number of child expressions is 3!", s),
		(0, c) => panic!("#[derive(SmtExpr)] error: Found {} compound child expressions in this SMT expression. \
		                  Only single-compound SMT expressions are supported! This may change in future versions.", c),
		(s, c) => panic!("#[derive(SmtExpr)] error: Found a mixture of compound ({}) and single child ({}) expressions. \
		                  This is not supported, yet!", c, s)
	}
}

struct TyGetterTokens(quote::Tokens);

fn extract_type_getter_components(fields: &[syn::Field]) -> TyGetterTokens {
	let ty_fields = collect_fields_by(fields, |ref field| {
		(unpack_field_ident(field) == &syn::parse_ident("ty").unwrap()) &&
		(field.ty == syn::parse_type("Type").unwrap())
	});
	if ty_fields.is_empty() {
		TyGetterTokens(quote!{ Type::Boolean })
	}
	else {
		TyGetterTokens(quote!{ self.ty })
	}
}

fn gen_final_code(name: &syn::Ident, fields: &[syn::Field]) -> quote::Tokens {
	let ChildsIterTokens{arity, childs, childs_mut, into_childs} = extract_iterator_components(fields);
	let TyGetterTokens(ty_body) = extract_type_getter_components(fields);
	quote! {
		impl ExprTrait for #name {

			/// Returns the kind of this expression.
			#[inline]
			fn kind(&self) -> ExprKind { ExprKind::#name }

			/// Returns the type of this expression.
			#[inline]
			fn ty(&self) -> Type { #ty_body }

			/// Returns the arity of this expression.
			/// 
			/// Note: The arity is the number of child expressions.
			#[inline]
			fn arity(&self) -> usize {
				#arity
			}

			/// Returns an iterator over the child expressions.
			#[inline]
			fn childs<'e>(&'e self) -> Childs<'e> {
				#childs
			}

			/// Returns a mutable iterator over the child expressions.
			#[inline]
			fn childs_mut<'e>(&'e mut self) -> ChildsMut<'e> {
				#childs_mut
			}

			/// Consumes this expression to return a move iterator over the child expressions.
			#[inline]
			fn into_childs(self) -> IntoChilds {
				#into_childs
			}

			/// Wraps this expression into its variant type.
			#[inline]
			fn into_variant(self) -> Expr { Expr::#name(self) }

		}
	}
}

fn impl_smt_expr(ast: &syn::MacroInput) -> quote::Tokens {
	let name = &ast.ident;
	if let syn::Body::Struct(ref struct_kind) = ast.body {
		match *struct_kind {
			syn::VariantData::Unit => {
				panic!("#[derive(SmtExpr)] is not defined for unit structs!")
			},
			syn::VariantData::Tuple(_) => {
				panic!("#[derive(SmtExpr)] is not defined for tuple structs! Use named fields instead.")
			},
			syn::VariantData::Struct(ref fields) => {
				gen_final_code(name, fields)
			}
		}
	}
	else {
		panic!("#[derive(SmtExpr)] is only defined for structs, not for enums!");
	}
}
