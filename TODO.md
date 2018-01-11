# TODO-List for Stevia

## AST

- Remove generic `Equals` expression.
- Add `BitvecEquals` expression.
- Add `ArrayEquals` expression.
- Add `expr` public submodule to `ast` module and export all concrete expressions in it.
- Rename `Expr` to `AnyExpr`.
- Improve doc-comments of some expressions. E.g. remove the ` ticks.
- (Maybe) add `*_infer` constructors to bitvec expressions to infer their bit width.
- Reduce code bloat by introducing further code-gen macros.

## Critical

- Restructure expression nodes from using `{left: Box<Expr>, right: Box<Expr>}` to using `{childs: Box<[Expr;2]>}`
	- Better cache locality
	- Smaller object size
	- Less `malloc` calls
	- More efficient iteration over children
	- Less frickeling with `Box` vs no `Box` upon creation
	- Can be done for expressions like If-Then-Else, too.
	- Requires additional specialized getters (`mut` and non-`mut`) for similarly well usability.
		- `fn left_right(&self) -> (&Expr, &Expr) { ... }`
		- `fn left_right_mut(&mut self) -> (&mut Expr, &mut Expr) { ... }`
		- `fn cond_then_else(&self) -> (&Expr, &Expr, &Expr) { ... }` and same for `mut` version
- Refactor ty.rs implementation somehow. (Just make it better ... somehow.)

- Implement default traversal routine for AST transformers.
	- It turned out that default traversal is useful for architectures with many different transformers such as 
		- Normalization
		- Lowering
		- ConstEvaluator
		- SymbolicSimplifier
		- IfConstraintPropagator
		- etc...
- Implement simplifier based on generic, recursive AST transformer.
	- [ ] Symbolic Simplifier
	- [ ] Const Evaluator
	- [ ] If-Constraint Propagator
	- [ ] Linear Bitvector Solver

## Short term

- Implement `Context` (or `Scope`) for handling symbols and their associated metadata. Used by factories.

## Long term

- Write documentation for all stable parts of the code.
- Find and depend on decent Bitvector library implementation.
- Find and depend on decent library implementation similar to STP's `libabc` for and-inverter-graph (AIG) computation..
- Add SMTLib2.X serialization (printer) and deserialization (parser) support.
- Implement `simple_type_check` method to naively check the children's type of a newly created expression for validity. This can be used by factory implementations that want to check for this addional safety guard. (Maybe this is not needed if we always create new child expressions with a type-checking factory!)

## Considerations

- Refactor binary nodes with two `P<Expr>` fields into a single `Box<[Expr;2]>` field. This allows for easier sorting and iterating. Think about more beautiful access to inner childs like `a.left` instead of `a.childs[0]`. This change may also lead to less `Box` allocations during simplification steps and would lead to better memory compaction and thus to better cache efficiency.
- Think about trade-offs by adding `Nand`, `Nor` and `Xnor` as new formula types.
- Think about trade-offs by replacing generic `Equals` with bool- and bitvector specific alternatives:
	- Bitvec: `BitvecEq` and `BitvecNe` or `BitEq` and `BitNe` or `BvEq` and `BvNe`
	- Boolean: `Iff` and `Xor`
- Do not add an attribute to `SmtExpr` proc macro to set the expression type explicitely since apparently `BitVecConst` doesn't really need it.

## Open Questions

- Is it better to unify every possible AST simplification into one giantic simplification routine or is it better to factor all the semantically different optimization techniques (such as const-propagation, reduction or normaliztion, quantifier-elimination, etc.)

## Science

- Find a decent design for an `expr_tree!` macro that simplifies creation of expression trees via factories and a syntax similar to SMTLIB2.0.
- Try to find a decent design to model `bvsum`, `bvprod`, `conjunction` and `disjunction` in `ExprFactory`.
	- Is it okay to just leave them out and depend on the simplifier to inline them automatically?
- Find out what scopes `push` & `pop` in STP are and how to incorporate them into this SMT solver.
	- STP has a stack of vectors that acts as assertion scope level. Users may wish to add or remove such scopes to add or remove entire
	   groups of assertions that have been added to the removed scope level. The STP scope design is inefficient and should not be taken over to Stevia. Stevia should model this concept with a single vector for the assertions and another vector for entry points to new scope levels.
