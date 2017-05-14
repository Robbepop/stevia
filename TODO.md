# TODO-List for Stevia

## Critical

- Implement generic recursive AST consumer that acts as a base for optimizations and other AST mutation operations.

## Short term

- Implement `Context` (or `Scope`) for handling symbols and their associated metadata. Used by factories.

## Long term

- Write documentation for all stable parts of the code.
- Implement expression simplifier based on generic recursive AST consumer.
- Find and depend on decent Bitvector library implementation.
- Find and depend on decent library implementation similar to STP's `libabc` for and-inverter-graph (AIG) computation..
- Add SMTLib2.X serialization (printer) and deserialization (parser) support.
- Implement `simple_type_check` method to naively check the children's type of a newly created expression for validity. This can be used by factory implementations that want to check for this addional safety guard. (Maybe this is not needed if we always create new child expressions with a type-checking factory!)

## Considerations

- Rename `ExprTrait` to `IExpr`.
- Do not add an attribute to `SmtExpr` proc macro to set the expression type explicitely since apparently `BitVecConst` doesn't really need it.
- Maybe remove `into_variant` from `ExprTrait` and put it into `IntoVariant` as new trait and make it possible to auto `impl From<T: IntoVariant> for ExprVariant { .. }`. Or maybe remove it if it is not needed at all.

## Open Questions

- Is it better to unify every possible AST simplification into one giantic simplification routine or is it better to factor all the semantically different optimization techniques (such as const-propagation, reduction or normaliztion, quantifier-elimination, etc.)
- How are child-expressions of n-ary expressions sorted? Need a well-defined sorting strategy for some optimizations that require normalization.

## Science

- Find a decent design for an `expr_tree!` macro that simplifies creation of expression trees via factories and a syntax similar to SMTLIB2.0.
- Try to find a decent design to model `bvsum`, `bvprod`, `conjunction` and `disjunction` in `ExprFactory`.

- Find out how to solve the problem of evaluability of bitvector `ty: Type` in `NaiveExprFactory::{s|u}extend` methods.
	- STP restricts these operations to constant values only but wraps them within expression nodes due to the bad underlying model of STP.
- Find out what scopes `push` & `pop` in STP are and how to incorporate them into this SMT solver.
	- STP has a stack of vectors that acts as assertion scope level. Users may wish to add or remove such scopes to add or remove entire
	   groups of assertions that have been added to the removed scope level. The STP scope design is inefficient and should not be taken over to Stevia. Stevia should model this concept with a single vector for the assertions and another vector for entry points to new scope levels.
