# TODO-List for Stevia

## AST

- Improve doc-comments of some expressions. E.g. remove the ` ticks.
- Reduce code bloat by introducing further code-gen macros.
- Add proper error management to the AST module. Maybe use failure?

## Long term

- Find and depend on decent library implementation similar to STP's `libabc` for and-inverter-graph (AIG) computation..
- Add SMTLib2.X serialization (printer) and deserialization (parser) support.
- Implement `simple_type_check` method to naively check the children's type of a newly created expression for validity. This can be used by factory implementations that want to check for this addional safety guard. (Maybe this is not needed if we always create new child expressions with a type-checking factory!)

## Considerations

- Think about trade-offs by adding `Nand`, `Nor` and `Xnor` as new formula types.

## Science

- Find a decent design for an `expr_tree!` macro that simplifies creation of expression trees via factories and a syntax similar to SMTLIB2.0.
- Find out what scopes `push` & `pop` in STP are and how to incorporate them into this SMT solver.
	- STP has a stack of vectors that acts as assertion scope level. Users may wish to add or remove such scopes to add or remove entire
	   groups of assertions that have been added to the removed scope level. The STP scope design is inefficient and should not be taken over to Stevia. Stevia should model this concept with a single vector for the assertions and another vector for entry points to new scope levels.
