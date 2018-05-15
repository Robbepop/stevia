## Simplifier

The simplifier is a term rewriting system for the theories of bitvector and arrays.
Currently only a fraction of the final rewriting rules are implemented.

The simplifier's architecture consists of many different simplification passes that have a unique
and distinct simplification job within the entire simplification procedure.
The simplifier calls those simplification passes similar as to how a modern compiler invokes its
semantic checking and optimizing passes over the abstract code.

This `README` will contain a brief description of all simplification passes as well as a list
of all expressions and their associated simplification rules and their connection to the passes
to provide readers of this `README` an overview of all simplification rules and passes.

### Simplifications

#### Boolean Symbolic Solver

Solves boolean formulas at a symbolic level.

Source: [Link][100]

#### Boolean Constant Propagator

Propagates and computes constant boolean formulas.

Source: [Link][110]

#### Comparison Reducer

Lowers the many different forms of comparison expressions to just use less-than.
This is the same for signed and unsigned comparison expressions.

Having to deal with less different forms for the same thing makes it simpler
to write more thoughough simplifications for other rules.

For example this lowers `(>= a b)` to `(not (< a b))` or `(> a b)` to `(< b a)`.

Source: [Link][140]

#### Flattener

Flattens some expressions with respect to their child expressions.

For example `(+ (+ a b) (+ c d))` is going to be flattened to the simpler
structure `(+ a b c d)`. This has the advantage of widening the context of other
simplifications that may occure. For example `(+ (+ (-5) a) (+ 5 b))` will
be simplified to `(+ (-5) a 5 b)` so that the symbolic solver is able to
identify `(-5)` and `5` as additive inverse elements thus eliminating them
resulting in the final `(+ a b)` expression.

Source: [Link][130]

#### Involution

Solves double negations of any generic form.

This includes boolean `Not` as well as expressions such as `Neg` and `BitNot`.

For example this simplifies `(-(-x))` to `a` or `(!(!a))` to `a`.

Source: [Link][150]

#### Normalizer

Normalizes some expressions with respect to their child expression ordering
as well as removing duplicate child expressions if necesary.
This simplification allows to compare expressions symbolically with each other
even if they are structurally different in the beginning such as in `(= (+ a b) (+ b a))`.

Normalization would bring both `Add` child expressions into the same form so
that the symbolic solver can see that they are the same and simplify the entire
expression to `true`.

Source: [Link][120]

### If Constraint Propagation

Propagates condition constraints towards then- and else cases.

For example `(if c (not c) d)` is going to be simplified to `(if c false d)`.

Source: [Link][160]

### Expressions

#### Legend

|      Symbol       |           Meaning           |
|:-----------------:|:---------------------------:|
| `⊤`               | Symbol representing `true`  |
| `⊥`               | Symbol representing `false` |
| `x ➔ y`           | `x` is simplified to `y`    |
| ☑                 | Simplification already implemented. |
| ☐                 | Simplification currently unimplemented. |

#### IfThenElse

- Formula `(ite condition then_case else_case)`

	- [x] `(ite c t e)` where `t == e` ➔ `t` ([BoolSymbolicSolver](#boolean-symbolic-solver))
	- [x] `(ite (not c) t e)` ➔ `(ite c e t)` ([BoolSymbolicSolver](#boolean-symbolic-solver))
	- [x] `(ite ⊤ t e)` ➔ `t` ([BoolConstPropagator](#boolean-constant-propagator))
	- [x] `(ite ⊥ t e)` ➔ `e` ([BoolConstPropagator](#boolean-constant-propagator))
	- [x] `(ite c t e)` where `t, e ∈ {⊤, ⊥}` and `t = e` ➔ `t` ([BoolConstPropagator](#boolean-constant-propagator))
	- [x] `(ite c ⊤ ⊥)` ➔ `c` ([BoolConstPropagator](#boolean-constant-propagator))
	- [x] `(ite c ⊥ ⊤)` ➔ `not c` ([BoolConstPropagator](#boolean-constant-propagator))
	- [x] `(ite c ⊤ e)` ➔ `(or c e)` ([BoolConstPropagator](#boolean-constant-propagator))
	- [x] `(ite c t ⊤)` ➔ `(or (not c) t)` ([BoolConstPropagator](#boolean-constant-propagator))
	- [x] `(ite c ⊥ e)` ➔ `(and (not c) e)` ([BoolConstPropagator](#boolean-constant-propagator))
	- [x] `(ite c t ⊥)` ➔ `(and c t)` ([BoolConstPropagator](#boolean-constant-propagator))
	- [x] `(ite c c (not c))` ➔ `(ite c ⊤ ⊥)` ([IfConstraintPropagator](#if-constraint-propagation))


[100]: https://github.com/Robbepop/stevia/blob/master/stevia_simplifier/src/simplifications/bool_symbolic_solver.rs
[110]: https://github.com/Robbepop/stevia/blob/master/stevia_simplifier/src/simplifications/bool_const_prop.rs
[120]: https://github.com/Robbepop/stevia/blob/master/stevia_simplifier/src/simplifications/normalizer.rs
[130]: https://github.com/Robbepop/stevia/blob/master/stevia_simplifier/src/simplifications/flattening.rs
[140]: https://github.com/Robbepop/stevia/blob/master/stevia_simplifier/src/simplifications/cmp_reduction.rs
[150]: https://github.com/Robbepop/stevia/blob/master/stevia_simplifier/src/simplifications/involution.rs
[160]: https://github.com/Robbepop/stevia/blob/master/stevia_simplifier/src/simplifications/if_constraint_prop.rs
