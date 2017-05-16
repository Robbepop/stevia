# Simplifications

The following simplifications on expression trees are listed here.

These are not currently implemented in Stevia but are planned or debated for future versions.

- If

	- [x] Const evaluation: `(ite true a b)` to `a` and `(ite false a b)` to `b`
	- [ ] Equivalence elimination: `(ite c a a)` to `a`

- Equals

	- [x] Const evaluation: `(= a b)` to `true` where `a` and `b` are const and evaluate to the same value
	- [x] Const contradiction: `(= a b)` to `false` where `a` and `b` are const and evaluate to a distinct value
	- [x] Logical contradiction: `(= a (not a))` to `false` and `(= a (neg a))` to `false`
	- [x] Flattening: `(= (= a b) (= c d))` to `(= a b c d)`
	- [x] Normalization by ordering of child expressions.

- Symbol

	- [ ] Lookup of constrains that enforces a constant value for it. (Solvable by linear solver. Or maybe better?)

- Not

	- [x] Not-Elimination: `(not (not a)` to `a`
	- [x] Const evaluation: `(not c1)` to `c2` where `c1` is const and `c2` is not `c1`

- And

	- [ ] Constant taugology detection: `(and true true)` to `true`
	- [ ] Constant contradiction detection: `(and true false)` to `false`
	- [ ] Equal-contradiction detection: `(and a (not a))` to `false`
	- [ ] Demorgan-transformation: `(and (not a) (not b))` to `(not (or a b))`
	- [ ] Flattening: `(and (and a b) (and c d))` to `(and a b c d)`
	- [ ] Normalization by ordering of child expressions.

- Or

	- [ ] Constant tautology extraction: `(or false true)` to `true`
	- [ ] Constant contradiction extraction: `(or false false)` to `false`
	- [ ] Equal-tautology detection: `(or a (not a))` to `true`
	- [ ] Demorgan-transformation: `(or (not a) (not b))` to `(not (and a b))`
	- [ ] Flattening: `(or (or a b) (or c d))` to `(or a b c d)`
	- [ ] Normalization by ordering of child expressions.

- Xor

- Iff (deprecated for equals?)

- Implies

- Parametric Bool

- Add

	- [ ] Const Propagation: `(+ c1 c2)` to `c3` where `c1` and `c2` are both constant and `c3 = c1 + c2`.
	- [ ] Neutral Element: `(+ a 0)` to `a`
	- [ ] Inverse Elimination: `(+ a (-a))` to `0`
	- [ ] Negation-Pulling: `(+ (-a) (-b))` to `(- (+ a b))`
	- [ ] Lowering to `mul`: `(+ a a)` to `(* 2 a)`
	- [ ] Flattening: `(+ (+ a b) (+ c d))` to `(+ a b c d)`
	- [ ] Normalization by ordering of child expressions.

- Neg

	- [x] Neg-Elimination: `(- (- a)` to `a`
	- [ ] Const evaluation: `(- c1)` to `c2` where `c1` is const and `c2` is the negation of `c1`

- Sub

	- [ ] Const Propagation: `(- c1 c2)` to `c3` where `c1` and `c2` are both constant and `c3 = c1 - c2`.
	- [ ] Equal Elimination: `(- a a)` to `0`
	- [ ] Negation-Elimination: `(- a (-b))` to `(+ a b)`

- Mul

	- [ ] Neutral Element: `(* a 1)` to `a`
	- [ ] Nulling: `(* a 0)` to `0`
	- [ ] Powers-of-Two: `(* a n)` to `(<< a (log n))` where `n` is a power of two.
	- [ ] Flattening: `(* (* a b) (* c d))` to `(* a b c d)`
	- [ ] Normalization by ordering of expressions.

- Div

	- [ ] Division by zero: `(/ a 0)` to `Undefined` <- signaling undefined behaviour to the user.
	- [ ] Neutral Element: `(/ a 1)` to `a`
	- [ ] Self-Division: `(/ a a)` to `1`
	- [ ] Inverse Elimination: `(/ a (/ 1 a))` to `a`
	- [ ] Negation-Pulling: `(/ a (-b))` to `(- (/ a b))`
