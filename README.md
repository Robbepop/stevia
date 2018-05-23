# Stevia - Satisfiability Modulo Theories (SMT) Solver

|       Linux       |       Windows       |       Chat        |      Coveralls       |      Codecov       |     Metrics      |
|:-----------------:|:-------------------:|:-----------------:|:--------------------:|:------------------:|:----------------:|
| [![travis][0]][1] | [![appveyor][2]][3] | [![chat][10]][11] | [![coveralls][4]][5] | [![licence][6]][7] | [![tokei][8]][9] |

---

This is a brave attempt to write a simple [SMT][smt-wiki] solver in the [Rust][rust-home] ([github][rust-repo]) programming language.

It is based on the design of:

- [STP][stp-home] ([github][stp-repo])
- [Boolector][boolector-home].

Currently the solver is in very early development phase.

## Supported Theories (SMT)

- Bitvectors of fixed bit-width and modulo-two arithmetics.
- Non-extensional arrays, indexed by bitvectors with bitvector values.
- Only supports quantifier-free inputs.

The combined theory in SMT notation is called `QF_ABV`.

## Future Goals

- Support inputs specified in [SMTLib 2.6][smtlib-home].
- Comprehensive documentation for all important parts of the code.
- Eventually be able to keep up with efficient SMT solvers like STP.
- C API to enable bindings for other languages.
- Use an efficient SAT solver under the hood, like [candy][candy-repo] and [JamSAT][jamsat-repo].

## Simplifications

Stevia supports word-level transformations, called simplifications, that it applies throughout the solving process.
In the following is an example of what is possible with the WIP implementation of the simplifier.

The arithmetic expression in LISP syntax:

```lisp
(+ x 42 (- x y) (* y (-5)) (- (+ x 10 y)))
```

Is simplified to:

```lisp
(+ 32 (* -7 y) x)
```

This output can then be further processed by other simplification and solving processes.

## Unstable Features Used

These features need to be stabilized before this crate can be used on the stable channel.

**Current State:** Rust version 1.26

- [`#![feature(crate_in_paths)]`][unstable_crate_in_paths]

- **Simplifier**

    - [`#![feature(box_patterns)]`][unstable_box_patterns]
    - [`#![feature(nll)]`][unstable_nll]

- **Bitblaster**

    - [`#![feature(fn_traits)]`][unstable_fn_traits]
    - [`#![feature(unboxed_closures)]`][unstable_unboxed_closures]

## License

Licensed under either of

 * Apache license, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Dual licence: [![badge][license-mit-badge]](LICENSE-MIT) [![badge][license-apache-badge]](LICENSE-APACHE)

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.

[0]: https://travis-ci.org/Robbepop/stevia.svg?branch=master
[1]: https://travis-ci.org/Robbepop/stevia

[2]: https://ci.appveyor.com/api/projects/status/16fc9l6rtroo4xqd?svg=true
[3]: https://ci.appveyor.com/project/Robbepop/stevia/branch/master

[4]: https://coveralls.io/repos/github/Robbepop/stevia/badge.svg?branch=master
[5]: https://coveralls.io/github/Robbepop/stevia?branch=master

[6]: https://codecov.io/gh/Robbepop/stevia/branch/master/graph/badge.svg
[7]: https://codecov.io/gh/Robbepop/stevia/branch/master

[8]: https://tokei.rs/b1/github/robbepop/stevia?category=code
[9]: https://github.com/Aaronepower/tokei#badges

[10]: https://badges.gitter.im/stevia-solver/gitter.svg
[11]: https://gitter.im/stevia-solver/Lobby?utm_source=share-link&utm_medium=link&utm_campaign=share-link

[license-mit-badge]: https://img.shields.io/badge/license-MIT-blue.svg
[license-apache-badge]: https://img.shields.io/badge/license-APACHE-orange.svg

[smt-wiki]: https://en.wikipedia.org/wiki/Satisfiability_modulo_theories
[rust-home]: https://www.rust-lang.org/
[rust-repo]: https://github.com/rust-lang/rust
[stp-home]: http://stp.github.io/
[stp-repo]: https://github.com/stp/stp
[boolector-home]: http://fmv.jku.at/boolector/
[smtlib-home]: http://smtlib.cs.uiowa.edu/index.shtml
[candy-repo]: https://github.com/Udopia/candy-kingdom
[jamsat-repo]: https://github.com/fkutzner/JamSAT

[unstable_box_patterns]: https://github.com/rust-lang/rust/issues/29641
[unstable_nll]: https://github.com/rust-lang/rust/issues/43234
[unstable_crate_in_paths]: https://github.com/rust-lang/rust/issues/44660
[unstable_fn_traits]: https://github.com/rust-lang/rust/issues/29625
[unstable_unboxed_closures]: https://github.com/rust-lang/rust/issues/29625
