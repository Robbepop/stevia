# Stevia - Satisfiability Modulo Theories (SMT) Solver

|       Linux       |       Windows       |      Coveralls       |      Codecov       |     Metrics      |
|:-----------------:|:-------------------:|:--------------------:|:------------------:|:----------------:|
| [![travis][0]][1] | [![appveyor][2]][3] | [![coveralls][4]][5] | [![licence][6]][7] | [![tokei][8]][9] |

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

- [`#![feature(box_patterns)]`][unstable-box-patterns]
- [`#![feature(nll)]`][nll]
- [`#![feature(crate_in_paths)]`][crate-in-paths]
- ~~[`#![feature(conservative_impl_trait)]`][conservative-impl-trait]~~ (stable in 1.26)
- ~~[`#![feature(copy_closures)]`][copy-closures]~~ (stable in 1.26)
- ~~[`#![feature(clone_closures)]`][clone-closures]~~ (stable in 1.26)
- ~~[`#![feature(match_default_bindings)]`][match-default-bindings]~~ (stable in 1.26)

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

[unstable-box-patterns]: https://github.com/rust-lang/rust/issues/29641
[conservative-impl-trait]: https://github.com/rust-lang/rust/issues/34511
[nll]: https://github.com/rust-lang/rust/issues/43234
[copy-closures]: https://github.com/rust-lang/rust/issues/44490
[clone-closures]: https://github.com/rust-lang/rust/issues/44490
[match-default-bindings]: https://github.com/rust-lang/rust/issues/42640
[crate-in-paths]: https://github.com/rust-lang/rust/issues/44660
