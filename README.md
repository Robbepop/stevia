# Stevia - Satisfiability Modulo Theories (SMT) Solver

|       Linux       |       Windows       |      Coveralls       |      Codecov       |
|:-----------------:|:-------------------:|:--------------------:|:------------------:|
| [![travis][0]][1] | [![appveyor][2]][3] | [![coveralls][4]][5] | [![licence][6]][7] |

---

This is a brave attempt to write a simple [SMT][smt-wiki] solver in the [Rust][rust-home] ([github][rust-repo]) programming language based on the design of [STP][stp-home] ([github][stp-repo]) and [Boolector][boolector-home].

Currently the solver is in very early development phase.

## Very future goals are

- Support for [SMTLib 2.6][smtlib-home].
- Theories of quantifier-free bitvectors and arrays: `QF_ABV`
- Comprehensive documentation for all important parts of the code.
- Eventually be able to keep up with other SMT solvers like STP.
- C API to enable bindings for other languages.
- Use an efficient SAT solver under the hood, like [candy][candy-repo] and [JamSat][jamsat-repo].

## Simplifications

Stevia will support a great machinery of simplifications to its input formulas.
An early example of what is possible now:

```lisp
(=
  (=
    (=
      false
      (= (_ :32  42) (_ :32 1337) )
    )
    (= (_ :32 42) (_ :32 42) )
  )
  (=
    (= (not true) (= true (not true) ) )
    (= ; Here is the break: true is not false!
      (and true true)
      (= (_ :64 100) (-(-(_ :64 100))) )
    )
  )
)
```

Is getting simplified to this:

```lisp
false
```

Keep in mind that this is still a pretty naive simplification. More to come in future versions of Stevia!

## Unstable Features Used

These features need to be stabilized before this crate can be used on the stable channel.

- [`#![feature(box_patterns)]`][unstable-box-patterns]
- [`#![feature(conservative_impl_trait)]`][conservative-impl-trait]
- [`#![feature(nll)]`][nll]

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