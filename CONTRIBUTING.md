# Contribution Guidelines

First of all, thank you for your interest in contributing to this project!

Sorry beforehand if these contribution guidelines do not contain enough emojies ...

## Creating an Issue

Before creating an issue please search in the [issue tracker] at GitHub for issues
concerning the same work, bug fix, or feature request.

Try to provide an appropriate upper-case starting issue title.

## Creating a Pull Request

### When implementing a new feature

Before creating a pull request to implement a new feature it might be a good idea
to discuss the new feature with the other contributors and maintainers.
For this please open an issue that tracks the discussion and implementation status
of the requested feature.

### When fixing a bug

Please create a link to the existing issue that tracks the bug.
Bugs that are not tracked are unknown to the project.
Please create an issue first so that people can find information about
this bug in the future.

Also please provide regression tests for the implemented bug fix to
stop this bug from happing again in future versions of the project.

## Coding Conventions

Before committing changes please make sure that you have auto-formatted the
changed parts (not the entire document or project) using [rust-fmt][link-to-rust-fmt].

The `.rustfmt.toml` file in the root directory of the project stores all settings
that diverge from the current Rust formatting defaults.

## Testing

Please provide tests for new features implemented in your pull requests.

Test code should be kept simple and many small tests are preferred over a few large tests.

## Commit Message Guidelines

For our commit messages we stick to the following structure:

```
<commit_header>(<module>): <short_description>
<br>
<long_description>
```

- `<commit_header>` describes the kind of work done by the commit.
                    It is one of the items in [this list][commit_headers].
- `<module>` is the representant of the many modules within the project.
             This is to better localize changes within the project.
             To allow for a more fine grained localization we can separate
             parent modules via `/`.
             If not a single module is applicable (e.g. refactoring over the entire code base)
             for the associated work done in the commit we can simply use `*`.
- `<short_description>` is a single short sentence describing the work that is done by this commit
                        in an imperative fashion. There shall be no punctuation and it should
                        be in small case.
- `<br>` represents an empty line (only shown for demonstration here)
- `<long_description>` is an optional longer description that might consists of multiple sentences.
                       The long description should start in upper case and should contain punctuation.

### Commit Headers

- **feat**: implementing a new feature
- **fix**: fixing a bug
- **refactor**: refactoring or restructuring code
- **style**: non-semantic changes to code, simple whitespace refactorings etc.
- **test**: adding tests, fixing tests, restructuring tests
- **chores**: work on build system, CI, release of versions etc.
- **perf**: performance improvements

### Examples

#### Short Commit Message

```
refactor(Bitblaster): rename LitPack::i to LitPack::get_unchecked
```

[Link][link-to-short-example]

#### Long Commit Message

```
feat(Bitblaster): add LitPack::flip_all method

This method allows to flip the polarities of all literals yielded by the LitPack.
This is useful for certain use cases, such as negating outputs and is efficiently
implementable.
```

[Link][link-to-long-example]

[link-to-rust-fmt]: https://github.com/rust-lang-nursery/rustfmt
[link-to-short-example]: https://github.com/Robbepop/stevia/commit/56dd1e78418b65db8a812534ce592db9aadf3431
[link-to-long-example]: https://github.com/Robbepop/stevia/commit/525d229c60059a0d3146703e0fbd93af352176cc
