use either::Either;
use std;

/// Commands available in SMTLib2 conforming solvers.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Command {
    /// Corresponds to the `assert` command.
    Assert,
    /// Corresponds to the `check-sat` command.
    CheckSat,
    /// Corresponds to the `check-sat-assuming` command.
    CheckSatAssuming,
    /// Corresponds to the `declare-const` command.
    DeclareConst,
    /// Corresponds to the `declare-datatype` command.
    DeclareDatatype,
    /// Corresponds to the `declare-datatypes` command.
    DeclareDatatypes,
    /// Corresponds to the `declare-fun` command.
    DeclareFun,
    /// Corresponds to the `declare-sort` command.
    DeclareSort,
    /// Corresponds to the `define-fun` command.
    DefineFun,
    /// Corresponds to the `define-fun-rec` command.
    DefineFunRec,
    /// Corresponds to the `define-funs-rec` command.
    DefineFunsRec,
    /// Corresponds to the `define-sort` command.
    DefineSort,
    /// Corresponds to the `echo` command.
    Echo,
    /// Corresponds to the `exit` command.
    Exit,
    /// Corresponds to the `get-assetions` command.
    GetAssertions,
    /// Corresponds to the `get-assignment` command.
    GetAssignment,
    /// Corresponds to the `get-info` command.
    GetInfo,
    /// Corresponds to the `get-model` command.
    GetModel,
    /// Corresponds to the `get-option` command.
    GetOption,
    /// Corresponds to the `get-proof` command.
    GetProof,
    /// Corresponds to the `get-unsat-assumptions` command.
    GetUnsatAssumptions,
    /// Corresponds to the `get-unsat-core` command.
    GetUnsatCore,
    /// Corresponds to the `get-value` command.
    GetValue,
    /// Corresponds to the `pop` command.
    Pop,
    /// Corresponds to the `push` command.
    Push,
    /// Corresponds to the `reset` command.
    Reset,
    /// Corresponds to the `reset-assertions` command.
    ResetAssertions,
    /// Corresponds to the `set-info` command.
    SetInfo,
    /// Corresponds to the `set-logic` command.
    SetLogic,
    /// Corresponds to the `set-option` command.
    SetOption,
}

impl Command {
    /// Returns the associated SMTLib2 string representation of `self`.
    pub fn to_str(self) -> &'static str {
        use self::Command::*;
        match self {
            Assert => "assert",
            CheckSat => "check-sat",
            CheckSatAssuming => "check-sat-assuming",
            DeclareConst => "declare-const",
            DeclareDatatype => "declare-datatype",
            DeclareDatatypes => "declare-datatypes",
            DeclareFun => "declare-fun",
            DeclareSort => "declare-sort",
            DefineFun => "define-fun",
            DefineFunRec => "define-fun-rec",
            DefineFunsRec => "define-funs-rec",
            DefineSort => "define-sort",
            Echo => "echo",
            Exit => "exit",
            GetAssertions => "get-assertions",
            GetAssignment => "get-assignment",
            GetInfo => "get-info",
            GetModel => "get-model",
            GetOption => "get-option",
            GetProof => "get-proof",
            GetUnsatAssumptions => "get-unsat-assumptions",
            GetUnsatCore => "get-unsat-core",
            GetValue => "get-value",
            Pop => "pop",
            Push => "push",
            Reset => "reset",
            ResetAssertions => "reset-assertions",
            SetInfo => "set-info",
            SetLogic => "set-logic",
            SetOption => "set-option",
        }
    }
}

/// Options of the SMTLib2 `set-option` and `get-option` commands.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum OptionKind<'c> {
    /// Corresponds to the `:diagnostic-output-channel` option.
    DiagnosticOutputChannel,
    /// Corresponds to the `:global-declarations` option.
    GlobalDeclarations,
    /// Corresponds to the `:interactive-mode` option.
    InteractiveMode,
    /// Corresponds to the `:print-success` option.
    PrintSuccess,
    /// Corresponds to the `:produce-assertions` option.
    ProduceAssertions,
    /// Corresponds to the `:produce-assignments` option.
    ProduceAssignments,
    /// Corresponds to the `:produce-models` option.
    ProduceModels,
    /// Corresponds to the `:produce-proofs` option.
    ProduceProofs,
    /// Corresponds to the `:produce-unsat-assumptions` option.
    ProduceUnsatAssumptions,
    /// Corresponds to the `:produce-unsat-core` option.
    ProduceUnsatCores,
    /// Corresponds to the `:random-seed` option.
    RandomSeed,
    /// Corresponds to the `:regular-output-channel` option.
    RegularOutputChannel,
    /// Corresponds to the `:reproducible-resource-limit` option.
    ReproducibleResourceLimit,
    /// Corresponds to the `:verbosity` option.
    Verbosity,
    /// Represents all non-predefined or unknown options.
    Custom(&'c str),
}

impl<'c> OptionKind<'c> {
    /// Returns `true` if the command is predefined and takes
    /// a value of type `bool` as parameter.
    pub fn has_bool_param(self) -> bool {
        use self::OptionKind::*;
        match self {
            | GlobalDeclarations
            | InteractiveMode
            | PrintSuccess
            | ProduceAssertions
            | ProduceAssignments
            | ProduceModels
            | ProduceProofs
            | ProduceUnsatAssumptions
            | ProduceUnsatCores => true,
            _ => false,
        }
    }

    /// Returns `true` if the command is predefined and takes
    /// an output channel value as parameter.
    pub fn has_output_channel_param(self) -> bool {
        use self::OptionKind::*;
        match self {
            DiagnosticOutputChannel | RegularOutputChannel => true,
            _ => false,
        }
    }

    /// Returns `true` if the command is predefined and takes
    /// a numeral value as parameter.
    pub fn has_numeral_param(self) -> bool {
        use self::OptionKind::*;
        match self {
            RandomSeed | ReproducibleResourceLimit | Verbosity => true,
            _ => false,
        }
    }
}

impl<'c> From<&'c str> for OptionKind<'c> {
    fn from(repr: &'c str) -> Self {
        use self::OptionKind::*;
        match repr {
            ":diagnostic-output-channel" => DiagnosticOutputChannel,
            ":global-declarations" => GlobalDeclarations,
            ":interactive-mode" => InteractiveMode,
            ":print-success" => PrintSuccess,
            ":produce-assertions" => ProduceAssertions,
            ":produce-assignments" => ProduceAssignments,
            ":produce-models" => ProduceModels,
            ":produce-proofs" => ProduceProofs,
            ":produce-unsat-assumptions" => ProduceUnsatAssumptions,
            ":produce-unsat-cores" => ProduceUnsatCores,
            ":random-seed" => RandomSeed,
            ":regular-output-channel" => RegularOutputChannel,
            ":reproducible-resource-limit" => ReproducibleResourceLimit,
            ":verbosity" => Verbosity,
            repr => Custom(repr),
        }
    }
}

/// Info flags of the SMTLib2 `get-info` command.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum GetInfoKind<'s> {
    /// Corresponds to the predefined `:all-statistics` info flag.
    AllStatistics,
    /// Corresponds to the predefined `:assertion-stack-levels` info flag.
    AssertionStackLevels,
    /// Corresponds to the predefined `:authors` info flag.
    Authors,
    /// Corresponds to the predefined `:error-behaviour` info flag.
    ErrorBehaviour,
    /// Corresponds to the predefined `:name` info flag.
    Name,
    /// Corresponds to the predefined `:reason-unknown` info flag.
    ReasonUnknown,
    /// Corresponds to the predefined `:version` info flag.
    Version,
    /// Corresponds to any non predefined info flag.
    Other(&'s str)
}

impl<'s> GetInfoKind<'s> {
    pub fn from_str(flag: &'s str) -> Self {
        match flag {
            ":all-statistics" => GetInfoKind::AllStatistics,
            ":assertion-stack-levels" => GetInfoKind::AssertionStackLevels,
            ":authors" => GetInfoKind::Authors,
            ":error-behaviour" => GetInfoKind::ErrorBehaviour,
            ":name" => GetInfoKind::Name,
            ":reason-unknown" => GetInfoKind::ReasonUnknown,
            ":version" => GetInfoKind::Version,
            s => GetInfoKind::Other(s)
        }
    }
}

/// View to a literal or constant specified in the SMTLib2 input language.
///
/// # Note
///
/// This is most often just a simple string sub slice into the given input
/// that was previously parsed and found to be a literal match.
///
/// This could either represent
///
/// - a boolean: `true` or `false`
/// - a string: `"Hello, World!"`
/// - a symbol: `foo`
/// - a keyword: `:bar`
/// - a numeral: `42`
/// - a decimal: `7.4`
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Literal<'c> {
    /// A boolean literal.
    Bool(bool),
    /// A string literal.
    String(&'c str),
    /// A simple or quoted symbol.
    ///
    /// # Note
    ///
    /// At this level of abstraction there is no distinction made
    /// between simply and quoted symbols of the SMTLib2 format.
    Symbol(&'c str),
    /// A keyword.
    Keyword(&'c str),
    /// A numeral literal.
    ///
    /// # Note
    ///
    /// The possible encodings for this are decimal, binary or hexadecimal.
    /// Binary starts with `#b`, hexadecimal starts with `#x` and decimal
    /// starts with any digit.
    Numeral(NumeralLit<'c>),
    /// A decimal literal.
    Decimal(DecimalLit<'c>),
}

impl<'c> Literal<'c> {
    /// Creates a new boolean literal from the given boolean value.
    pub fn bool(val: bool) -> Self {
        Literal::Bool(val)
    }

    /// Creates a new string literal for the given string slice.
    ///
    /// # Note
    ///
    /// This given string slice is not checked to match the properties
    /// of a valid SMTLib2 string literal.
    pub fn string(content: &'c str) -> Self {
        Literal::String(content)
    }

    /// Creates a new symbol for the given string slice.
    ///
    /// # Note
    ///
    /// This given string slice is not checked to match the properties
    /// of a valid SMTLib2 symbol.
    pub fn symbol(name: &'c str) -> Self {
        Literal::Symbol(name)
    }

    /// Creates a new keyword for the given string slice.
    ///
    /// # Note
    ///
    /// This given string slice is not checked to match the properties
    /// of a valid SMTLib2 keyword.
    pub fn keyword(name: &'c str) -> Self {
        Literal::Keyword(name)
    }

    /// Creates a new numeral literal for the given string slice.
    ///
    /// # Note
    ///
    /// This given string slice is not checked to match the properties
    /// of a valid SMTLib2 numeral literal.
    pub fn numeral(repr: &'c str) -> Self {
        Literal::Numeral(NumeralLit::from_str(repr))
    }

    /// Creates a new decimal literal for the given string slice.
    ///
    /// # Note
    ///
    /// This given string slice is not checked to match the properties
    /// of a valid SMTLib2 decimal literal.
    pub fn decimal(repr: &'c str) -> Self {
        Literal::Decimal(unsafe { DecimalLit::new_unchecked(repr) })
    }
}

/// Represents a radix that describes in which number system an associated
/// string represents a numeral value.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Radix {
    /// Binary number system.
    ///
    /// # Note
    ///
    /// In SMTLib2 binary decoded numerals always start with `#b` in
    /// their string representation.
    Binary,
    /// Hexa-decimal number system.
    ///
    /// # Note
    ///
    /// In SMTLib2 hexa-decimal decoded numerals always start with `#x`
    /// in their string representation.
    Hexdec,
    /// Decimal number system.
    ///
    /// # Note
    ///
    /// In SMTLib2 all numerals that have no special prefix are encoded
    /// in the decimal number system.
    Decimal,
}

impl Radix {
    /// Converts the radix into a `u32` value.
    ///
    /// # Note
    ///
    /// This is useful since most standard library features that
    /// interact with radices are in fact operating on raw `u32` values.
    pub fn to_u32(&self) -> u32 {
        match self {
            Radix::Binary => 2,
            Radix::Hexdec => 16,
            Radix::Decimal => 10,
        }
    }
}

/// Represents a numeral literal.
///
/// # Note
///
/// This is just a simple string sub slice into a part
/// of the input string that has been found to be a valid
/// numeral literal.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct NumeralLit<'c> {
    /// The number representation as string.
    repr: &'c str,
    /// The radix at which the digits within `repr` are interpreted.
    radix: Radix,
}

impl<'c> NumeralLit<'c> {
    fn new(radix: Radix, repr: &'c str) -> Self {
        NumeralLit { radix, repr }
    }

    pub(crate) fn from_str(repr: &'c str) -> Self {
        if repr.is_empty() {
            panic!("empty representations are invalid numeral literals") // TODO: replace with proper error
        }
        let radix = if repr.starts_with("#") {
            if repr.len() < 3 {
                panic!("invalid length of numeral literal with radix annotation (e.g. #b1") // TODO: replace with proper error
            }
            if repr.starts_with("#b") {
                Radix::Binary
            } else if repr.starts_with("#x") {
                Radix::Hexdec
            } else {
                panic!("unknown radix identifier: {}", &repr[0..1]) // TODO: replace with proper error
            }
        } else {
            Radix::Decimal
        };
        let offset = match radix {
            Radix::Binary => "#b".len(),
            Radix::Hexdec => "#x".len(),
            Radix::Decimal => 0,
        };
        let raw_repr = &repr[offset..];
        if raw_repr.chars().any(|c| !c.is_digit(radix.to_u32())) {
            panic!("not all characters are valid digits for the given radix") // TODO: replace with proper error
        }
        NumeralLit::new(radix, raw_repr)
    }

    /// Returns either a `u128` representing the value of the numeral
    /// literal or returns a pair of raw string representation and associated
    /// radix for its encoding if the value cannot be represented
    /// by a single `u128`.
    pub fn value(&self) -> Either<u128, (&str, Radix)> {
        use std::u128;
        match u128::from_str_radix(self.repr, self.radix.to_u32()) {
            Ok(val) => Either::Left(val),
            Err(_) => Either::Right((self.repr, self.radix)),
        }
    }
}

/// Represents a decimal literal.
///
/// # Note
///
/// This is just a simple string sub slice into a part
/// of the input string that has been found to be a valid
/// decimal literal.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct DecimalLit<'c> {
    repr: &'c str,
}

impl<'c> DecimalLit<'c> {
    /// Creates a new decimal literal for the given string slice.
    ///
    /// # Safety
    ///
    /// This given string slice is not checked to match the properties
    /// of a valid SMTLib2 decimal literal.
    pub unsafe fn new_unchecked(repr: &'c str) -> Self {
        Self { repr }
    }

    /// Returns the string representation of this decimal literal.
    pub fn str_repr(self) -> &'c str {
        self.repr
    }

    /// Returns a `f32` representation of this decimal literal.
    ///
    /// # Note
    ///
    /// This could lead to information loss during convertion.
    pub fn to_f32(self) -> f32 {
        self.repr.parse().unwrap()
    }

    /// Returns a `f32` representation of this decimal literal.
    ///
    /// # Note
    ///
    /// This could lead to information loss during convertion.
    pub fn to_f64(self) -> f64 {
        self.repr.parse().unwrap()
    }
}

/// The output channel that is a parameter to the SMTLib2
/// commands `:diagnostic-output-channel` and `:regular-output-channel`.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum OutputChannel<'c> {
    /// Standard out.
    Stderr,
    /// Standard in.
    Stdout,
    /// Stream into the file at the given path.
    File(&'c std::path::Path),
}

/// An option key and its associated value.
///
/// This covers all predefined options and their value types
/// as well as custom commands with their parameters.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum OptionAndValue<'c> {
    /// Corresponds to the `:diagnostic-output-channel` and its given output channel.
    DiagnosticOutputChannel(OutputChannel<'c>),
    /// Corresponds to the `:global-declarations` and its boolean parameter.
    GlobalDeclarations(bool),
    /// Corresponds to the `:interactive-mode` and its boolean parameter.
    InteractiveMode(bool),
    /// Corresponds to the `:print-success` and its boolean parameter.
    PrintSuccess(bool),
    /// Corresponds to the `:produce-assertions` and its boolean parameter.
    ProduceAssertions(bool),
    /// Corresponds to the `:produce-assignments` and its boolean parameter.
    ProduceAssignments(bool),
    /// Corresponds to the `:produce-models` and its boolean parameter.
    ProduceModels(bool),
    /// Corresponds to the `:produce-proofs` and its boolean parameter.
    ProduceProofs(bool),
    /// Corresponds to the `:produce-unsat-assumptions` and its boolean parameter.
    ProduceUnsatAssumptions(bool),
    /// Corresponds to the `:produce-unsat-cores` and its boolean parameter.
    ProduceUnsatCores(bool),
    /// Corresponds to the `:random-seed` and its numeral parameter.
    RandomSeed(NumeralLit<'c>),
    /// Corresponds to the `:regular-output-channel` and its given output channel.
    RegularOutputChannel(OutputChannel<'c>),
    /// Corresponds to the `:reproducible-resource-limit` and its numeral parameter.
    ReproducibleResourceLimit(NumeralLit<'c>),
    /// Corresponds to the `:verbosity` and its numeral parameter.
    Verbosity(NumeralLit<'c>),
    /// Corresponds to non predefined option that has exactly one single value.
    SimpleCustom {
        /// The key of the simple custom command.
        key: &'c str,
        /// The optional value of the simple custom command.
        value: Option<Literal<'c>>,
    },
    /// Corresponds to non predefined option that has a recursively defined value.
    ComplexCustom {
        /// The key of the complex custom command.
        key: &'c str,
    },
}

/// Represents a problem category for an SMT problem instance.
///
/// SMTLib2 problems are either crafted, randomly created or industrial
/// which represents all other problems.
///
/// This is used as a value to the `set-info` command using the
/// `:category` meta attribute.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ProblemCategory {
    /// The problem was crafted by an author.
    Crafted,
    /// The problem was randomly generated.
    Random,
    /// Any other way that a problem was created.
    Industrial,
}

/// Represents the satisfiability of a corresponding SMTLib2 problem instance.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ProblemStatus {
    /// The next call to `(assert)` must be satisfiable.
    Sat,
    /// The next call to `(assert)` must be unsatisfiable.
    Unsat,
    /// The satisfiability of the next call to `(assert)` is unknown.
    Unknown,
}

/// Represents an info and its respective value when invoking the `set-info`
/// SMTLib2 command.
///
/// There are some predefined info kinds and their associated value type
/// as well as custom info kinds and their generic values.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum InfoAndValue<'c> {
    /// Corresponds to the `:smt-lib-version` info flag and its decimal parameter.
    SMTLibVersion(DecimalLit<'c>),
    /// Corresponds to the `:source` info flag and its string or quoted symbol parameter.
    Source(&'c str),
    /// Corresponds to the `:license` info flag and its string parameter.
    License(&'c str),
    /// Corresponds to the `:category` info flag and its associated value.
    Category(ProblemCategory),
    /// Corresponds to the `:status` info flag and its associated value.
    Status(ProblemStatus),
    /// Corresponds to any non predefined info flag that has exactly one value.
    SimpleCustom {
        /// The key of the custom info flag.
        key: &'c str,
        /// The optional value of the custom info flag.
        value: Option<Literal<'c>>,
    },
    /// Corresponds to any non predefined info flag that has a potentially complex value.
    ComplexCustom {
        /// The key of the custom info flag.
        key: &'c str,
    },
}
