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
            | DiagnosticOutputChannel | RegularOutputChannel => true,
            _ => false,
        }
    }

    /// Returns `true` if the command is predefined and takes
    /// a numeral value as parameter.
    pub fn has_numeral_param(self) -> bool {
        use self::OptionKind::*;
        match self {
            | RandomSeed | ReproducibleResourceLimit | Verbosity => true,
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Literal<'c> {
    Bool(bool),
    String(&'c str),
    Symbol(&'c str),
    Keyword(&'c str),
    Numeral(NumeralLit<'c>),
    Decimal(DecimalLit<'c>),
}

impl<'c> Literal<'c> {
    pub fn bool(val: bool) -> Self {
        Literal::Bool(val)
    }

    pub fn string(content: &'c str) -> Self {
        Literal::String(content)
    }

    pub fn symbol(name: &'c str) -> Self {
        Literal::Symbol(name)
    }

    pub fn keyword(name: &'c str) -> Self {
        Literal::Keyword(name)
    }

    pub fn numeral(repr: &'c str) -> Self {
        Literal::Numeral(unsafe { NumeralLit::new_unchecked(repr) })
    }

    pub fn decimal(repr: &'c str) -> Self {
        Literal::Decimal(unsafe { DecimalLit::new_unchecked(repr) })
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct NumeralLit<'c> {
    repr: &'c str,
}

impl<'c> NumeralLit<'c> {
    pub unsafe fn new_unchecked(repr: &'c str) -> Self {
        Self { repr }
    }

    pub fn str_repr(self) -> &'c str {
        self.repr
    }

    pub fn to_u32(self) -> Option<u32> {
        self.repr.parse().ok()
    }

    pub fn to_u64(self) -> Option<u64> {
        self.repr.parse().ok()
    }

    pub fn to_u128(self) -> Option<u128> {
        self.repr.parse().ok()
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct DecimalLit<'c> {
    repr: &'c str,
}

impl<'c> DecimalLit<'c> {
    pub unsafe fn new_unchecked(repr: &'c str) -> Self {
        Self { repr }
    }

    pub fn str_repr(self) -> &'c str {
        self.repr
    }

    pub fn to_f32(self) -> f32 {
        self.repr.parse().unwrap()
    }

    pub fn to_f64(self) -> f64 {
        self.repr.parse().unwrap()
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum OutputChannel<'c> {
    Stderr,
    Stdout,
    File(&'c std::path::Path),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum OptionAndValue<'c> {
    DiagnosticOutputChannel(OutputChannel<'c>),
    GlobalDeclarations(bool),
    InteractiveMode(bool),
    PrintSuccess(bool),
    ProduceAssertions(bool),
    ProduceAssignments(bool),
    ProduceModels(bool),
    ProduceProofs(bool),
    ProduceUnsatAssumptions(bool),
    ProduceUnsatCores(bool),
    RandomSeed(NumeralLit<'c>),
    RegularOutputChannel(OutputChannel<'c>),
    ReproducibleResourceLimit(NumeralLit<'c>),
    Verbosity(NumeralLit<'c>),
    SimpleCustom {
        key: &'c str,
        value: Option<Literal<'c>>,
    },
    ComplexCustom {
        key: &'c str,
    },
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ProblemCategory {
    Crafted,
    Random,
    Industrial,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ProblemStatus {
    Sat,
    Unsat,
    Unknown,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum InfoAndValue<'c> {
    SMTLibVersion(DecimalLit<'c>),
    Source(&'c str),
    License(&'c str),
    Category(ProblemCategory),
    Status(ProblemStatus),
    SimpleCustom {
        key: &'c str,
        value: Option<Literal<'c>>,
    },
    ComplexCustom {
        key: &'c str,
    },
}
