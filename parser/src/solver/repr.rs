use std;

use crate::parser::{
    Numeral,
    Decimal
};

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

use std::str::FromStr;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnknownCommand;

impl FromStr for Command {
    type Err = UnknownCommand;

    /// Returns the associated command for the given identifier string.
    /// 
    /// # Note
    /// 
    /// Returns an error if there is no such command.
    fn from_str(input: &str) -> Result<Self, Self::Err> {
        match input {
            "assert" => Ok(Command::Assert),
            "check-sat" => Ok(Command::CheckSat),
            "check-sat-assuming" => Ok(Command::CheckSatAssuming),
            "declare-const" => Ok(Command::DeclareConst),
            "declare-datatype" => Ok(Command::DeclareDatatype),
            "declare-datatypes" => Ok(Command::DeclareDatatypes),
            "declare-fun" => Ok(Command::DeclareFun),
            "declare-sort" => Ok(Command::DeclareSort),
            "define-fun" => Ok(Command::DefineFun),
            "define-fun-rec" => Ok(Command::DefineFunRec),
            "define-funs-rec" => Ok(Command::DefineFunsRec),
            "define-sort" => Ok(Command::DefineSort),
            "echo" => Ok(Command::Echo),
            "exit" => Ok(Command::Exit),
            "get-assertions" => Ok(Command::GetAssertions),
            "get-assignment" => Ok(Command::GetAssignment),
            "get-info" => Ok(Command::GetInfo),
            "get-model" => Ok(Command::GetModel),
            "get-option" => Ok(Command::GetOption),
            "get-proof" => Ok(Command::GetProof),
            "get-unsat-assumptions" => Ok(Command::GetUnsatAssumptions),
            "get-unsat-core" => Ok(Command::GetUnsatCore),
            "get-value" => Ok(Command::GetValue),
            "pop" => Ok(Command::Pop),
            "push" => Ok(Command::Push),
            "reset" => Ok(Command::Reset),
            "reset-assertions" => Ok(Command::ResetAssertions),
            "set-info" => Ok(Command::SetInfo),
            "set-logic" => Ok(Command::SetLogic),
            "set-option" => Ok(Command::SetOption),
            _ => Err(UnknownCommand),
        }
    }
}

impl Command {
    /// Returns the associated SMTLib2 string representation of `self`.
    pub fn to_str(self) -> &'static str {
        match self {
            Command::Assert => "assert",
            Command::CheckSat => "check-sat",
            Command::CheckSatAssuming => "check-sat-assuming",
            Command::DeclareConst => "declare-const",
            Command::DeclareDatatype => "declare-datatype",
            Command::DeclareDatatypes => "declare-datatypes",
            Command::DeclareFun => "declare-fun",
            Command::DeclareSort => "declare-sort",
            Command::DefineFun => "define-fun",
            Command::DefineFunRec => "define-fun-rec",
            Command::DefineFunsRec => "define-funs-rec",
            Command::DefineSort => "define-sort",
            Command::Echo => "echo",
            Command::Exit => "exit",
            Command::GetAssertions => "get-assertions",
            Command::GetAssignment => "get-assignment",
            Command::GetInfo => "get-info",
            Command::GetModel => "get-model",
            Command::GetOption => "get-option",
            Command::GetProof => "get-proof",
            Command::GetUnsatAssumptions => "get-unsat-assumptions",
            Command::GetUnsatCore => "get-unsat-core",
            Command::GetValue => "get-value",
            Command::Pop => "pop",
            Command::Push => "push",
            Command::Reset => "reset",
            Command::ResetAssertions => "reset-assertions",
            Command::SetInfo => "set-info",
            Command::SetLogic => "set-logic",
            Command::SetOption => "set-option",
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
            GlobalDeclarations
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
    Other(&'s str),
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
            s => GetInfoKind::Other(s),
        }
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

impl<'c> OutputChannel<'c> {
    /// Creates a new output channel from the given string identifier.
    /// 
    /// # Note
    /// 
    /// This fallbacks into a file output channel.
    pub fn from_str(s: &str) -> OutputChannel {
        use std::path::Path;
        match s {
            "stderr" => OutputChannel::Stderr,
            "stdout" => OutputChannel::Stdout,
            file => OutputChannel::File(Path::new(file))
        }
    }
}

/// An option key and its associated value.
///
/// This covers all predefined options and their value types
/// as well as custom commands with their parameters.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum OptionAndValue<'c, E> {
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
    RandomSeed(Numeral<'c>),
    /// Corresponds to the `:regular-output-channel` and its given output channel.
    RegularOutputChannel(OutputChannel<'c>),
    /// Corresponds to the `:reproducible-resource-limit` and its numeral parameter.
    ReproducibleResourceLimit(Numeral<'c>),
    /// Corresponds to the `:verbosity` and its numeral parameter.
    Verbosity(Numeral<'c>),
    /// Corresponds to non predefined option that might have a value.
    Other {
        /// The key of the simple custom command.
        key: &'c str,
        /// The optional value of the simple custom command.
        value: Option<E>,
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

impl ProblemCategory {
    /// Creates a new problem category from the given string identifier.
    /// 
    /// # Errors
    /// 
    /// Results in an error upon an unknown input.
    pub fn from_str(s: &str) -> Option<ProblemCategory> {
        match s {
            "crafted" => Some(ProblemCategory::Crafted),
            "random" => Some(ProblemCategory::Random),
            "industrial" => Some(ProblemCategory::Industrial),
            _ => None
        }
    }
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

impl ProblemStatus {
    /// Creates a new problem status from the given string identifier.
    /// 
    /// # Errors
    /// 
    /// Results in an error upon an unknown input.
    pub fn from_str(s: &str) -> Option<ProblemStatus> {
        match s {
            "sat" => Some(ProblemStatus::Sat),
            "unsat" => Some(ProblemStatus::Unsat),
            "unknown" => Some(ProblemStatus::Unknown),
            _ => None
        }
    }
}

/// Represents an info and its respective value when invoking the `set-info`
/// SMTLib2 command.
///
/// There are some predefined info kinds and their associated value type
/// as well as custom info kinds and their generic values.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InfoAndValue<'c, E> {
    /// Corresponds to the `:smt-lib-version` info flag and its decimal parameter.
    SMTLibVersion(Decimal<'c>),
    /// Corresponds to the `:source` info flag and its string or quoted symbol parameter.
    Source(&'c str),
    /// Corresponds to the `:license` info flag and its string parameter.
    License(&'c str),
    /// Corresponds to the `:category` info flag and its associated value.
    Category(ProblemCategory),
    /// Corresponds to the `:status` info flag and its associated value.
    Status(ProblemStatus),
    /// Corresponds to any non predefined info flag that might have a value.
    Other {
        /// The key of the custom info flag.
        key: &'c str,
        /// The optional value of the custom info flag.
        value: Option<E>,
    },
}
