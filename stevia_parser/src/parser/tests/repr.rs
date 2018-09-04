use parser::{
    self,
    Sign,
};
use solver::{
    self,
    ProblemCategory,
    ProblemStatus,
    Radix,
};

use std;

/// Testable dummy propositional literal.
///
/// This simply owns its data instead of borrowing
/// which makes it easier to test.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropLit {
    /// The name of the propositional literal.
    name: String,
    /// The sign of the propositional literal.
    sign: Sign,
}

impl<'c> From<parser::PropLit<'c>> for PropLit {
    fn from(prop_lit: parser::PropLit) -> Self {
        Self {
            name: prop_lit.name().to_owned(),
            sign: prop_lit.sign(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OptionKind {
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
    Custom { id: String },
}

impl OptionKind {
    pub fn custom<S>(id: S) -> Self
    where
        S: Into<String>,
    {
        OptionKind::Custom { id: id.into() }
    }
}

impl<'c> From<solver::OptionKind<'c>> for OptionKind {
    fn from(kind: solver::OptionKind<'c>) -> Self {
        use self::OptionKind::*;
        use solver::OptionKind as OptKind;
        match kind {
            OptKind::DiagnosticOutputChannel => DiagnosticOutputChannel,
            OptKind::GlobalDeclarations => GlobalDeclarations,
            OptKind::InteractiveMode => InteractiveMode,
            OptKind::PrintSuccess => PrintSuccess,
            OptKind::ProduceAssertions => ProduceAssertions,
            OptKind::ProduceAssignments => ProduceAssignments,
            OptKind::ProduceModels => ProduceModels,
            OptKind::ProduceProofs => ProduceProofs,
            OptKind::ProduceUnsatAssumptions => ProduceUnsatAssumptions,
            OptKind::ProduceUnsatCores => ProduceUnsatCores,
            OptKind::RandomSeed => RandomSeed,
            OptKind::RegularOutputChannel => RegularOutputChannel,
            OptKind::ReproducibleResourceLimit => ReproducibleResourceLimit,
            OptKind::Verbosity => Verbosity,
            OptKind::Custom(id) => OptionKind::custom(id),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GetInfoKind {
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
    Other(String)
}

impl GetInfoKind {
    pub fn other<S>(flag: S) -> Self
    where
        S: Into<String>,
    {
        GetInfoKind::Other(flag.into())
    }
}

impl<'c> From<solver::GetInfoKind<'c>> for GetInfoKind {
    fn from(kind: solver::GetInfoKind<'c>) -> Self {
        use self::GetInfoKind::*;
        use solver::GetInfoKind as Flag;
        match kind {
            Flag::AllStatistics => AllStatistics,
            Flag::AssertionStackLevels => AssertionStackLevels,
            Flag::Authors => Authors,
            Flag::ErrorBehaviour => ErrorBehaviour,
            Flag::Name => Name,
            Flag::ReasonUnknown => ReasonUnknown,
            Flag::Version => Version,
            Flag::Other(id) => GetInfoKind::other(id),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    /// A boolean literal.
    Bool(bool),
    /// A string literal.
    String(String),
    /// A simple or quoted symbol.
    ///
    /// # Note
    ///
    /// At this level of abstraction there is no distinction made
    /// between simply and quoted symbols of the SMTLib2 format.
    Symbol(String),
    /// A keyword.
    Keyword(String),
    /// A numeral literal.
    ///
    /// # Note
    ///
    /// The possible encodings for this are decimal, binary or hexadecimal.
    /// Binary starts with `#b`, hexadecimal starts with `#x` and decimal
    /// starts with any digit.
    Numeral(NumeralLit),
    /// A decimal literal.
    Decimal(DecimalLit),
}

impl Literal {
    pub fn numeral<N>(val: N) -> Self
    where
        N: Into<NumeralLit>,
    {
        Literal::Numeral(val.into())
    }

    pub fn decimal<D>(val: D) -> Self
    where
        D: Into<DecimalLit>,
    {
        Literal::Decimal(val.into())
    }

    pub fn string<S>(val: S) -> Self
    where
        S: Into<String>,
    {
        Literal::String(val.into())
    }

    pub fn symbol<S>(val: S) -> Self
    where
        S: Into<String>,
    {
        Literal::Symbol(val.into())
    }

    pub fn keyword<S>(keyword: S) -> Self
    where
        S: Into<String>,
    {
        let keyword = keyword.into();
        assert!(keyword.starts_with(":"));
        Literal::Keyword(keyword)
    }
}

impl<'c> From<solver::Literal<'c>> for Literal {
    fn from(lit: solver::Literal<'c>) -> Self {
        use solver::Literal::*;
        match lit {
            Bool(flag) => Literal::Bool(flag),
            String(content) => Literal::string(content),
            Symbol(name) => Literal::symbol(name),
            Keyword(id) => Literal::keyword(id),
            Numeral(lit) => Literal::numeral(lit),
            Decimal(lit) => Literal::decimal(lit),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NumeralLit {
    /// For numerals that fit within an `u128`.
    Small(u128),
    /// For numerals that do not fit within an `u128`.
    Large { radix: Radix, repr: String },
}

impl From<u8> for NumeralLit {
    fn from(val: u8) -> Self {
        NumeralLit::small(val as u128)
    }
}

impl From<u16> for NumeralLit {
    fn from(val: u16) -> Self {
        NumeralLit::small(val as u128)
    }
}

impl From<u32> for NumeralLit {
    fn from(val: u32) -> Self {
        NumeralLit::small(val as u128)
    }
}

impl From<u64> for NumeralLit {
    fn from(val: u64) -> Self {
        NumeralLit::small(val as u128)
    }
}

impl From<u128> for NumeralLit {
    fn from(val: u128) -> Self {
        NumeralLit::small(val)
    }
}

impl NumeralLit {
    fn small(val: u128) -> Self {
        NumeralLit::Small(val)
    }

    fn large<S>(radix: Radix, repr: S) -> Self
    where
        S: Into<String>,
    {
        NumeralLit::Large {
            radix,
            repr: repr.into(),
        }
    }
}

impl<'c> From<solver::NumeralLit<'c>> for NumeralLit {
    fn from(lit: solver::NumeralLit<'c>) -> Self {
        use either::Either;
        match lit.value() {
            Either::Left(val) => Self::small(val),
            Either::Right((repr, radix)) => Self::large(radix, repr),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecimalLit(String);

impl From<f32> for DecimalLit {
    fn from(val: f32) -> Self {
        DecimalLit(val.to_string())
    }
}

impl From<f64> for DecimalLit {
    fn from(val: f64) -> Self {
        DecimalLit(val.to_string())
    }
}

impl<'c> From<solver::DecimalLit<'c>> for DecimalLit {
    fn from(lit: solver::DecimalLit<'c>) -> Self {
        DecimalLit(lit.str_repr().to_owned())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum OutputChannelKind {
    /// Standard out.
    Stderr,
    /// Standard in.
    Stdout,
    /// Stream into the file at the given path.
    File(std::path::PathBuf),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OutputChannel {
    kind: OutputChannelKind,
}

impl<'c> From<solver::OutputChannel<'c>> for OutputChannel {
    fn from(ch: solver::OutputChannel<'c>) -> Self {
        use solver::OutputChannel::*;
        match ch {
            Stderr => OutputChannel::stderr(),
            Stdout => OutputChannel::stdout(),
            File(path) => OutputChannel::file(path),
        }
    }
}

impl OutputChannel {
    pub fn stderr() -> Self {
        OutputChannel {
            kind: OutputChannelKind::Stderr,
        }
    }

    pub fn stdout() -> Self {
        OutputChannel {
            kind: OutputChannelKind::Stdout,
        }
    }

    pub fn file<P>(path_buf: P) -> Self
    where
        P: Into<::std::path::PathBuf>,
    {
        OutputChannel {
            kind: OutputChannelKind::File(path_buf.into()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OptionAndValue {
    /// Corresponds to the `:diagnostic-output-channel` and its given output channel.
    DiagnosticOutputChannel(OutputChannel),
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
    RandomSeed(NumeralLit),
    /// Corresponds to the `:regular-output-channel` and its given output channel.
    RegularOutputChannel(OutputChannel),
    /// Corresponds to the `:reproducible-resource-limit` and its numeral parameter.
    ReproducibleResourceLimit(NumeralLit),
    /// Corresponds to the `:verbosity` and its numeral parameter.
    Verbosity(NumeralLit),
    /// Corresponds to non predefined option that has exactly one single value.
    SimpleCustom {
        /// The key of the simple custom command.
        key: String,
        /// The optional value of the simple custom command.
        value: Option<Literal>,
    },
    /// Corresponds to non predefined option that has a recursively defined value.
    ComplexCustom {
        /// The key of the complex custom command.
        key: String,
    },
}

impl OptionAndValue {
    pub fn custom<S, V>(key: S, value: V) -> Self
    where
        S: Into<String>,
        V: Into<Option<Literal>>,
    {
        OptionAndValue::SimpleCustom {
            key: key.into(),
            value: value.into(),
        }
    }
}

impl<'c> From<solver::OptionAndValue<'c>> for OptionAndValue {
    fn from(opt_and_val: solver::OptionAndValue<'c>) -> Self {
        use solver::OptionAndValue::*;
        match opt_and_val {
            DiagnosticOutputChannel(ch) => {
                OptionAndValue::DiagnosticOutputChannel(ch.into())
            },
            GlobalDeclarations(flag) => {
                OptionAndValue::GlobalDeclarations(flag)
            },
            InteractiveMode(flag) => {
                OptionAndValue::InteractiveMode(flag)
            },
            PrintSuccess(flag) => {
                OptionAndValue::PrintSuccess(flag)
            },
            ProduceAssertions(flag) => {
                OptionAndValue::ProduceAssertions(flag)
            },
            ProduceAssignments(flag) => {
                OptionAndValue::ProduceAssignments(flag)
            },
            ProduceModels(flag) => {
                OptionAndValue::ProduceModels(flag)
            },
            ProduceProofs(flag) => {
                OptionAndValue::ProduceProofs(flag)
            },
            ProduceUnsatAssumptions(flag) => {
                OptionAndValue::ProduceUnsatAssumptions(flag)
            },
            ProduceUnsatCores(flag) => {
                OptionAndValue::ProduceUnsatCores(flag)
            },
            RandomSeed(num_lit) => {
                OptionAndValue::RandomSeed(num_lit.into())
            },
            RegularOutputChannel(ch) => {
                OptionAndValue::RegularOutputChannel(ch.into())
            },
            ReproducibleResourceLimit(num_lit) => {
                OptionAndValue::ReproducibleResourceLimit(num_lit.into())
            },
            Verbosity(num_lit) => {
                OptionAndValue::Verbosity(num_lit.into())
            },
            SimpleCustom{key, value} => {
                OptionAndValue::SimpleCustom{
                    key: key.to_owned(),
                    value: value.map(Literal::from)
                }
            },
            ComplexCustom{.. /*key*/} => {
                unimplemented!()
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InfoAndValue {
    /// Corresponds to the `:smt-lib-version` info flag and its decimal parameter.
    SMTLibVersion(DecimalLit),
    /// Corresponds to the `:source` info flag and its string or quoted symbol parameter.
    Source(String),
    /// Corresponds to the `:license` info flag and its string parameter.
    License(String),
    /// Corresponds to the `:category` info flag and its associated value.
    Category(ProblemCategory),
    /// Corresponds to the `:status` info flag and its associated value.
    Status(ProblemStatus),
    /// Corresponds to any non predefined info flag that has exactly one value.
    SimpleCustom {
        /// The key of the custom info flag.
        key: String,
        /// The optional value of the custom info flag.
        value: Option<Literal>,
    },
    /// Corresponds to any non predefined info flag that has a potentially complex value.
    ComplexCustom {
        /// The key of the custom info flag.
        key: String,
    },
}

impl InfoAndValue {
    pub fn custom<S, V>(key: S, value: V) -> Self
    where
        S: Into<String>,
        V: Into<Option<Literal>>,
    {
        InfoAndValue::SimpleCustom {
            key: key.into(),
            value: value.into(),
        }
    }
}

impl<'c> From<solver::InfoAndValue<'c>> for InfoAndValue {
    fn from(info_and_val: solver::InfoAndValue<'c>) -> Self {
        use solver::InfoAndValue::*;
        match info_and_val {
            SMTLibVersion(ch) => InfoAndValue::SMTLibVersion(ch.into()),
            Source(content) => InfoAndValue::Source(content.to_owned()),
            License(content) => InfoAndValue::License(content.to_owned()),
            Category(category) => InfoAndValue::Category(category.into()),
            Status(status) => InfoAndValue::Status(status.into()),
            SimpleCustom { key, value } => InfoAndValue::SimpleCustom {
                key: key.to_owned(),
                value: value.map(Literal::from),
            },
            ComplexCustom { key } => InfoAndValue::ComplexCustom {
                key: key.to_owned(),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckSatAssumingEvent {
    prop_lits: Vec<PropLit>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclareSortEvent {
    symbol_name: String,
    arity: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ParseEventKind {
    CheckSat,
    CheckSatAssuming(CheckSatAssumingEvent),
    DeclareSort(DeclareSortEvent),
    Echo { content: String },
    Exit,
    GetAssertions,
    GetAssignment,
    GetInfo { info: GetInfoKind },
    GetModel,
    GetOption { option: OptionKind },
    GetProof,
    GetUnsatAssumptions,
    GetUnsatCore,
    Pop { levels: usize },
    Push { levels: usize },
    Reset,
    ResetAssertions,
    SetLogic { id: String },
    SetOption { option_and_value: OptionAndValue },
    SetInfo { info_and_value: InfoAndValue },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseEvent {
    kind: ParseEventKind
}

impl ParseEvent {
    fn new(kind: ParseEventKind) -> Self {
        ParseEvent{ kind }
    }

    pub fn check_sat() -> Self {
        ParseEvent::new(ParseEventKind::CheckSat)
    }

    pub fn exit() -> Self {
        ParseEvent::new(ParseEventKind::Exit)
    }

    pub fn get_assertions() -> Self {
        ParseEvent::new(ParseEventKind::GetAssertions)
    }

    pub fn get_assignment() -> Self {
        ParseEvent::new(ParseEventKind::GetAssignment)
    }

    pub fn get_model() -> Self {
        ParseEvent::new(ParseEventKind::GetModel)
    }

    pub fn get_proof() -> Self {
        ParseEvent::new(ParseEventKind::GetProof)
    }

    pub fn get_unsat_assumptions() -> Self {
        ParseEvent::new(ParseEventKind::GetUnsatAssumptions)
    }

    pub fn get_unsat_core() -> Self {
        ParseEvent::new(ParseEventKind::GetUnsatCore)
    }

    pub fn reset() -> Self {
        ParseEvent::new(ParseEventKind::Reset)
    }

    pub fn reset_assertions() -> Self {
        ParseEvent::new(ParseEventKind::ResetAssertions)
    }

    pub fn check_sat_assuming<L, P>(prop_lits: L) -> Self
    where
        L: IntoIterator<Item = P>,
        PropLit: From<P>,
    {
        CheckSatAssumingEvent {
            prop_lits: prop_lits.into_iter().map(PropLit::from).collect(),
        }.into()
    }

    pub fn declare_sort<S>(symbol_name: S, arity: usize) -> Self
    where
        S: Into<String>,
    {
        ParseEvent::new(ParseEventKind::DeclareSort(DeclareSortEvent {
            symbol_name: symbol_name.into(),
            arity,
        }))
    }

    pub fn echo<S>(content: S) -> Self
    where
        S: Into<String>,
    {
        ParseEvent::new(ParseEventKind::Echo {
            content: content.into(),
        })
    }

    pub fn get_info<V>(flag: V) -> Self
    where
        V: Into<GetInfoKind>
    {
        ParseEvent::new(ParseEventKind::GetInfo { info: flag.into() })
    }

    pub fn get_option<V>(kind: V) -> Self
    where
        V: Into<OptionKind>
    {
        ParseEvent::new(ParseEventKind::GetOption { option: kind.into() })
    }

    pub fn set_option<V>(option_and_value: V) -> Self
    where
        V: Into<OptionAndValue>
    {
        ParseEvent::new(ParseEventKind::SetOption { option_and_value: option_and_value.into() })
    }

    pub fn set_info<V>(info_and_value: V) -> Self
    where
        V: Into<InfoAndValue>
    {
        ParseEvent::new(ParseEventKind::SetInfo { info_and_value: info_and_value.into() })
    }

    pub fn push(levels: usize) -> Self {
        ParseEvent::new(ParseEventKind::Push { levels })
    }

    pub fn pop(levels: usize) -> Self {
        ParseEvent::new(ParseEventKind::Pop { levels })
    }

    pub fn set_logic<S>(id: S) -> Self
    where
        S: Into<String>,
    {
        ParseEvent::new(ParseEventKind::SetLogic { id: id.into() })
    }
}

impl From<CheckSatAssumingEvent> for ParseEvent {
    fn from(concrete: CheckSatAssumingEvent) -> Self {
        ParseEvent::new(ParseEventKind::CheckSatAssuming(concrete))
    }
}

impl From<DeclareSortEvent> for ParseEvent {
    fn from(concrete: DeclareSortEvent) -> Self {
        ParseEvent::new(ParseEventKind::DeclareSort(concrete))
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct DummySolver {
    events: Vec<ParseEvent>,
}

impl<'c> IntoIterator for DummySolver {
    type Item = ParseEvent;
    type IntoIter = <Vec<ParseEvent> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.events.into_iter()
    }
}

use parser::PropLitsIter;
use solver::{
    ResponseResult,
    SMTLib2Solver,
};

impl SMTLib2Solver for DummySolver {
    fn check_sat(&mut self) -> ResponseResult {
        self.events.push(ParseEvent::check_sat());
        Ok(())
    }

    fn check_sat_assuming(&mut self, prop_lits: PropLitsIter) -> ResponseResult {
        self.events.push(ParseEvent::check_sat_assuming(prop_lits));
        Ok(())
    }

    fn declare_sort(&mut self, symbol: &str, arity: usize) -> ResponseResult {
        self.events.push(ParseEvent::declare_sort(symbol, arity));
        Ok(())
    }

    fn echo(&mut self, content: &str) -> ResponseResult {
        self.events.push(ParseEvent::echo(content));
        Ok(())
    }

    fn exit(&mut self) -> ResponseResult {
        self.events.push(ParseEvent::exit());
        Ok(())
    }

    fn get_assertions(&mut self) -> ResponseResult {
        self.events.push(ParseEvent::get_assertions());
        Ok(())
    }

    fn get_assignment(&mut self) -> ResponseResult {
        self.events.push(ParseEvent::get_assignment());
        Ok(())
    }

    fn get_info(&mut self, flag: solver::GetInfoKind) -> ResponseResult {
        self.events.push(ParseEvent::get_info(flag));
        Ok(())
    }

    fn get_model(&mut self) -> ResponseResult {
        self.events.push(ParseEvent::get_model());
        Ok(())
    }

    fn get_option(&mut self, option: solver::OptionKind) -> ResponseResult {
        self.events.push(ParseEvent::get_option(option));
        Ok(())
    }

    fn get_proof(&mut self) -> ResponseResult {
        self.events.push(ParseEvent::get_proof());
        Ok(())
    }

    fn get_unsat_assumptions(&mut self) -> ResponseResult {
        self.events.push(ParseEvent::get_unsat_assumptions());
        Ok(())
    }

    fn get_unsat_core(&mut self) -> ResponseResult {
        self.events.push(ParseEvent::get_unsat_core());
        Ok(())
    }

    fn pop(&mut self, levels: usize) -> ResponseResult {
        self.events.push(ParseEvent::pop(levels));
        Ok(())
    }

    fn push(&mut self, levels: usize) -> ResponseResult {
        self.events.push(ParseEvent::push(levels));
        Ok(())
    }

    fn reset(&mut self) -> ResponseResult {
        self.events.push(ParseEvent::reset());
        Ok(())
    }

    fn reset_assertions(&mut self) -> ResponseResult {
        self.events.push(ParseEvent::reset_assertions());
        Ok(())
    }

    fn set_logic(&mut self, id: &str) -> ResponseResult {
        self.events.push(ParseEvent::set_logic(id));
        Ok(())
    }

    fn set_option(&mut self, option_and_value: solver::OptionAndValue) -> ResponseResult {
        self.events.push(ParseEvent::set_option(option_and_value));
        Ok(())
    }

    fn set_info(&mut self, info_and_value: solver::InfoAndValue) -> ResponseResult {
        self.events.push(ParseEvent::set_info(info_and_value));
        Ok(())
    }
}
