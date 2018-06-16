use parser::PropLitsIter;

use std;

/// The response from the SMT solver back to the parser.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ResponseError {
    Unsupported,
    UnexpectedCommand,
    InvalidState
}

pub type ResponseResult = std::result::Result<(), ResponseError>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum OptionKindBase<S> {
    DiagnosticOutputChannel,
    GlobalDeclarations,
    InteractiveMode,
    PrintSuccess,
    ProduceAssertions,
    ProduceAssignments,
    ProduceModels,
    ProduceProofs,
    ProduceUnsatAssumptions,
    ProduceUnsatCores,
    RandomSeed,
    RegularOutputChannel,
    ReproducibleResourceLimit,
    Verbosity,
    Custom(S)
}
pub type OptionKind<'c> = OptionKindBase<&'c str>;

impl<S> OptionKindBase<S> {
    pub fn has_bool_param(self) -> bool {
        use self::OptionKindBase::*;
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
            _ => false
        }
    }

    pub fn has_output_channel_param(self) -> bool {
        use self::OptionKindBase::*;
        match self {
            | DiagnosticOutputChannel
            | RegularOutputChannel => true,
            _ => false
        }
    }

    pub fn has_numeral_param(self) -> bool {
        use self::OptionKindBase::*;
        match self {
            | RandomSeed
            | ReproducibleResourceLimit
            | Verbosity => true,
            _ => false
        }
    }
}

impl<'c> From<&'c str> for OptionKind<'c> {
    fn from(repr: &'c str) -> Self {
        use self::OptionKindBase::*;
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
pub enum LiteralBase<S> {
    Bool(bool),
    String(S),
    Symbol(S),
    Numeral(NumeralLitBase<S>),
    Keyword(S),
    Decimal(DecimalLitBase<S>)
}
pub type Literal<'c> = LiteralBase<&'c str>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct NumeralLitBase<S> {
    pub(crate) repr: S
}
pub type NumeralLit<'c> = NumeralLitBase<&'c str>;
impl<S> NumeralLitBase<S> {
    pub fn into_repr(self) -> S {
        self.repr
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct DecimalLitBase<S> {
    pub(crate) repr: S
}
pub type DecimalLit<'c> = DecimalLitBase<&'c str>;
impl<S> DecimalLitBase<S> {
    pub fn into_repr(self) -> S {
        self.repr
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum OutputChannelBase<P> {
    Stderr,
    Stdout,
    File(P)
}
pub type OutputChannel<'c> = OutputChannelBase<&'c std::path::Path>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum OptionAndValueBase<S, P> {
    DiagnosticOutputChannel(OutputChannelBase<P>),
    GlobalDeclarations(bool),
    InteractiveMode(bool),
    PrintSuccess(bool),
    ProduceAssertions(bool),
    ProduceAssignments(bool),
    ProduceModels(bool),
    ProduceProofs(bool),
    ProduceUnsatAssumptions(bool),
    ProduceUnsatCores(bool),
    RandomSeed(NumeralLitBase<S>),
    RegularOutputChannel(OutputChannelBase<P>),
    ReproducibleResourceLimit(NumeralLitBase<S>),
    Verbosity(NumeralLitBase<S>),
    SimpleCustom{
        key: S,
        value: Option<LiteralBase<S>>
    },
    ComplexCustom{
        key: S
    }
}
pub type OptionAndValue<'c> = OptionAndValueBase<&'c str, &'c std::path::Path>;

pub enum VarSizeCommand {
    Assert,
    DeclareConst,
    DeclareDatatype,
    DeclareDatatypes,
    DeclareFun,
    DefineFun,
    DefineFunRec,
    DefineFunsRec,
    DefineSort,
    GetValue,
    SetInfo,
    SetOption
}

fn end(command: VarSizeCommand) {}

pub trait SMTLib2Solver {
    // Variable-size commands:
    // 
    // We still need a proper design for those commands.
    //
    // (assert <term>)
    //
    // (declare-const <symbol> <sort>)
    // (declare-datatype <symbol> <datatype_dec>)
    // (declare-datatypes (<sort_dec>^(n+1)) (<datatype_dec>^(n+1)))
    // (declare-fun <symbol> (<sort>*) <sort>)
    //
    // (define-fun <function_def>)
    // (define-fun-rec <function_def>)
    // (define-funs-rec (<function_def>^(n+1)) (<term>^(n+1)))
    // (define-sort <symbol> (<symbol>*) <sort>)
    //
    // (get-value (<term>+))
    //
    // (set-info <attribute>)
    // (set-option <option>)
    //
    //
    // At QPR we use a SAX (Simple API XML) parser with the following interface:
    //
    // fn OnStartDocument();
    // fn OnEndDocument();
    // fn OnStartElement(name: &str, attributes: Iterator<(String, String)>);
    // fn OnEndElement(name: &str);
    // fn OnCharacters(value: &str);
    //
    // fn beginAssert() {} // missing all rest
    // fn beginDeclareConst(id: &str) {} // missing `sort`
    // fn beginDeclareDatatype(id: &str) {} // missing `datatype_dec`
    // fn beginDeclareDatatypes() {} // missing all rest
    // fn beginDeclareFun(name: &str) {} // missing params and return sort
    // fn beginDefineFun(name: &str) {} // missing function definition
    // fn beginDefineFunRec(name: &str) {} // missing function definition
    // fn beginDefineFunsRec() {} // missing all rest
    // fn beginDefineSort(name: &str) {} // missing all rest
    // fn beginGetValue() {} // missing terms
    //

    fn check_sat(&mut self) -> ResponseResult {
        Err(ResponseError::Unsupported)
    }

    fn check_sat_assuming(&mut self, _prop_lits: PropLitsIter) -> ResponseResult {
        Ok(())
    }

    fn declare_sort(&mut self, _symbol: &str, _arity: usize) -> ResponseResult {
        Ok(())
    }

    fn echo(&mut self, _content: &str) -> ResponseResult {
        Ok(())
    }

    fn exit(&mut self) -> ResponseResult {
        Ok(())
    }

    fn get_assertions(&mut self) -> ResponseResult {
        Ok(())
    }

    fn get_assignment(&mut self) -> ResponseResult {
        Ok(())
    }

    fn get_info(&mut self, _info: &str) -> ResponseResult {
        Ok(())
    }

    fn get_model(&mut self) -> ResponseResult {
        Ok(())
    }

    fn get_option(&mut self, _option: OptionKind) -> ResponseResult {
        Ok(())
    }

    fn get_proof(&mut self) -> ResponseResult {
        Ok(())
    }

    fn get_unsat_assumptions(&mut self) -> ResponseResult {
        Ok(())
    }

    fn get_unsat_core(&mut self) -> ResponseResult {
        Ok(())
    }

    fn pop(&mut self, _levels: usize) -> ResponseResult {
        Ok(())
    }

    fn push(&mut self, _levels: usize) -> ResponseResult {
        Ok(())
    }

    fn reset(&mut self) -> ResponseResult {
        Ok(())
    }

    fn reset_assertions(&mut self) -> ResponseResult {
        Ok(())
    }

    fn set_logic(&mut self, _symbol: &str) -> ResponseResult {
        Ok(())
    }

    fn set_option(&mut self, _option: OptionAndValue) -> ResponseResult {
        Ok(())
    }
}
