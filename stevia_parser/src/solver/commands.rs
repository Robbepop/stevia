use parser::PropLitsIter;
use solver::repr::{
    InfoAndValue,
    OptionAndValue,
    OptionKind,
    GetInfoKind,
};
use solver::{
    Command,
    ResponseError,
    ResponseResult,
};

/// This is the SMT solver interface with which the parser will
/// interactively communicate upon parsing the input stream.
///
/// SMTLib2 conformant SMT solver simply have to implement a viable
/// sub set of this trait and be done. Nothing else is required in order
/// to support the SMTLib2 format using this library for the SMT solver.
///
/// All commands have default implementations to indicate that they are
/// unsupported by the SMT solver. So SMT solver implementors should only
/// implement the trait methods they actually support.
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

    /// Corresponds to the `check-sat` command.
    fn check_sat(&mut self) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::CheckSat))
    }

    /// Corresponds to the `check-sat-assuming` command.
    fn check_sat_assuming(&mut self, _prop_lits: PropLitsIter) -> ResponseResult {
        Err(ResponseError::unsupported_command(
            Command::CheckSatAssuming,
        ))
    }

    /// Corresponds to the `declare-sort` command.
    fn declare_sort(&mut self, _symbol: &str, _arity: usize) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::DeclareSort))
    }

    /// Corresponds to the `echo` command.
    fn echo(&mut self, _content: &str) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::Echo))
    }

    /// Corresponds to the `exit` command.
    fn exit(&mut self) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::Exit))
    }

    /// Corresponds to the `get-assertions` command.
    fn get_assertions(&mut self) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::GetAssertions))
    }

    /// Corresponds to the `get-assignment` command.
    fn get_assignment(&mut self) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::GetAssignment))
    }

    /// Corresponds to the `get-info` command.
    fn get_info(&mut self, _info: GetInfoKind) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::GetInfo))
    }

    /// Corresponds to the `get-model` command.
    fn get_model(&mut self) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::GetModel))
    }

    /// Corresponds to the `get-option` command.
    fn get_option(&mut self, _option: OptionKind) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::GetOption))
    }

    /// Corresponds to the `get-proof` command.
    fn get_proof(&mut self) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::GetProof))
    }

    /// Corresponds to the `get-unsat-assumptions` command.
    fn get_unsat_assumptions(&mut self) -> ResponseResult {
        Err(ResponseError::unsupported_command(
            Command::GetUnsatAssumptions,
        ))
    }

    /// Corresponds to the `get-unsat-core` command.
    fn get_unsat_core(&mut self) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::GetUnsatCore))
    }

    /// Corresponds to the `pop` command.
    fn pop(&mut self, _levels: usize) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::Pop))
    }

    /// Corresponds to the `push` command.
    fn push(&mut self, _levels: usize) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::Push))
    }

    /// Corresponds to the `reset` command.
    fn reset(&mut self) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::Reset))
    }

    /// Corresponds to the `reset-assertions` command.
    fn reset_assertions(&mut self) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::ResetAssertions))
    }

    /// Corresponds to the `set-logic` command.
    fn set_logic(&mut self, _symbol: &str) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::SetLogic))
    }

    /// Corresponds to the `set-option` command.
    fn set_option(&mut self, _option: OptionAndValue) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::SetOption))
    }

    /// Corresponds to the `set-info` command.
    fn set_info(&mut self, _info: InfoAndValue) -> ResponseResult {
        Err(ResponseError::unsupported_command(Command::SetInfo))
    }
}
