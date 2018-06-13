use parser::PropLitsIter;

/// The response from the SMT solver back to the parser.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ParserResponse {
    Success,
    Unsupported,
    UnexpectedCommand
}

pub trait SMTLib2Solver {
    // Variable-size commands:
    // 
    // We still need a proper design for those commands.
    //
    // (assert <term>)
    // (check-sat-assuming (<prop_literal>*))
    // (declare-const <symbol> <sort>)
    // (declare-datatype <symbol> <datatype_dec>)
    // (declare-datatypes (<sort_dec>^(n+1)) (<datatype_dec>^(n+1)))
    // (declare-fun <symbol> (<sort>*) <sort>)
    // (define-fun <function_def>)
    // (define-fun-rec <function_def>)
    // (define-funs-rec (<function_def>^(n+1)) (<term>^(n+1)))
    // (define-sort <symbol> (<symbol>*) <sort>)
    // (get-value (<term>+))
    // (set-info <attribute>)
    // (set-option <option>)

    fn check_sat(&mut self) -> ParserResponse {
        ParserResponse::Unsupported
    }

    fn check_sat_assuming(&mut self, _prop_lits: PropLitsIter) -> ParserResponse {
        ParserResponse::Unsupported
    }

    fn declare_sort(&mut self, _symbol: &str, _arity: usize) -> ParserResponse {
        ParserResponse::Unsupported
    }

    fn echo(&mut self, _content: &str) -> ParserResponse {
        ParserResponse::Unsupported
    }

    fn exit(&mut self) -> ParserResponse {
        ParserResponse::Unsupported
    }

    fn get_assertions(&mut self) -> ParserResponse {
        ParserResponse::Unsupported
    }

    fn get_assignment(&mut self) -> ParserResponse {
        ParserResponse::Unsupported
    }

    fn get_info(&mut self, _info: &str) -> ParserResponse {
        ParserResponse::Unsupported
    }

    fn get_model(&mut self) -> ParserResponse {
        ParserResponse::Unsupported
    }

    fn get_option(&mut self, _option: &str) -> ParserResponse {
        ParserResponse::Unsupported
    }

    fn get_proof(&mut self) -> ParserResponse {
        ParserResponse::Unsupported
    }

    fn get_unsat_assumptions(&mut self) -> ParserResponse {
        ParserResponse::Unsupported
    }

    fn get_unsat_core(&mut self) -> ParserResponse {
        ParserResponse::Unsupported
    }

    fn pop(&mut self, _levels: usize) -> ParserResponse {
        ParserResponse::Unsupported
    }

    fn push(&mut self, _levels: usize) -> ParserResponse {
        ParserResponse::Unsupported
    }

    fn reset(&mut self) -> ParserResponse {
        ParserResponse::Unsupported
    }

    fn reset_assertions(&mut self) -> ParserResponse {
        ParserResponse::Unsupported
    }

    fn set_logic(&mut self, _symbol: &str) -> ParserResponse {
        ParserResponse::Unsupported
    }
}
