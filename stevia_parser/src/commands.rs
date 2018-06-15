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

    fn get_option(&mut self, _option: &str) -> ResponseResult {
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

    }
}
