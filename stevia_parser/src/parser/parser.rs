use commands::SMTLib2Solver;
use lexer::{smtlib2_tokens, Command, Token, TokenIter, TokenKind};
use parser::error::{ParseError, ParseResult};

pub fn parse_smtlib2<S>(input: &str, solver: &mut S) -> ParseResult<()>
where
    S: SMTLib2Solver,
{
    Parser::new(input, solver).parse_script()
}

#[derive(Debug)]
pub struct Parser<'c, 's, S: 's> {
    token_iter: TokenIter<'c>,
    peek: Option<Token>,
    solver: &'s mut S,
}

impl<'c, 's, S> Parser<'c, 's, S>
where
    S: SMTLib2Solver,
{
    pub(self) fn new(input: &'c str, solver: &'s mut S) -> Self {
        Self {
            token_iter: smtlib2_tokens(input),
            peek: None,
            solver,
        }
    }

    fn peek(&mut self) -> ParseResult<Token> {
        if let Some(tok) = self.peek {
            return Ok(tok);
        }
        let tok = self.token_iter.next_token()?;
        self.peek = Some(tok);
        Ok(tok)
    }

    fn consume(&mut self) {
        debug_assert!(self.peek.is_some());
        self.peek = None;
    }

    fn unexpected_token_kind<T>(&mut self, found_kind: TokenKind, expected_kind: T) -> ParseError
    where
        T: Into<Option<TokenKind>>,
    {
        ParseError::unexpected_token_kind(found_kind, expected_kind)
    }

    fn expect_tok_kind(&mut self, kind: TokenKind) -> ParseResult<Token> {
        let peek = self.peek()?;
        if peek.kind() != kind {
            return Err(self.unexpected_token_kind(peek.kind(), kind));
        }
        self.consume();
        Ok(peek)
    }

    fn expect_command_tok(&mut self) -> ParseResult<Command> {
        match self.peek()?.kind() {
            TokenKind::Command(command) => {
                self.consume();
                Ok(command)
            }
            _ => Err(unimplemented!()),
        }
    }

    fn parse_command(&mut self) -> ParseResult<()> {
        self.expect_tok_kind(TokenKind::OpenParen)?;
        let command = self.expect_command_tok()?;
        self.expect_tok_kind(TokenKind::CloseParen)?;
        match command {
            Command::CheckSat => {
                self.solver.check_sat();
            }
            _ => unimplemented!(),
        }
        Ok(())
    }

    pub fn parse_script(&mut self) -> ParseResult<()> {
        while let Ok(_) = self.peek() {
            self.parse_command()?
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use commands::{ParserResponse, InfoKind, OptionKind};

    #[derive(Debug, Clone, PartialEq, Eq)]
    enum ParseEvent<'c> {
        CheckSat,
        DeclareSort{
            symbol: &'c str,
            arity: usize
        },
        Echo{
            content: &'c str
        },
        Exit,
        GetAssertions,
        GetAssignment,
        GetInfo{
            info: InfoKind
        },
        GetModel,
        GetOption{
            option: OptionKind
        },
        GetProof,
        GetUnsatAssumptions,
        GetUnsatCore,
        Pop{
            levels: usize
        },
        Push{
            levels: usize
        },
        Reset,
        ResetAssertions,
        SetLogic{
            symbol: &'c str
        }
    }

    #[derive(Debug, Default, Clone)]
    struct DummySolver<'c> {
        events: Vec<ParseEvent<'c>>,
    }

    impl<'c> IntoIterator for DummySolver<'c> {
        type Item = ParseEvent<'c>;
        type IntoIter = <Vec<ParseEvent<'c>> as IntoIterator>::IntoIter;

        fn into_iter(self) -> Self::IntoIter {
            self.events.into_iter()
        }
    }

    impl<'c> SMTLib2Solver for DummySolver<'c> {
        fn check_sat(&mut self) -> ParserResponse {
            self.events.push(ParseEvent::CheckSat);
            ParserResponse::Success
        }

        fn declare_sort(&mut self, _symbol: &str, _arity: usize) -> ParserResponse {
            ParserResponse::Success
        }

        fn echo(&mut self, _content: &str) -> ParserResponse {
            ParserResponse::Success
        }

        fn exit(&mut self) -> ParserResponse {
            ParserResponse::Success
        }

        fn get_assertions(&mut self) -> ParserResponse {
            ParserResponse::Success
        }

        fn get_assignment(&mut self) -> ParserResponse {
            ParserResponse::Success
        }

        fn get_info(&mut self, _info: InfoKind) -> ParserResponse {
            ParserResponse::Success
        }

        fn get_model(&mut self) -> ParserResponse {
            ParserResponse::Success
        }

        fn get_option(&mut self, _option: OptionKind) -> ParserResponse {
            ParserResponse::Success
        }

        fn get_proof(&mut self) -> ParserResponse {
            ParserResponse::Success
        }

        fn get_unsat_assumptions(&mut self) -> ParserResponse {
            ParserResponse::Success
        }

        fn get_unsat_core(&mut self) -> ParserResponse {
            ParserResponse::Success
        }

        fn pop(&mut self, _levels: usize) -> ParserResponse {
            ParserResponse::Success
        }

        fn push(&mut self, _levels: usize) -> ParserResponse {
            ParserResponse::Success
        }

        fn reset(&mut self) -> ParserResponse {
            ParserResponse::Success
        }

        fn reset_assertions(&mut self) -> ParserResponse {
            ParserResponse::Success
        }

        fn set_logic(&mut self, _symbol: &str) -> ParserResponse {
            ParserResponse::Success
        }
    }

    fn assert_parse_valid_smtlib2(input: &str, expected_events: Vec<ParseEvent>) {
        let mut dummy_solver = DummySolver::default();
        parse_smtlib2(input, &mut dummy_solver).unwrap();
        for (actual, expected) in dummy_solver.into_iter().zip(expected_events.into_iter()) {
            assert_eq!(actual, expected)
        }
    }

    #[test]
    fn simple() {
        assert_parse_valid_smtlib2("(check-sat)", vec![ParseEvent::CheckSat]);
    }
}
