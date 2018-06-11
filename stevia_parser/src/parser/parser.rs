use commands::{ParserResponse, SMTLib2Solver};
use lexer::{smtlib2_tokens, Command, Span, Token, TokenIter, TokenKind};
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
    input_str: ParseContent<'c>,
    peek: Option<Token>,
    solver: &'s mut S,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ParseContent<'c> {
    content: &'c str,
}

impl<'c> From<&'c str> for ParseContent<'c> {
    fn from(content: &'c str) -> Self {
        Self { content }
    }
}

impl<'c> ParseContent<'c> {
    pub fn span_to_str(&self, span: Span) -> Option<&str> {
        debug_assert!(self.content.as_bytes().len() >= 1);

        let content_bytes = self.content.as_bytes();
        let begin_offset = span.begin.to_usize();
        let end_offset = span.end.to_usize();
        if begin_offset >= content_bytes.len() {
            return None;
        }
        if end_offset >= content_bytes.len() {
            return None;
        }
        Some(&self.content[span.begin.to_usize()..span.end.to_usize() + 1])
    }

    pub fn span_to_str_unchecked(&self, span: Span) -> &str {
        debug_assert!(self.content.as_bytes().len() >= 1);
        debug_assert!(span.begin.to_usize() < self.content.as_bytes().len());
        debug_assert!(span.end.to_usize() < self.content.as_bytes().len());
        unsafe {
            self.content
                .slice_unchecked(span.begin.to_usize(), span.end.to_usize() + 1)
        }
    }
}

impl<'c, 's, S> Parser<'c, 's, S>
where
    S: SMTLib2Solver,
{
    pub(self) fn new(input: &'c str, solver: &'s mut S) -> Self {
        Self {
            token_iter: smtlib2_tokens(input),
            input_str: ParseContent::from(input),
            peek: None,
            solver,
        }
    }

    fn pull(&mut self) -> ParseResult<Token> {
        let tok = self.token_iter.next_token()?;
        if !tok.kind().has_semantic_meaning() {
            return self.pull();
        }
        self.peek = Some(tok);
        Ok(tok)
    }

    fn peek(&mut self) -> ParseResult<Token> {
        if let Some(tok) = self.peek {
            return Ok(tok);
        }
        self.pull()
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

    fn parse_simple_command<C>(&mut self, _kind: Command, command: C) -> ParseResult<()>
    where
        C: Fn(&mut S) -> ParserResponse,
    {
        debug_assert!(self.peek().is_ok());
        debug_assert_eq!(self.peek().unwrap().kind(), TokenKind::CloseParen);

        self.expect_tok_kind(TokenKind::CloseParen)?;
        command(self.solver);
        Ok(())
    }

    fn parse_command(&mut self) -> ParseResult<()> {
        self.expect_tok_kind(TokenKind::OpenParen)?;
        let command = self.expect_command_tok()?;
        use self::Command::*;
        #[cfg_attr(rustfmt, rustfmt_skip)]
        match command {
            CheckSat            => self.parse_simple_command(CheckSat, S::check_sat),
            Exit                => self.parse_simple_command(Exit, S::exit),
            GetAssertions       => self.parse_simple_command(GetAssertions, S::get_assertions),
            GetAssignment       => self.parse_simple_command(GetAssignment, S::get_assignment),
            GetModel            => self.parse_simple_command(GetModel, S::get_model),
            GetProof            => self.parse_simple_command(GetProof, S::get_proof),
            GetUnsatAssumptions => self.parse_simple_command(GetUnsatAssumptions, S::get_unsat_assumptions),
            GetUnsatCore        => self.parse_simple_command(GetUnsatCore, S::get_unsat_core),
            Reset               => self.parse_simple_command(Reset, S::reset),
            ResetAssertions     => self.parse_simple_command(ResetAssertions, S::reset_assertions),
            _ => unimplemented!(),
        }
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
    use commands::{InfoKind, OptionKind, ParserResponse};

    #[derive(Debug, Clone, PartialEq, Eq)]
    enum ParseEvent {
        CheckSat,
        DeclareSort { symbol: String, arity: usize },
        Echo { content: String },
        Exit,
        GetAssertions,
        GetAssignment,
        GetInfo { info: InfoKind },
        GetModel,
        GetOption { option: OptionKind },
        GetProof,
        GetUnsatAssumptions,
        GetUnsatCore,
        Pop { levels: usize },
        Push { levels: usize },
        Reset,
        ResetAssertions,
        SetLogic { symbol: String },
    }

    #[derive(Debug, Default, Clone)]
    struct DummySolver {
        events: Vec<ParseEvent>,
    }

    impl IntoIterator for DummySolver {
        type Item = ParseEvent;
        type IntoIter = <Vec<ParseEvent> as IntoIterator>::IntoIter;

        fn into_iter(self) -> Self::IntoIter {
            self.events.into_iter()
        }
    }

    impl SMTLib2Solver for DummySolver {
        fn check_sat(&mut self) -> ParserResponse {
            self.events.push(ParseEvent::CheckSat);
            ParserResponse::Success
        }

        fn declare_sort(&mut self, symbol: &str, arity: usize) -> ParserResponse {
            self.events.push(ParseEvent::DeclareSort{ symbol: symbol.to_owned(), arity });
            ParserResponse::Success
        }

        fn echo(&mut self, _content: &str) -> ParserResponse {
            ParserResponse::Success
        }

        fn exit(&mut self) -> ParserResponse {
            self.events.push(ParseEvent::Exit);
            ParserResponse::Success
        }

        fn get_assertions(&mut self) -> ParserResponse {
            self.events.push(ParseEvent::GetAssertions);
            ParserResponse::Success
        }

        fn get_assignment(&mut self) -> ParserResponse {
            self.events.push(ParseEvent::GetAssignment);
            ParserResponse::Success
        }

        fn get_info(&mut self, _info: InfoKind) -> ParserResponse {
            ParserResponse::Success
        }

        fn get_model(&mut self) -> ParserResponse {
            self.events.push(ParseEvent::GetModel);
            ParserResponse::Success
        }

        fn get_option(&mut self, _option: OptionKind) -> ParserResponse {
            ParserResponse::Success
        }

        fn get_proof(&mut self) -> ParserResponse {
            self.events.push(ParseEvent::GetProof);
            ParserResponse::Success
        }

        fn get_unsat_assumptions(&mut self) -> ParserResponse {
            self.events.push(ParseEvent::GetUnsatAssumptions);
            ParserResponse::Success
        }

        fn get_unsat_core(&mut self) -> ParserResponse {
            self.events.push(ParseEvent::GetUnsatCore);
            ParserResponse::Success
        }

        fn pop(&mut self, _levels: usize) -> ParserResponse {
            ParserResponse::Success
        }

        fn push(&mut self, _levels: usize) -> ParserResponse {
            ParserResponse::Success
        }

        fn reset(&mut self) -> ParserResponse {
            self.events.push(ParseEvent::Reset);
            ParserResponse::Success
        }

        fn reset_assertions(&mut self) -> ParserResponse {
            self.events.push(ParseEvent::ResetAssertions);
            ParserResponse::Success
        }

        fn set_logic(&mut self, _symbol: &str) -> ParserResponse {
            ParserResponse::Success
        }
    }

    fn assert_parse_valid_smtlib2(input: &str, expected_events: Vec<ParseEvent>) {
        let mut dummy_solver = DummySolver::default();
        parse_smtlib2(input, &mut dummy_solver).unwrap();
        let actual_events = dummy_solver.into_iter().collect::<Vec<_>>();
        assert_eq!(actual_events.len(), expected_events.len());
        for (actual, expected) in actual_events.into_iter().zip(expected_events.into_iter()) {
            assert_eq!(actual, expected)
        }
    }

    mod commands {
        use super::*;

        #[test]
        fn simple() {
            assert_parse_valid_smtlib2("(check-sat)", vec![ParseEvent::CheckSat]);
            assert_parse_valid_smtlib2("(exit)", vec![ParseEvent::Exit]);
            assert_parse_valid_smtlib2("(get-assertions)", vec![ParseEvent::GetAssertions]);
            assert_parse_valid_smtlib2("(get-assignment)", vec![ParseEvent::GetAssignment]);
            assert_parse_valid_smtlib2("(get-model)", vec![ParseEvent::GetModel]);
            assert_parse_valid_smtlib2("(get-proof)", vec![ParseEvent::GetProof]);
            assert_parse_valid_smtlib2(
                "(get-unsat-assumptions)",
                vec![ParseEvent::GetUnsatAssumptions],
            );
            assert_parse_valid_smtlib2("(get-unsat-core)", vec![ParseEvent::GetUnsatCore]);
            assert_parse_valid_smtlib2("(reset)", vec![ParseEvent::Reset]);
            assert_parse_valid_smtlib2("(reset-assertions)", vec![ParseEvent::ResetAssertions]);
        }

        #[test]
        fn simple_chain() {
            assert_parse_valid_smtlib2(
                indoc!(
                    "(check-sat)
                     (exit)
                     (get-assertions)
                     (get-assignment)
                     (get-model)
                     (get-proof)
                     (get-unsat-assumptions)
                     (get-unsat-core)
                     (reset)
                     (reset-assertions)"
                ),
                vec![
                    ParseEvent::CheckSat,
                    ParseEvent::Exit,
                    ParseEvent::GetAssertions,
                    ParseEvent::GetAssignment,
                    ParseEvent::GetModel,
                    ParseEvent::GetProof,
                    ParseEvent::GetUnsatAssumptions,
                    ParseEvent::GetUnsatCore,
                    ParseEvent::Reset,
                    ParseEvent::ResetAssertions,
                ],
            );
        }
    }
}
