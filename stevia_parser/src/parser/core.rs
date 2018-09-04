use lexer::{
    scan_smtlib2,
    Span,
    Token,
    TokenIter,
    TokenKind,
};
use parser::{
    ParseError,
    ParseResult,
};
use solver::{
    Command,
    CommandResponseResult,
    DecimalLit,
    GetInfoKind,
    InfoAndValue,
    Literal,
    NumeralLit,
    OptionAndValue,
    OptionKind,
    OutputChannel,
    ProblemCategory,
    ProblemStatus,
    ResponseResult,
    SMTLib2Solver,
};

pub fn parse_smtlib2<S>(input: &str, solver: &mut S) -> ParseResult<()>
where
    S: SMTLib2Solver,
{
    ParserDriver {
        parser: Parser::new(input),
        solver,
    }.parse_script()
}

#[derive(Debug, Clone)]
pub struct Parser<'c> {
    token_iter: TokenIter<'c>,
    input_str: ParseContent<'c>,
    peek: Option<Token>,
}

pub struct ParserDriver<'c, 's, S>
where
    S: 's,
{
    parser: Parser<'c>,
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
    pub fn span_to_str(&self, span: Span) -> Option<&'c str> {
        debug_assert!(!self.content.as_bytes().is_empty());

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

    pub fn span_to_str_unchecked(&self, span: Span) -> &'c str {
        debug_assert!(!self.content.as_bytes().is_empty());
        debug_assert!(span.begin.to_usize() < self.content.as_bytes().len());
        debug_assert!(span.end.to_usize() < self.content.as_bytes().len());
        unsafe {
            self.content
                .get_unchecked(span.begin.to_usize()..span.end.to_usize() + 1)
        }
    }
}

impl<'c> Parser<'c> {
    pub(self) fn new(input: &'c str) -> Self {
        Self {
            token_iter: scan_smtlib2(input),
            input_str: ParseContent::from(input),
            peek: None,
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
            _ => unimplemented!(), // error: unexpected non-command token
        }
    }

    fn expect_usize_numeral(&mut self) -> ParseResult<usize> {
        debug_assert!(self.peek().is_ok());

        let numeral_tok = self.expect_tok_kind(TokenKind::Numeral)?;
        let numeric = self
            .input_str
            .span_to_str_unchecked(numeral_tok.span())
            .parse()
            .unwrap(); // TODO: better error handling here
        Ok(numeric)
    }

    fn expect_symbol_tok(&mut self) -> ParseResult<&'c str> {
        let sym = self.expect_tok_kind(TokenKind::Symbol)?;
        let sym_str = self.input_str.span_to_str_unchecked(sym.span());
        Ok(sym_str)
    }

    fn expect_symbol_matching_pred<P>(&mut self, pred: P) -> ParseResult<&'c str>
    where
        P: Fn(&str) -> bool,
    {
        let symbol_str = self.expect_symbol_tok()?;
        if !pred(symbol_str) {
            /* return */
            unimplemented!();
        }
        Ok(symbol_str)
    }

    fn expect_symbol_matching_str(&mut self, match_str: &str) -> ParseResult<()> {
        self.expect_symbol_matching_pred(|s| s == match_str)
            .map(|_| ())
    }
}

impl<'c, 's, S> ParserDriver<'c, 's, S>
where
    S: SMTLib2Solver + 's,
{
    fn parse_simple_command<C>(&mut self, kind: Command, command: C) -> ParseResult<()>
    where
        C: Fn(&mut S) -> ResponseResult,
    {
        debug_assert!(self.parser.peek().is_ok());

        self.parser.expect_tok_kind(TokenKind::CloseParen)?;
        command(self.solver).map_err(|err| err.invoked_by(kind))?;
        Ok(())
    }

    fn parse_declare_sort_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let symbol = self.parser.expect_tok_kind(TokenKind::Symbol)?;
        let arity = self.parser.expect_usize_numeral()?;
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        let symbol_str = self.parser.input_str.span_to_str_unchecked(symbol.span());

        self.solver
            .declare_sort(symbol_str, arity)
            .map_err(|err| err.invoked_by(Command::DeclareSort))?;
        Ok(())
    }

    fn parse_echo_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let text = self.parser.expect_tok_kind(TokenKind::StringLiteral)?;
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        let text_str = self.parser.input_str.span_to_str_unchecked(text.span());

        self.solver
            .echo(text_str)
            .map_err(|err| err.invoked_by(Command::Echo))?;
        Ok(())
    }

    fn parse_pop_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let levels = self.parser.expect_usize_numeral()?;
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        self.solver
            .pop(levels)
            .map_err(|err| err.invoked_by(Command::Pop))?;
        Ok(())
    }

    fn parse_push_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let levels = self.parser.expect_usize_numeral()?;
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        self.solver
            .push(levels)
            .map_err(|err| err.invoked_by(Command::Push))?;
        Ok(())
    }

    fn parse_get_info_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let info_tok = self.parser.expect_tok_kind(TokenKind::Keyword)?;
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        let info_str = self.parser.input_str.span_to_str_unchecked(info_tok.span());

        self.solver
            .get_info(GetInfoKind::from_str(info_str))
            .map_err(|err| err.invoked_by(Command::GetInfo))?;
        Ok(())
    }

    fn parse_get_option_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let option_tok = self.parser.expect_tok_kind(TokenKind::Keyword)?;
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        let option_str = self
            .parser
            .input_str
            .span_to_str_unchecked(option_tok.span());

        self.solver
            .get_option(option_str.into())
            .map_err(|err| err.invoked_by(Command::GetOption))?;
        Ok(())
    }

    fn parse_set_logic_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let logic_tok = self.parser.expect_tok_kind(TokenKind::Symbol)?;
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        let logic_str = self
            .parser
            .input_str
            .span_to_str_unchecked(logic_tok.span());

        self.solver
            .set_logic(logic_str)
            .map_err(|err| err.invoked_by(Command::SetLogic))?;
        Ok(())
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Sign {
    Pos,
    Neg,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct PropLit<'c> {
    name: &'c str,
    sign: Sign,
}

impl<'c> PropLit<'c> {
    fn new(name: &'c str, sign: Sign) -> Self {
        Self { name, sign }
    }

    pub fn pos(name: &'c str) -> PropLit {
        Self::new(name, Sign::Pos)
    }

    pub fn neg(name: &'c str) -> PropLit {
        Self::new(name, Sign::Neg)
    }

    pub fn name(self) -> &'c str {
        self.name
    }

    pub fn sign(self) -> Sign {
        self.sign
    }
}

#[derive(Debug, Clone)]
pub struct PropLitsIter<'c> {
    parser: Parser<'c>,
}

impl<'c> PropLitsIter<'c> {
    /// # Safety
    ///
    /// The caller has to verify that the given slice of the token iter is a valid
    /// sequence for propositional literals in SMTLib2 format.
    pub(self) unsafe fn new(parser: Parser<'c>) -> Self {
        let mut iter = Self { parser };
        iter.parser.expect_tok_kind(TokenKind::OpenParen).unwrap();
        iter
    }
}

impl<'c> Iterator for PropLitsIter<'c> {
    type Item = PropLit<'c>;

    fn next(&mut self) -> Option<Self::Item> {
        let tok = self.parser.peek().unwrap();
        match tok.kind() {
            TokenKind::Symbol => {
                self.parser.consume();
                Some(PropLit::pos(
                    self.parser.input_str.span_to_str_unchecked(tok.span()),
                ))
            }
            TokenKind::OpenParen => {
                self.parser.consume();
                self.parser.expect_symbol_matching_str("not").unwrap();
                let lit_str = self.parser.expect_symbol_tok().unwrap();
                self.parser.expect_tok_kind(TokenKind::CloseParen).unwrap();
                Some(PropLit::neg(lit_str))
            }
            TokenKind::CloseParen => None,
            _ => unreachable!(),
        }
    }
}

fn invoke_set_option<S>(solver: &mut S, option_data: OptionAndValue) -> CommandResponseResult
where
    S: SMTLib2Solver,
{
    solver
        .set_option(option_data)
        .map_err(|err| err.invoked_by(Command::SetOption))
}

fn invoke_set_info<S>(solver: &mut S, info_data: InfoAndValue) -> CommandResponseResult
where
    S: SMTLib2Solver,
{
    solver
        .set_info(info_data)
        .map_err(|err| err.invoked_by(Command::SetInfo))
}

impl<'c, 's, S> ParserDriver<'c, 's, S>
where
    S: SMTLib2Solver + 's,
{
    fn parse_check_sat_assuming_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let parser_before_sequence = self.parser.clone();
        self.parser.expect_tok_kind(TokenKind::OpenParen)?;

        while let Ok(tok) = self.parser.peek() {
            match tok.kind() {
                TokenKind::Symbol => {
                    self.parser.consume();
                }
                TokenKind::OpenParen => {
                    self.parser.consume();
                    self.parser.expect_symbol_matching_str("not")?;
                    self.parser.expect_tok_kind(TokenKind::Symbol)?;
                    self.parser.expect_tok_kind(TokenKind::CloseParen)?;
                }
                _ => break,
            }
        }
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;
        self.solver
            .check_sat_assuming(unsafe { PropLitsIter::new(parser_before_sequence) })
            .unwrap(); // TODO: proper error handling
        Ok(())
    }

    fn parse_set_option_bool_command(&mut self, opt: OptionKind) -> ParseResult<()> {
        debug_assert!(opt.has_bool_param());

        let bool_str = self
            .parser
            .expect_symbol_matching_pred(|s| s == "true" || s == "false")?;
        let flag = match bool_str {
            "true" => true,
            "false" => false,
            _ => unreachable!(),
        };

        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        use self::OptionKind::*;
        match opt {
            GlobalDeclarations => {
                invoke_set_option(self.solver, OptionAndValue::GlobalDeclarations(flag))
            }
            InteractiveMode => {
                invoke_set_option(self.solver, OptionAndValue::InteractiveMode(flag))
            }
            PrintSuccess => invoke_set_option(self.solver, OptionAndValue::PrintSuccess(flag)),
            ProduceAssertions => {
                invoke_set_option(self.solver, OptionAndValue::ProduceAssertions(flag))
            }
            ProduceAssignments => {
                invoke_set_option(self.solver, OptionAndValue::ProduceAssignments(flag))
            }
            ProduceProofs => invoke_set_option(self.solver, OptionAndValue::ProduceProofs(flag)),
            ProduceModels => invoke_set_option(self.solver, OptionAndValue::ProduceModels(flag)),
            ProduceUnsatAssumptions => {
                invoke_set_option(self.solver, OptionAndValue::ProduceUnsatAssumptions(flag))
            }
            ProduceUnsatCores => {
                invoke_set_option(self.solver, OptionAndValue::ProduceUnsatCores(flag))
            }
            _ => unreachable!(),
        }?;

        Ok(())
    }

    fn parse_set_option_output_channel_command(&mut self, opt: OptionKind) -> ParseResult<()> {
        debug_assert!(opt.has_output_channel_param());

        let outch_tok = self.parser.expect_tok_kind(TokenKind::StringLiteral)?;
        let outch_str = self
            .parser
            .input_str
            .span_to_str_unchecked(outch_tok.span());

        use std;
        let outch_ch = match outch_str {
            "stderr" => OutputChannel::Stderr,
            "stdout" => OutputChannel::Stdout,
            file => OutputChannel::File(std::path::Path::new(file)),
        };
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        match opt {
            OptionKind::DiagnosticOutputChannel => invoke_set_option(
                self.solver,
                OptionAndValue::DiagnosticOutputChannel(outch_ch),
            ),
            OptionKind::RegularOutputChannel => {
                invoke_set_option(self.solver, OptionAndValue::RegularOutputChannel(outch_ch))
            }
            _ => unreachable!(),
        }?;

        Ok(())
    }

    fn parse_set_option_numeral_command(&mut self, opt: OptionKind) -> ParseResult<()> {
        debug_assert!(opt.has_numeral_param());

        let numeral_tok = self.parser.expect_tok_kind(TokenKind::Numeral)?;
        let numeral_str = self
            .parser
            .input_str
            .span_to_str_unchecked(numeral_tok.span());
        let numeral_lit = NumeralLit::from_str(numeral_str);
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        use self::OptionKind::*;
        match opt {
            RandomSeed => invoke_set_option(self.solver, OptionAndValue::RandomSeed(numeral_lit)),
            ReproducibleResourceLimit => invoke_set_option(
                self.solver,
                OptionAndValue::ReproducibleResourceLimit(numeral_lit),
            ),
            Verbosity => invoke_set_option(self.solver, OptionAndValue::Verbosity(numeral_lit)),
            _ => unreachable!(),
        }?;

        Ok(())
    }

    fn parse_set_complex_custom_option_command(&mut self, _key_str: &'c str) -> ParseResult<()> {
        unimplemented!()
    }

    fn parse_set_custom_option_command(&mut self, key_str: &'c str) -> ParseResult<()> {
        let peek_tok = self.parser.peek()?;
        let peek_str = self.parser.input_str.span_to_str_unchecked(peek_tok.span());

        if peek_tok.kind() == TokenKind::OpenParen {
            return self.parse_set_complex_custom_option_command(key_str);
        }

        let value = match peek_tok.kind() {
            TokenKind::CloseParen => None,
            TokenKind::StringLiteral => Some(Literal::String(peek_str)),
            TokenKind::Keyword => Some(Literal::Keyword(peek_str)),
            TokenKind::Numeral => Some(Literal::Numeral(NumeralLit::from_str(peek_str))),
            TokenKind::Decimal => Some(Literal::Decimal(unsafe {
                DecimalLit::new_unchecked(peek_str)
            })), // { repr: peek_str })),
            TokenKind::Symbol => match peek_str {
                "true" => Some(Literal::Bool(true)),
                "false" => Some(Literal::Bool(false)),
                _ => Some(Literal::Symbol(peek_str)),
            },
            _ => unimplemented!(), // unexpected token
        };

        self.parser.consume();
        if value.is_some() {
            self.parser.expect_tok_kind(TokenKind::CloseParen)?;
        }

        invoke_set_option(
            self.solver,
            OptionAndValue::SimpleCustom {
                key: key_str,
                value,
            },
        )?;

        Ok(())
    }

    fn parse_set_option_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let option_tok = self.parser.expect_tok_kind(TokenKind::Keyword)?;
        let option_str = self
            .parser
            .input_str
            .span_to_str_unchecked(option_tok.span());

        use self::OptionKind::*;
        match option_str.into() {
            opt if opt.has_bool_param() => self.parse_set_option_bool_command(opt),
            opt if opt.has_output_channel_param() => {
                self.parse_set_option_output_channel_command(opt)
            }
            opt if opt.has_numeral_param() => self.parse_set_option_numeral_command(opt),
            Custom(key_str) => self.parse_set_custom_option_command(key_str),
            _ => unreachable!(),
        }
    }

    fn parse_set_info_smt_lib_version_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let version_tok = self.parser.expect_tok_kind(TokenKind::Decimal)?;
        let version_str = self
            .parser
            .input_str
            .span_to_str_unchecked(version_tok.span());
        let version_lit = unsafe { DecimalLit::new_unchecked(version_str) }; // { repr: version_str };
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        invoke_set_info(self.solver, InfoAndValue::SMTLibVersion(version_lit))?;

        Ok(())
    }

    fn parse_set_info_source_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let peek_tok = self.parser.peek()?;
        let peek_str = match peek_tok.kind() {
            TokenKind::StringLiteral | TokenKind::Symbol => {
                self.parser.input_str.span_to_str_unchecked(peek_tok.span())
            }
            _ => unimplemented!(), // unexpected token
        };

        self.parser.consume();
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        invoke_set_info(self.solver, InfoAndValue::Source(peek_str))?;

        Ok(())
    }

    fn parse_set_info_category_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let text_tok = self.parser.expect_tok_kind(TokenKind::StringLiteral)?;
        let text_str = self.parser.input_str.span_to_str_unchecked(text_tok.span());

        let category = match text_str {
            "crafted" => ProblemCategory::Crafted,
            "random" => ProblemCategory::Random,
            "industrial" => ProblemCategory::Industrial,
            _ => unimplemented!(), // error: unknown category kind
        };

        self.parser.expect_tok_kind(TokenKind::CloseParen)?;
        invoke_set_info(self.solver, InfoAndValue::Category(category))?;

        Ok(())
    }

    fn parse_set_info_license_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let text_tok = self.parser.expect_tok_kind(TokenKind::StringLiteral)?;
        let text_str = self.parser.input_str.span_to_str_unchecked(text_tok.span());

        self.parser.expect_tok_kind(TokenKind::CloseParen)?;
        invoke_set_info(self.solver, InfoAndValue::License(text_str))?;

        Ok(())
    }

    fn parse_set_info_status_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let sym_str = self.parser.expect_symbol_tok()?;

        let status = match sym_str {
            "sat" => ProblemStatus::Sat,
            "unsat" => ProblemStatus::Unsat,
            "unknown" => ProblemStatus::Unknown,
            _ => unimplemented!(), // error: unknown status kind
        };

        self.parser.expect_tok_kind(TokenKind::CloseParen)?;
        invoke_set_info(self.solver, InfoAndValue::Status(status))?;

        Ok(())
    }

    fn parse_set_info_complex_custom_command(&mut self, _key: &'c str) -> ParseResult<()> {
        unimplemented!()
    }

    fn parse_set_info_custom_command(&mut self, key: &'c str) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let peek_tok = self.parser.peek()?;
        let peek_str = self.parser.input_str.span_to_str_unchecked(peek_tok.span());

        if let TokenKind::OpenParen = peek_tok.kind() {
            return self.parse_set_info_complex_custom_command(key);
        }

        let value = match peek_tok.kind() {
            TokenKind::CloseParen => None,
            TokenKind::StringLiteral => Some(Literal::String(peek_str)),
            TokenKind::Keyword => Some(Literal::Keyword(peek_str)),
            TokenKind::Numeral => Some(Literal::Numeral(NumeralLit::from_str(peek_str))),
            TokenKind::Decimal => Some(Literal::Decimal(unsafe {
                DecimalLit::new_unchecked(peek_str)
            })), //{ repr: peek_str })),
            TokenKind::Symbol => match peek_str {
                "true" => Some(Literal::Bool(true)),
                "false" => Some(Literal::Bool(false)),
                _ => Some(Literal::Symbol(peek_str)),
            },
            _ => unimplemented!(), // unexpected token
        };

        self.parser.consume();
        if value.is_some() {
            self.parser.expect_tok_kind(TokenKind::CloseParen)?;
        }

        invoke_set_info(self.solver, InfoAndValue::SimpleCustom { key, value })?;

        Ok(())
    }

    fn parse_set_info_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let info_tok = self.parser.expect_tok_kind(TokenKind::Keyword)?;
        let info_str = self.parser.input_str.span_to_str_unchecked(info_tok.span());

        match info_str {
            ":smt-lib-version" => self.parse_set_info_smt_lib_version_command(),
            ":source" => self.parse_set_info_source_command(),
            ":category" => self.parse_set_info_category_command(),
            ":license" => self.parse_set_info_license_command(),
            ":status" => self.parse_set_info_status_command(),
            custom => self.parse_set_info_custom_command(custom),
        }?;

        Ok(())
    }

    fn parse_command(&mut self) -> ParseResult<()> {
        self.parser.expect_tok_kind(TokenKind::OpenParen)?;
        let command = self.parser.expect_command_tok()?;
        use self::Command::*;
        #[cfg_attr(rustfmt, rustfmt_skip)]
        match command {
            // Simple commands that have no parameters.
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

            // Fixed-size commands that have a fixed set of fixed-size parameters.
            DeclareSort      => self.parse_declare_sort_command(),
            Echo             => self.parse_echo_command(),
            Pop              => self.parse_pop_command(),
            Push             => self.parse_push_command(),
            GetInfo          => self.parse_get_info_command(),
            GetOption        => self.parse_get_option_command(),
            SetLogic         => self.parse_set_logic_command(),
            CheckSatAssuming => self.parse_check_sat_assuming_command(),
            SetOption        => self.parse_set_option_command(),
            SetInfo          => self.parse_set_info_command(),

            _ => unimplemented!(),
        }
    }

    pub fn parse_script(&mut self) -> ParseResult<()> {
        while let Ok(_) = self.parser.peek() {
            self.parse_command()?
        }
        Ok(())
    }
}
