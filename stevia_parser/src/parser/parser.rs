use commands::{
    DecimalLit,
    DecimalLitBase,
    LiteralBase,
    NumeralLit,
    NumeralLitBase,
    OptionAndValueBase,
    OptionKind,
    OptionKindBase,
    OutputChannelBase,
    ResponseResult,
    SMTLib2Solver,
    SetInfoKind,
    SetInfoKindBase,
};
use lexer::{smtlib2_tokens, Command, Span, Token, TokenIter, TokenKind};
use parser::error::{ParseError, ParseResult};

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

    pub fn span_to_str_unchecked(&self, span: Span) -> &'c str {
        debug_assert!(self.content.as_bytes().len() >= 1);
        debug_assert!(span.begin.to_usize() < self.content.as_bytes().len());
        debug_assert!(span.end.to_usize() < self.content.as_bytes().len());
        unsafe {
            self.content
                .slice_unchecked(span.begin.to_usize(), span.end.to_usize() + 1)
        }
    }
}

impl<'c> Parser<'c> {
    pub(self) fn new(input: &'c str) -> Self {
        Self {
            token_iter: smtlib2_tokens(input),
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
            _ => Err(unimplemented!()), // error: unexpected non-command token
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
            return Err(unimplemented!());
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
    fn parse_simple_command<C>(&mut self, _kind: Command, command: C) -> ParseResult<()>
    where
        C: Fn(&mut S) -> ResponseResult,
    {
        debug_assert!(self.parser.peek().is_ok());

        self.parser.expect_tok_kind(TokenKind::CloseParen)?;
        command(self.solver)?;
        Ok(())
    }

    fn parse_declare_sort_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let symbol = self.parser.expect_tok_kind(TokenKind::Symbol)?;
        let arity = self.parser.expect_usize_numeral()?;
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        let symbol_str = self.parser.input_str.span_to_str_unchecked(symbol.span());

        self.solver.declare_sort(symbol_str, arity)?;
        Ok(())
    }

    fn parse_echo_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let text = self.parser.expect_tok_kind(TokenKind::StringLiteral)?;
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        let text_str = self.parser.input_str.span_to_str_unchecked(text.span());

        self.solver.echo(text_str)?;
        Ok(())
    }

    fn parse_pop_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let levels = self.parser.expect_usize_numeral()?;
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        self.solver.pop(levels)?;
        Ok(())
    }

    fn parse_push_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let levels = self.parser.expect_usize_numeral()?;
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        self.solver.push(levels)?;
        Ok(())
    }

    fn parse_get_info_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let info_tok = self.parser.expect_tok_kind(TokenKind::Keyword)?;
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        let info_str = self.parser.input_str.span_to_str_unchecked(info_tok.span());

        self.solver.get_info(info_str)?;
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

        self.solver.get_option(option_str.into())?;
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

        self.solver.set_logic(logic_str)?;
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

        use self::OptionKindBase::*;
        match opt {
            GlobalDeclarations => self
                .solver
                .set_option(OptionAndValueBase::GlobalDeclarations(flag)),
            InteractiveMode => self
                .solver
                .set_option(OptionAndValueBase::InteractiveMode(flag)),
            PrintSuccess => self
                .solver
                .set_option(OptionAndValueBase::PrintSuccess(flag)),
            ProduceAssertions => self
                .solver
                .set_option(OptionAndValueBase::ProduceAssertions(flag)),
            ProduceAssignments => self
                .solver
                .set_option(OptionAndValueBase::ProduceAssignments(flag)),
            ProduceModels => self
                .solver
                .set_option(OptionAndValueBase::ProduceModels(flag)),
            ProduceProofs => self
                .solver
                .set_option(OptionAndValueBase::ProduceProofs(flag)),
            ProduceUnsatAssumptions => self
                .solver
                .set_option(OptionAndValueBase::ProduceUnsatAssumptions(flag)),
            ProduceUnsatCores => self
                .solver
                .set_option(OptionAndValueBase::ProduceUnsatCores(flag)),
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
            "stderr" => OutputChannelBase::Stderr,
            "stdout" => OutputChannelBase::Stdout,
            file => OutputChannelBase::File(std::path::Path::new(file)),
        };
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        match opt {
            OptionKindBase::DiagnosticOutputChannel => self
                .solver
                .set_option(OptionAndValueBase::DiagnosticOutputChannel(outch_ch)),
            OptionKindBase::RegularOutputChannel => self
                .solver
                .set_option(OptionAndValueBase::RegularOutputChannel(outch_ch)),
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
        let numeral_lit = NumeralLit { repr: numeral_str };
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        use self::OptionKindBase::*;
        match opt {
            RandomSeed => self
                .solver
                .set_option(OptionAndValueBase::RandomSeed(numeral_lit)),
            ReproducibleResourceLimit => self
                .solver
                .set_option(OptionAndValueBase::ReproducibleResourceLimit(numeral_lit)),
            Verbosity => self
                .solver
                .set_option(OptionAndValueBase::Verbosity(numeral_lit)),
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
            TokenKind::StringLiteral => Some(LiteralBase::String(peek_str)),
            TokenKind::Keyword => Some(LiteralBase::Keyword(peek_str)),
            TokenKind::Numeral => Some(LiteralBase::Numeral(NumeralLitBase { repr: peek_str })),
            TokenKind::Decimal => Some(LiteralBase::Decimal(DecimalLitBase { repr: peek_str })),
            TokenKind::Symbol => match peek_str {
                "true" => Some(LiteralBase::Bool(true)),
                "false" => Some(LiteralBase::Bool(false)),
                _ => Some(LiteralBase::Symbol(peek_str)),
            },
            _ => return Err(unimplemented!()), // unexpected token
        };

        self.parser.consume();
        if value.is_some() {
            self.parser.expect_tok_kind(TokenKind::CloseParen)?;
        }

        self.solver.set_option(OptionAndValueBase::SimpleCustom {
            key: key_str,
            value,
        })?;

        Ok(())
    }

    fn parse_set_option_command(&mut self) -> ParseResult<()> {
        debug_assert!(self.parser.peek().is_ok());

        let option_tok = self.parser.expect_tok_kind(TokenKind::Keyword)?;
        let option_str = self
            .parser
            .input_str
            .span_to_str_unchecked(option_tok.span());

        use self::OptionKindBase::*;
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
        let version_lit = DecimalLit { repr: version_str };
        self.parser.expect_tok_kind(TokenKind::CloseParen)?;

        self.solver
            .set_info(SetInfoKindBase::SMTLibVersion(version_lit))?;

        Ok(())
    }

    fn parse_set_info_source_command(&mut self) -> ParseResult<()> {
        unimplemented!()
    }

    fn parse_set_info_category_command(&mut self) -> ParseResult<()> {
        unimplemented!()
    }

    fn parse_set_info_license_command(&mut self) -> ParseResult<()> {
        unimplemented!()
    }

    fn parse_set_info_status_command(&mut self) -> ParseResult<()> {
        unimplemented!()
    }

    fn parse_set_info_custom_command(&mut self, _key: &'c str) -> ParseResult<()> {
        unimplemented!()
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

#[cfg(test)]
mod tests {
    use super::*;
    use commands::ResponseResult;

    #[derive(Debug, Clone, PartialEq, Eq)]
    enum DummyPropLit {
        Pos(String),
        Neg(String),
    }

    impl DummyPropLit {
        pub fn pos<S>(id: S) -> Self
        where
            S: Into<String>,
        {
            DummyPropLit::Pos(id.into())
        }

        pub fn neg<S>(id: S) -> Self
        where
            S: Into<String>,
        {
            DummyPropLit::Neg(id.into())
        }
    }

    use commands::{
        DecimalLit,
        DecimalLitBase,
        Literal,
        LiteralBase,
        NumeralLit,
        NumeralLitBase,
        OptionAndValue,
        OptionAndValueBase,
        OutputChannel,
        OutputChannelBase,
    };
    use std;

    pub type DummyOptionKind = OptionKindBase<String>;
    pub type DummyLiteral = LiteralBase<String>;
    pub type DummyNumeralLit = NumeralLitBase<String>;
    pub type DummyDecimalLit = DecimalLitBase<String>;
    pub type DummyOutputChannel = OutputChannelBase<std::path::PathBuf>;
    pub type DummyOptionAndValue = OptionAndValueBase<String, std::path::PathBuf>;
    pub type DummySetInfoKind = SetInfoKindBase<String>;

    impl<'c> From<NumeralLit<'c>> for DummyNumeralLit {
        fn from(lit: NumeralLit<'c>) -> Self {
            Self {
                repr: lit.into_repr().to_owned(),
            }
        }
    }

    impl<'c> From<DecimalLit<'c>> for DummyDecimalLit {
        fn from(lit: DecimalLit<'c>) -> Self {
            Self {
                repr: lit.into_repr().to_owned(),
            }
        }
    }

    impl<'c> From<OutputChannel<'c>> for DummyOutputChannel {
        fn from(och: OutputChannel<'c>) -> Self {
            use self::OutputChannelBase::*;
            match och {
                Stdout => Stdout,
                Stderr => Stderr,
                File(p) => File(p.to_owned()),
            }
        }
    }

    impl<'c> From<Literal<'c>> for DummyLiteral {
        fn from(lit: Literal<'c>) -> Self {
            use self::LiteralBase::*;
            match lit {
                Bool(repr) => Bool(repr),
                String(repr) => String(repr.to_owned()),
                Symbol(repr) => Symbol(repr.into()),
                Numeral(repr) => Numeral(repr.into()),
                Keyword(repr) => Keyword(repr.to_owned()),
                Decimal(repr) => Decimal(repr.into()),
            }
        }
    }

    impl<'c> From<OptionKind<'c>> for DummyOptionKind {
        fn from(kind: OptionKind<'c>) -> Self {
            use self::OptionKindBase::*;
            match kind {
                DiagnosticOutputChannel => DiagnosticOutputChannel,
                GlobalDeclarations => GlobalDeclarations,
                InteractiveMode => InteractiveMode,
                PrintSuccess => PrintSuccess,
                ProduceAssertions => ProduceAssertions,
                ProduceAssignments => ProduceAssignments,
                ProduceModels => ProduceModels,
                ProduceProofs => ProduceProofs,
                ProduceUnsatAssumptions => ProduceUnsatAssumptions,
                ProduceUnsatCores => ProduceUnsatCores,
                RandomSeed => RandomSeed,
                RegularOutputChannel => RegularOutputChannel,
                ReproducibleResourceLimit => ReproducibleResourceLimit,
                Verbosity => Verbosity,
                Custom(s) => Custom(s.to_owned()),
            }
        }
    }

    impl<'c> From<OptionAndValue<'c>> for DummyOptionAndValue {
        fn from(kind: OptionAndValue<'c>) -> Self {
            use self::OptionAndValueBase::*;
            match kind {
                DiagnosticOutputChannel(ch) => DiagnosticOutputChannel(ch.into()),
                GlobalDeclarations(f) => GlobalDeclarations(f),
                InteractiveMode(f) => InteractiveMode(f),
                PrintSuccess(f) => PrintSuccess(f),
                ProduceAssertions(f) => ProduceAssertions(f),
                ProduceAssignments(f) => ProduceAssignments(f),
                ProduceModels(f) => ProduceModels(f),
                ProduceProofs(f) => ProduceProofs(f),
                ProduceUnsatAssumptions(f) => ProduceUnsatAssumptions(f),
                ProduceUnsatCores(f) => ProduceUnsatCores(f),
                RandomSeed(r) => RandomSeed(r.into()),
                RegularOutputChannel(ch) => RegularOutputChannel(ch.into()),
                ReproducibleResourceLimit(n) => ReproducibleResourceLimit(n.into()),
                Verbosity(n) => Verbosity(n.into()),
                SimpleCustom { key, value } => SimpleCustom {
                    key: key.into(),
                    value: value.map(Into::into),
                },
                ComplexCustom { key } => ComplexCustom {
                    key: key.to_owned(),
                },
            }
        }
    }

    impl<'c> From<SetInfoKind<'c>> for DummySetInfoKind {
        fn from(kind: SetInfoKind<'c>) -> Self {
            use self::SetInfoKindBase::*;
            match kind {
                SMTLibVersion(dec) => SMTLibVersion(dec.into()),
                Source(s) => Source(s.into()),
                Category(cat) => Category(cat.into()),
                License(text) => License(text.into()),
                Status(kind) => Status(kind.into()),
                SimpleCustom { key, value } => SimpleCustom {
                    key: key.into(),
                    value: value.map(|v| v.into()),
                },
                ComplexCustom { key } => ComplexCustom { key: key.into() },
            }
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    enum ParseEvent {
        CheckSat,
        CheckSatAssuming {
            prop_lits: Vec<DummyPropLit>,
        },
        DeclareSort {
            symbol: String,
            arity: usize,
        },
        Echo {
            content: String,
        },
        Exit,
        GetAssertions,
        GetAssignment,
        GetInfo {
            info: String,
        },
        GetModel,
        GetOption {
            option: DummyOptionKind,
        },
        GetProof,
        GetUnsatAssumptions,
        GetUnsatCore,
        Pop {
            levels: usize,
        },
        Push {
            levels: usize,
        },
        Reset,
        ResetAssertions,
        SetLogic {
            id: String,
        },
        SetOption {
            option_and_value: DummyOptionAndValue,
        },
        SetInfo {
            info_and_value: DummySetInfoKind,
        },
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
        fn check_sat(&mut self) -> ResponseResult {
            self.events.push(ParseEvent::CheckSat);
            Ok(())
        }

        fn check_sat_assuming(&mut self, prop_lits: PropLitsIter) -> ResponseResult {
            self.events.push(ParseEvent::CheckSatAssuming {
                prop_lits: prop_lits
                    .map(|lit| match lit.sign() {
                        Sign::Pos => DummyPropLit::pos(lit.name()),
                        Sign::Neg => DummyPropLit::neg(lit.name()),
                    })
                    .collect(),
            });
            Ok(())
        }

        fn declare_sort(&mut self, symbol: &str, arity: usize) -> ResponseResult {
            self.events.push(ParseEvent::DeclareSort {
                symbol: symbol.to_owned(),
                arity,
            });
            Ok(())
        }

        fn echo(&mut self, content: &str) -> ResponseResult {
            self.events.push(ParseEvent::Echo {
                content: content.to_owned(),
            });
            Ok(())
        }

        fn exit(&mut self) -> ResponseResult {
            self.events.push(ParseEvent::Exit);
            Ok(())
        }

        fn get_assertions(&mut self) -> ResponseResult {
            self.events.push(ParseEvent::GetAssertions);
            Ok(())
        }

        fn get_assignment(&mut self) -> ResponseResult {
            self.events.push(ParseEvent::GetAssignment);
            Ok(())
        }

        fn get_info(&mut self, info: &str) -> ResponseResult {
            self.events.push(ParseEvent::GetInfo {
                info: info.to_owned(),
            });
            Ok(())
        }

        fn get_model(&mut self) -> ResponseResult {
            self.events.push(ParseEvent::GetModel);
            Ok(())
        }

        fn get_option(&mut self, option: OptionKind) -> ResponseResult {
            self.events.push(ParseEvent::GetOption {
                option: option.into(),
            });
            Ok(())
        }

        fn get_proof(&mut self) -> ResponseResult {
            self.events.push(ParseEvent::GetProof);
            Ok(())
        }

        fn get_unsat_assumptions(&mut self) -> ResponseResult {
            self.events.push(ParseEvent::GetUnsatAssumptions);
            Ok(())
        }

        fn get_unsat_core(&mut self) -> ResponseResult {
            self.events.push(ParseEvent::GetUnsatCore);
            Ok(())
        }

        fn pop(&mut self, levels: usize) -> ResponseResult {
            self.events.push(ParseEvent::Pop { levels });
            Ok(())
        }

        fn push(&mut self, levels: usize) -> ResponseResult {
            self.events.push(ParseEvent::Push { levels });
            Ok(())
        }

        fn reset(&mut self) -> ResponseResult {
            self.events.push(ParseEvent::Reset);
            Ok(())
        }

        fn reset_assertions(&mut self) -> ResponseResult {
            self.events.push(ParseEvent::ResetAssertions);
            Ok(())
        }

        fn set_logic(&mut self, id: &str) -> ResponseResult {
            self.events.push(ParseEvent::SetLogic { id: id.to_owned() });
            Ok(())
        }

        fn set_option(&mut self, option_and_value: OptionAndValue) -> ResponseResult {
            self.events.push(ParseEvent::SetOption {
                option_and_value: option_and_value.into(),
            });
            Ok(())
        }

        fn set_info(&mut self, info_and_value: SetInfoKind) -> ResponseResult {
            self.events.push(ParseEvent::SetInfo {
                info_and_value: info_and_value.into(),
            });
            Ok(())
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

        #[test]
        fn fixed_size() {
            assert_parse_valid_smtlib2(
                "(declare-sort FooTypeName 42)",
                vec![ParseEvent::DeclareSort {
                    symbol: String::from("FooTypeName"),
                    arity: 42,
                }],
            );
            assert_parse_valid_smtlib2(
                "(echo \"Hello, World!\")",
                vec![ParseEvent::Echo {
                    content: String::from("Hello, World!"),
                }],
            );
            assert_parse_valid_smtlib2("(push 42)", vec![ParseEvent::Push { levels: 42 }]);
            assert_parse_valid_smtlib2("(pop 5)", vec![ParseEvent::Pop { levels: 5 }]);
            assert_parse_valid_smtlib2(
                "(get-option :my-option)",
                vec![ParseEvent::GetOption {
                    option: OptionKindBase::Custom(":my-option".to_owned()),
                }],
            );
            assert_parse_valid_smtlib2(
                "(set-logic QF_ABV)",
                vec![ParseEvent::SetLogic {
                    id: "QF_ABV".to_owned(),
                }],
            );
        }

        #[test]
        fn get_info_command() {
            fn assert_get_info_for(info: &str) {
                assert_parse_valid_smtlib2(
                    &format!("(get-info {})", info),
                    vec![ParseEvent::GetInfo {
                        info: info.to_owned(),
                    }],
                );
            }
            assert_get_info_for(":all-statistics");
            assert_get_info_for(":assert-non-stack-levels");
            assert_get_info_for(":authors");
            assert_get_info_for(":error-behaviour");
            assert_get_info_for(":name");
            assert_get_info_for(":reason-unknown");
            assert_get_info_for(":version");
            assert_get_info_for(":my-custom-info-flag");
        }

        mod check_sat_assuming {
            use super::*;

            #[test]
            fn empty_prop_lits() {
                assert_parse_valid_smtlib2(
                    "(check-sat-assuming ())",
                    vec![ParseEvent::CheckSatAssuming { prop_lits: vec![] }],
                );
            }

            #[test]
            fn only_pos() {
                assert_parse_valid_smtlib2(
                    "(check-sat-assuming (fst snd trd))",
                    vec![ParseEvent::CheckSatAssuming {
                        prop_lits: vec![
                            DummyPropLit::pos("fst"),
                            DummyPropLit::pos("snd"),
                            DummyPropLit::pos("trd"),
                        ],
                    }],
                );
            }

            #[test]
            fn only_neg() {
                assert_parse_valid_smtlib2(
                    "(check-sat-assuming ((not fst) (not snd) (not trd)))",
                    vec![ParseEvent::CheckSatAssuming {
                        prop_lits: vec![
                            DummyPropLit::neg("fst"),
                            DummyPropLit::neg("snd"),
                            DummyPropLit::neg("trd"),
                        ],
                    }],
                );
            }

            #[test]
            fn mixed() {
                assert_parse_valid_smtlib2(
                    "(check-sat-assuming (fst (not snd) trd))",
                    vec![ParseEvent::CheckSatAssuming {
                        prop_lits: vec![
                            DummyPropLit::pos("fst"),
                            DummyPropLit::neg("snd"),
                            DummyPropLit::pos("trd"),
                        ],
                    }],
                );
            }
        }

        mod set_option {
            use super::*;

            #[test]
            fn simple_bool() {
                use self::OptionAndValueBase::*;
                fn assert_simple_bool(
                    opt_str: &str,
                    true_case: DummyOptionAndValue,
                    false_case: DummyOptionAndValue,
                ) {
                    assert_parse_valid_smtlib2(
                        &format!("(set-option {} true)", opt_str),
                        vec![ParseEvent::SetOption {
                            option_and_value: true_case,
                        }],
                    );
                    assert_parse_valid_smtlib2(
                        &format!("(set-option {} false)", opt_str),
                        vec![ParseEvent::SetOption {
                            option_and_value: false_case,
                        }],
                    );
                }
                assert_simple_bool(
                    ":global-declarations",
                    GlobalDeclarations(true),
                    GlobalDeclarations(false),
                );
                assert_simple_bool(
                    ":interactive-mode",
                    InteractiveMode(true),
                    InteractiveMode(false),
                );
                assert_simple_bool(":print-success", PrintSuccess(true), PrintSuccess(false));
                assert_simple_bool(
                    ":produce-assertions",
                    ProduceAssertions(true),
                    ProduceAssertions(false),
                );
                assert_simple_bool(
                    ":produce-assignments",
                    ProduceAssignments(true),
                    ProduceAssignments(false),
                );
                assert_simple_bool(":produce-models", ProduceModels(true), ProduceModels(false));
                assert_simple_bool(":produce-proofs", ProduceProofs(true), ProduceProofs(false));
                assert_simple_bool(
                    ":produce-unsat-assumptions",
                    ProduceUnsatAssumptions(true),
                    ProduceUnsatAssumptions(false),
                );
                assert_simple_bool(
                    ":produce-unsat-cores",
                    ProduceUnsatCores(true),
                    ProduceUnsatCores(false),
                );
            }

            #[test]
            fn simple_numeral() {
                use self::OptionAndValueBase::*;
                assert_parse_valid_smtlib2(
                    "(set-option :random-seed 5)",
                    vec![ParseEvent::SetOption {
                        option_and_value: RandomSeed(DummyNumeralLit {
                            repr: String::from("5"),
                        }),
                    }],
                );
                assert_parse_valid_smtlib2(
                    "(set-option :reproducible-resource-limit 42)",
                    vec![ParseEvent::SetOption {
                        option_and_value: ReproducibleResourceLimit(DummyNumeralLit {
                            repr: String::from("42"),
                        }),
                    }],
                );
                assert_parse_valid_smtlib2(
                    "(set-option :verbosity 1337)",
                    vec![ParseEvent::SetOption {
                        option_and_value: Verbosity(DummyNumeralLit {
                            repr: String::from("1337"),
                        }),
                    }],
                );
            }

            #[test]
            fn simple_output_channel() {
                use self::OptionAndValueBase::*;
                {
                    assert_parse_valid_smtlib2(
                        "(set-option :diagnostic-output-channel \"stderr\")",
                        vec![ParseEvent::SetOption {
                            option_and_value: DiagnosticOutputChannel(OutputChannelBase::Stderr),
                        }],
                    );
                    assert_parse_valid_smtlib2(
                        "(set-option :diagnostic-output-channel \"stdout\")",
                        vec![ParseEvent::SetOption {
                            option_and_value: DiagnosticOutputChannel(OutputChannelBase::Stdout),
                        }],
                    );
                    assert_parse_valid_smtlib2(
                        "(set-option :diagnostic-output-channel \"my_file\")",
                        vec![ParseEvent::SetOption {
                            option_and_value: DiagnosticOutputChannel(OutputChannelBase::File(
                                std::path::PathBuf::from("my_file"),
                            )),
                        }],
                    );
                }
                {
                    assert_parse_valid_smtlib2(
                        "(set-option :regular-output-channel \"stderr\")",
                        vec![ParseEvent::SetOption {
                            option_and_value: RegularOutputChannel(OutputChannelBase::Stderr),
                        }],
                    );
                    assert_parse_valid_smtlib2(
                        "(set-option :regular-output-channel \"stdout\")",
                        vec![ParseEvent::SetOption {
                            option_and_value: RegularOutputChannel(OutputChannelBase::Stdout),
                        }],
                    );
                    assert_parse_valid_smtlib2(
                        "(set-option :regular-output-channel \"my_file\")",
                        vec![ParseEvent::SetOption {
                            option_and_value: RegularOutputChannel(OutputChannelBase::File(
                                std::path::PathBuf::from("my_file"),
                            )),
                        }],
                    );
                }
            }

            mod simple_custom {
                use self::OptionAndValueBase::*;
                use super::*;

                #[test]
                fn empty_value() {
                    assert_parse_valid_smtlib2(
                        "(set-option :my-custom-cmd)",
                        vec![ParseEvent::SetOption {
                            option_and_value: SimpleCustom {
                                key: String::from(":my-custom-cmd"),
                                value: None,
                            },
                        }],
                    );
                }

                #[test]
                fn bool_value() {
                    assert_parse_valid_smtlib2(
                        "(set-option :my-custom-cmd true)",
                        vec![ParseEvent::SetOption {
                            option_and_value: SimpleCustom {
                                key: String::from(":my-custom-cmd"),
                                value: Some(LiteralBase::Bool(true)),
                            },
                        }],
                    );
                    assert_parse_valid_smtlib2(
                        "(set-option :my-custom-cmd false)",
                        vec![ParseEvent::SetOption {
                            option_and_value: SimpleCustom {
                                key: String::from(":my-custom-cmd"),
                                value: Some(LiteralBase::Bool(false)),
                            },
                        }],
                    );
                }

                #[test]
                fn symbol_value() {
                    assert_parse_valid_smtlib2(
                        "(set-option :my-custom-cmd Foo)",
                        vec![ParseEvent::SetOption {
                            option_and_value: SimpleCustom {
                                key: String::from(":my-custom-cmd"),
                                value: Some(LiteralBase::Symbol(String::from("Foo"))),
                            },
                        }],
                    );
                }

                #[test]
                fn numeral_value() {
                    assert_parse_valid_smtlib2(
                        "(set-option :my-custom-cmd 42)",
                        vec![ParseEvent::SetOption {
                            option_and_value: SimpleCustom {
                                key: String::from(":my-custom-cmd"),
                                value: Some(LiteralBase::Numeral(NumeralLitBase {
                                    repr: String::from("42"),
                                })),
                            },
                        }],
                    );
                }

                #[test]
                fn decimal_value() {
                    assert_parse_valid_smtlib2(
                        "(set-option :my-custom-cmd 7.7)",
                        vec![ParseEvent::SetOption {
                            option_and_value: SimpleCustom {
                                key: String::from(":my-custom-cmd"),
                                value: Some(LiteralBase::Decimal(DecimalLitBase {
                                    repr: String::from("7.7"),
                                })),
                            },
                        }],
                    );
                }

                #[test]
                fn keyword_value() {
                    assert_parse_valid_smtlib2(
                        "(set-option :my-custom-cmd :my-keyword)",
                        vec![ParseEvent::SetOption {
                            option_and_value: SimpleCustom {
                                key: String::from(":my-custom-cmd"),
                                value: Some(LiteralBase::Keyword(String::from(":my-keyword"))),
                            },
                        }],
                    );
                }
            }
        }

        mod set_info {
            use self::SetInfoKindBase::*;
            use super::*;

            #[test]
            fn smt_lib_version() {
                assert_parse_valid_smtlib2(
                    "(set-info :smt-lib-version 2.6)",
                    vec![ParseEvent::SetInfo {
                        info_and_value: SMTLibVersion(DecimalLitBase {
                            repr: String::from("2.6"),
                        }),
                    }],
                );
            }
        }
    }
}
