use either::Either;

use std;
use std::iter::FromIterator;

/// An expression.
///
/// This is either a standalone atom or an S-expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr<'c> {
    /// An atom.
    Atom(Atom<'c>),
    /// An S-expression bundling several sub expressions together.
    SExpr(SExpr<'c>),
}

impl<'c> From<Atom<'c>> for Expr<'c> {
    fn from(atom: Atom<'c>) -> Self {
        Expr::Atom(atom)
    }
}

impl<'c> From<SExpr<'c>> for Expr<'c> {
    fn from(s_expr: SExpr<'c>) -> Self {
        Expr::SExpr(s_expr)
    }
}

impl<'c> Expr<'c> {
    pub fn string_unchecked(content: &'c str) -> Self {
        Expr::from(Atom::from(Literal::string(content)))
    }

    pub fn numeral(content: &'c str) -> NumeralResult<Self> {
        Ok(Expr::from(Atom::from(Literal::from(Numeral::from_str(content)?))))
    }

    pub fn decimal(content: &'c str) -> DecimalResult<Self> {
        Ok(Expr::from(Atom::from(Literal::from(unsafe{ Decimal::from_str_unchecked(content) }))))
    }

    pub fn symbol_unchecked(content: &'c str) -> Self {
        Expr::from(Atom::from(unsafe{ Symbol::new_unchecked(content) }))
    }

    pub fn keyword_unchecked(content: &'c str) -> Self {
        Expr::from(Atom::from(unsafe{ Keyword::new_unchecked(content) }))
    }

    pub fn s_expr<I>(exprs: I) -> Self
    where
        I: IntoIterator<Item = Expr<'c>>,
    {
        Expr::from(SExpr::from_iter(exprs))
    }
}

/// An S-Expression.
///
/// This bundles several child expressions together.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SExpr<'c> {
    /// The child expressions of this S-expression.
    exprs: Vec<Expr<'c>>,
}

impl<'c> Default for SExpr<'c> {
    fn default() -> Self {
        SExpr { exprs: vec![] }
    }
}

impl<'c> SExpr<'c> {
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn len(&self) -> usize {
        self.exprs.len()
    }

    pub fn push<'e, E>(&mut self, expr: E)
    where
        E: Into<Expr<'e>>,
        'e: 'c,
    {
        self.exprs.push(expr.into());
    }
}

impl<'c> FromIterator<Expr<'c>> for SExpr<'c> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = Expr<'c>>,
    {
        SExpr {
            exprs: iter.into_iter().collect::<Vec<_>>(),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Atom<'c> {
    /// A literal.
    ///
    /// # Note
    ///
    /// For example a boolean, string or number literal.
    Literal(Literal<'c>),
    /// A symbol.
    ///
    /// # Note
    ///
    /// At this level of abstraction there is no distinction made
    /// between simple and quoted symbols of the SMTLib2 format.
    Symbol(Symbol<'c>),
    /// A predefined symbol with special meaning starting with ':' (a.k.a. keyword).
    Keyword(Keyword<'c>),
}

impl<'c> From<Symbol<'c>> for Atom<'c> {
    fn from(symbol: Symbol<'c>) -> Self {
        Atom::Symbol(symbol)
    }
}

impl<'c> From<Literal<'c>> for Atom<'c> {
    fn from(literal: Literal<'c>) -> Self {
        Atom::Literal(literal)
    }
}

impl<'c> From<Keyword<'c>> for Atom<'c> {
    fn from(keyword: Keyword<'c>) -> Self {
        Atom::Keyword(keyword)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Symbol<'c> {
    /// The identifier or name of this symbol.
    content: &'c str,
}

impl<'c> Symbol<'c> {
    /// Constructs a new symbol from the given content `str`.
    ///
    /// # Safety
    ///
    /// This does not check integrity of the input `str`.
    pub unsafe fn new_unchecked(content: &'c str) -> Self {
        Symbol { content }
    }

    /// Returns the identifier or name of the associated symbol.
    pub fn as_str(&self) -> &str {
        self.content
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Keyword<'c> {
    /// The identifier or name of this keyword.
    content: &'c str,
}

impl<'c> Keyword<'c> {
    /// Constructs a new keyword from the given content `str`.
    ///
    /// # Safety
    ///
    /// This does not check integrity of the input `str`.
    pub unsafe fn new_unchecked(content: &'c str) -> Self {
        Keyword { content }
    }

    /// Returns the identifier or name of the associated keyword.
    pub fn as_str(&self) -> &str {
        self.content
    }
}

/// View to a literal or constant specified in the SMTLib2 input language.
///
/// # Note
///
/// This is most often just a simple string sub slice into the given input
/// that was previously parsed and found to be a literal match.
///
/// This could either represent
///
/// - a boolean: `true` or `false`
/// - a string: `"Hello, World!"`
/// - a symbol: `foo`
/// - a keyword: `:bar`
/// - a numeral: `42`
/// - a decimal: `7.4`
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum LiteralKind<'c> {
    /// A string literal.
    String(&'c str),
    /// A numeral literal.
    ///
    /// # Note
    ///
    /// The possible encodings for this are decimal, binary or hexadecimal.
    /// Binary starts with `#b`, hexadecimal starts with `#x` and decimal
    /// starts with any digit.
    Numeral(Numeral<'c>),
    /// A decimal literal.
    Decimal(Decimal<'c>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Literal<'c> {
    /// The kind and associated data of this literal.
    kind: LiteralKind<'c>,
}

impl<'c> From<Numeral<'c>> for Literal<'c> {
    fn from(numeral: Numeral<'c>) -> Self {
        Literal {
            kind: LiteralKind::Numeral(numeral),
        }
    }
}

impl<'c> From<Decimal<'c>> for Literal<'c> {
    fn from(decimal: Decimal<'c>) -> Self {
        Literal {
            kind: LiteralKind::Decimal(decimal),
        }
    }
}

impl<'c> Literal<'c> {
    /// Returns the kind of this literal.
    pub fn kind(&self) -> LiteralKind<'c> {
        self.kind
    }

    /// Creates a new string literal for the given string slice.
    ///
    /// # Note
    ///
    /// The content string slice shall not contain the `"` delimiters.
    ///
    /// # Safety
    ///
    /// This does not check integrity of the input.
    pub fn string(content: &'c str) -> Self {
        Literal {
            kind: LiteralKind::String(content),
        }
    }
}

/// Represents a radix that describes in which number system an associated
/// string represents a numeral value.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Radix {
    /// Binary number system.
    ///
    /// # Note
    ///
    /// In SMTLib2 binary decoded numerals always start with `#b` in
    /// their string representation.
    Binary,
    /// Hexa-decimal number system.
    ///
    /// # Note
    ///
    /// In SMTLib2 hexa-decimal decoded numerals always start with `#x`
    /// in their string representation.
    Hexdec,
    /// Decimal number system.
    ///
    /// # Note
    ///
    /// In SMTLib2 all numerals that have no special prefix are encoded
    /// in the decimal number system.
    Decimal,
}

impl Radix {
    /// Converts the radix into a `u32` value.
    ///
    /// # Note
    ///
    /// This is useful since most standard library features that
    /// interact with radices are in fact operating on raw `u32` values.
    pub fn to_u32(self) -> u32 {
        match self {
            Radix::Binary => 2,
            Radix::Hexdec => 16,
            Radix::Decimal => 10,
        }
    }
}

/// Represents a numeral literal.
///
/// # Note
///
/// This is just a simple string sub slice into a part
/// of the input string that has been found to be a valid
/// numeral literal.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Numeral<'c> {
    /// The string representation of the numeral.
    repr: &'c str,
    /// The radix at which the digits within `repr` are interpreted.
    radix: Radix,
}

/// An error that is raised upon failures upon construction of a numeral from a string slice.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum NumeralError {
    /// Raised when trying to create a numeral from an empty string slice.
    EmptyRepresentation,
    /// Raised when trying to create a numeral from a string slice that is too short
    /// to match the required format, especially with radix annotations.
    InvalidLength,
    /// Raised when encountering an unknown radix identifier.
    /// Known radix identifiers are `#b` (binary) and `#x` hexadecimal.
    UnknownRadixIdentifier,
    /// Raised when encountering an invalid digit for the given radix.
    InvalidDigit,
}

impl std::fmt::Display for NumeralError {
    fn fmt(&self, _f: &mut std::fmt::Formatter) -> std::fmt::Result {
        unimplemented!()
    }
}

impl std::error::Error for NumeralError {
    fn description(&self) -> &str {
        match self {
            NumeralError::EmptyRepresentation => "encountered empty string representation for a numeral literal",
            NumeralError::InvalidLength => "encountered invalid length of numeral literal with radix annotation",
            NumeralError::UnknownRadixIdentifier => "encountered unknown radix identifier",
            NumeralError::InvalidDigit => "encountered invalid digit for the given radix",
        }
    }
}

/// Convenient wrapper around `NumeralError`.
pub type NumeralResult<T> = std::result::Result<T, NumeralError>;

impl<'c> Numeral<'c> {
    fn new(radix: Radix, repr: &'c str) -> Self {
        Numeral { radix, repr }
    }

    /// Creates a new numeral string slice.
    ///
    /// # Errors
    ///
    /// If the given input does not match the expected format.
    pub(crate) fn from_str(repr: &'c str) -> NumeralResult<Self> {
        if repr.is_empty() {
            return Err(NumeralError::EmptyRepresentation);
        }
        let radix = if repr.starts_with('#') {
            if repr.len() < 3 {
                return Err(NumeralError::InvalidLength);
            }
            if repr.starts_with("#b") {
                Radix::Binary
            } else if repr.starts_with("#x") {
                Radix::Hexdec
            } else {
                return Err(NumeralError::UnknownRadixIdentifier); // unknown radix ID: &repr[0..1]
            }
        } else {
            Radix::Decimal
        };
        let offset = match radix {
            Radix::Binary => "#b".len(),
            Radix::Hexdec => "#x".len(),
            Radix::Decimal => 0,
        };
        let raw_repr = &repr[offset..];
        if raw_repr.chars().any(|c| !c.is_digit(radix.to_u32())) {
            return Err(NumeralError::InvalidDigit);
        }
        Ok(Numeral::new(radix, raw_repr))
    }

    /// Returns the value of this numeral.
    ///
    /// # Note
    ///
    /// This either returns the value as `u128` if it fits in or
    /// it returns it as a tuple of the string represenation alongside
    /// its radix.
    pub fn value(&self) -> Either<u128, (&str, Radix)> {
        use std::u128;
        match u128::from_str_radix(self.repr, self.radix.to_u32()) {
            Ok(val) => Either::Left(val),
            Err(_) => Either::Right((self.repr, self.radix)),
        }
    }
}

/// Represents a decimal literal.
///
/// # Note
///
/// This is just a simple string sub slice into a part
/// of the input string that has been found to be a valid
/// decimal literal.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Decimal<'c> {
    /// The string representation of the decimal literal.
    repr: &'c str,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum DecimalError {
    InvalidDigit,
    InvalidLength,
    InvalidFormat,
}

impl std::fmt::Display for DecimalError {
    fn fmt(&self, _f: &mut std::fmt::Formatter) -> std::fmt::Result {
        unimplemented!()
    }
}

impl std::error::Error for DecimalError {
    fn description(&self) -> &str {
        use self::DecimalError::*;
        match self {
            InvalidDigit => "found invalid digits within the decimal literal",
            InvalidLength => "invalid length of the decimal literal representation",
            InvalidFormat => "invalid decimal literal string format",
        }
    }
}

pub type DecimalResult<T> = std::result::Result<T, DecimalError>;

impl<'c> Decimal<'c> {
    /// Creates a new decimal literal from the given string slice.
    ///
    /// # Safety
    ///
    /// This does not check integrity of the input.
    pub unsafe fn from_str_unchecked(repr: &'c str) -> Self {
        {
            let mut split = repr.split('.');
            debug_assert!(split.next().unwrap().chars().all(|c: char| c.is_digit(10)));
            debug_assert!(split.next().unwrap().chars().all(|c: char| c.is_digit(10)));
            debug_assert_eq!(split.next(), None);
        }
        Self { repr }
    }

    /// Creates a new decimal literal from the given string slice.
    ///
    /// # Errors
    ///
    /// If the given input does not match the expected format.
    pub fn from_str(repr: &'c str) -> DecimalResult<Self> {
        if repr.len() < 3 {
            return Err(DecimalError::InvalidLength);
        }
        {
            let mut split = repr.split('.');
            match split.next() {
                None => return Err(DecimalError::InvalidFormat),
                Some(repr) => if repr.chars().any(|c: char| !c.is_digit(10)) {
                    return Err(DecimalError::InvalidDigit);
                },
            }
            match split.next() {
                None => return Err(DecimalError::InvalidFormat),
                Some(repr) => if repr.chars().any(|c: char| !c.is_digit(10)) {
                    return Err(DecimalError::InvalidDigit);
                },
            }
            if let Some(_) = split.next() {
                return Err(DecimalError::InvalidFormat);
            }
        }
        Ok(Self { repr })
    }

    /// Returns the string representation of this decimal literal.
    pub fn str_repr(self) -> &'c str {
        self.repr
    }

    /// Returns a `f32` representation of this decimal literal.
    ///
    /// # Note
    ///
    /// This could lead to information loss during convertion.
    pub fn to_f64(self) -> f64 {
        // Unwrapping here should be safe since `repr` should
        // always represent a parsable string slice.
        self.repr.parse().unwrap()
    }
}

/// Raised when there are errors while building up an expression tree.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum BuildError {
    /// May be raised upon `ExprBuilder::finalize` when there
    /// are still unclosed S-expressions.
    UnclosedSExpr,
    /// Encountered when
    /// - closing an S-expression while there is not a single opened instance of it.
    /// - when a concrete SMT solver expected more arguments
    UnexpectedCloseSExpr,
    /// Raised when encountering an unexpected atom.
    ///
    /// # Note
    ///
    /// Some SMT solvers might require a certain format for their expression trees.
    UnexpectedAtom,
    /// Raised when encountering an unexpected S-expression opening.
    ///
    /// # Note
    ///
    /// Some SMT solvers might require a certain format for their expression trees.
    UnexpectedOpenSExpr,
    /// Raised when encountering an unexpected finalization.
    /// 
    /// # Note
    /// 
    /// This happens when the currently built expression structure is not allow to
    /// be finalized. This is similar as finalization upon existance unclosed expressions.
    UnexpectedFinalize,
}

pub type BuildResult<T> = ::std::result::Result<T, BuildError>;

pub trait ExprBuilder<'s> {
    type Expr;

    /// Introduces the given atom for the current scope.
    fn atom(&mut self, atom: Atom<'s>) -> BuildResult<()>;
    /// Opens a new S-expression scope.
    fn open_sexpr(&mut self) -> BuildResult<()>;
    /// Closes the latest opened S-expression scope.
    fn close_sexpr(&mut self) -> BuildResult<()>;
    /// Consumes the expression builder and returns the built expression.
    fn finalize(self) -> BuildResult<Self::Expr>;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SExprBuilder<'s> {
    s_exprs: Vec<SExpr<'s>>,
}

impl<'s> Default for SExprBuilder<'s> {
    fn default() -> Self {
        SExprBuilder {
            s_exprs: vec![SExpr::default()],
        }
    }
}

impl<'s> ExprBuilder<'s> for SExprBuilder<'s> {
    type Expr = SExpr<'s>;

    fn atom(&mut self, new_atom: Atom<'s>) -> BuildResult<()> {
        self.s_exprs.last_mut().unwrap().push(new_atom);
        Ok(())
    }

    fn open_sexpr(&mut self) -> BuildResult<()> {
        self.s_exprs.push(SExpr::default());
        Ok(())
    }

    fn close_sexpr(&mut self) -> BuildResult<()> {
        let top = self
            .s_exprs
            .pop()
            .ok_or_else(|| BuildError::UnexpectedCloseSExpr)?;
        self.s_exprs
            .last_mut()
            .ok_or_else(|| BuildError::UnexpectedCloseSExpr)?
            .push(top);
        Ok(())
    }

    fn finalize(mut self) -> BuildResult<Self::Expr> {
        if self.s_exprs.len() != 1 {
            return Err(BuildError::UnclosedSExpr)
        }
        Ok(self.s_exprs.pop().unwrap())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum DefaultExprBuilderState<'s> {
    Uninitialized,
    Atom(Atom<'s>),
    SExpr(SExprBuilder<'s>)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefaultExprBuilder<'s> {
    state: DefaultExprBuilderState<'s>
}

impl<'s> DefaultExprBuilder<'s> {
    fn state_mut(&mut self) -> &mut DefaultExprBuilderState<'s> {
        &mut self.state
    }

    fn into_state(self) -> DefaultExprBuilderState<'s> {
        self.state
    }
}

impl<'s> Default for DefaultExprBuilder<'s> {
    fn default() -> Self {
        DefaultExprBuilder{ state: DefaultExprBuilderState::Uninitialized }
    }
}

impl<'s> ExprBuilder<'s> for DefaultExprBuilder<'s> {
    type Expr = Expr<'s>;

    fn atom(&mut self, new_atom: Atom<'s>) -> BuildResult<()> {
        let state = self.state_mut();
        match state {
            DefaultExprBuilderState::Uninitialized => {
                *state = DefaultExprBuilderState::Atom(new_atom);
                Ok(())
            }
            DefaultExprBuilderState::Atom(_) => {
                Err(BuildError::UnexpectedAtom)
            }
            DefaultExprBuilderState::SExpr(builder) => {
                builder.atom(new_atom)
            }
        }
    }

    fn open_sexpr(&mut self) -> BuildResult<()> {
        let state = self.state_mut();
        match state {
            DefaultExprBuilderState::Uninitialized => {
                *state = DefaultExprBuilderState::SExpr(SExprBuilder::default());
                Ok(())
            }
            DefaultExprBuilderState::Atom(_) => {
                Err(BuildError::UnexpectedOpenSExpr)
            }
            DefaultExprBuilderState::SExpr(builder) => {
                builder.open_sexpr()
            }
        }
    }

    fn close_sexpr(&mut self) -> BuildResult<()> {
        match self.state_mut() {
            DefaultExprBuilderState::Uninitialized |
            DefaultExprBuilderState::Atom(_) => {
                Err(BuildError::UnexpectedCloseSExpr)
            }
            DefaultExprBuilderState::SExpr(builder) => {
                builder.close_sexpr()
            }
        }
    }

    fn finalize(self) -> BuildResult<Self::Expr> {
        match self.into_state() {
            DefaultExprBuilderState::Uninitialized => {
                Err(BuildError::UnexpectedFinalize)
            }
            DefaultExprBuilderState::Atom(atom) => {
                Ok(Expr::Atom(atom))
            }
            DefaultExprBuilderState::SExpr(builder) => {
                builder.finalize().map(|s_expr| Expr::SExpr(s_expr))
            }
        }
    }
}
