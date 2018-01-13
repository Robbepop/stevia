use ast2::*;

use std::result;

pub mod prelude {
    pub use super::{
        IntoAnyExprOrError,
        ExprTreeFactory,
        ExprTreeBuilder
    };
}

type Result<T> = result::Result<T, String>;

/// Utility trait to be implemented by `AnyExpr` and `Result<AnyExpr>`
/// in order to allow for functions generically taking both types as input.
/// 
/// This allows better ergonomics for users of AST factories when creating
/// new expression trees.
/// 
/// # Note
/// 
/// This feature is explicitely not realized by generically implementing
/// corresponding impls for `From` and `Into` because this system tries to
/// be encapsulated and does not want to spam conversions between types
/// that are not necesary outside of this frame.
pub trait IntoAnyExprOrError {
    /// Converts `self` into the apropriate `Result<AnyExpr>`.
    fn into_any_expr_or_error(self) -> Result<AnyExpr>;
}

impl IntoAnyExprOrError for AnyExpr {
    /// Wraps `self` into `Result<Self>`.
    fn into_any_expr_or_error(self) -> Result<AnyExpr> {
        Ok(self)
    }
}

impl IntoAnyExprOrError for Result<AnyExpr> {
    /// Simply forwards `self` as is.
    fn into_any_expr_or_error(self) -> Result<AnyExpr> {
        self
    }
}

/// An expression tree factory.
/// 
/// This is used to more easily create expression trees with less
/// error handling and less boilerplate code.
/// 
/// The realization via trait allows for different concrete expression
/// tree factories, such as
/// 
/// - A `NaiveExprTreeFactory` that simply creates all input expression trees.
///   This is useful for debugging and shorter running SMT instances where
///   simplifications are not required.
/// - A slightly more advanced `SimplifyingExprTreeFactory` that immediately
///   simplifies its given expression trees for better performance in longer
///   running SMT instances.
pub trait ExprTreeFactory {
    /// Creates a new if-then-else expression with the given condition expression
    /// then case expression and else case expression.
    fn cond(self, cond: AnyExpr, then_case: AnyExpr, else_case: AnyExpr) -> Result<AnyExpr>;

    /// Creates a new boolean variable expression with the given name.
    fn bool_var<S>(self, name: S) -> Result<AnyExpr>
        where S: Into<String> + AsRef<str>;

    /// Creates a new bitvector variable expression with the given name and type.
    fn bitvec_var<S>(self, ty: BitvecTy, name: S) -> Result<AnyExpr>
        where S: Into<String> + AsRef<str>;

    /// Creates a new array variable expression with the given name and type.
    fn array_var<S>(self, ty: ArrayTy, name: S) -> Result<AnyExpr>
        where S: Into<String> + AsRef<str>;

    /// Creates a new constant boolean expression with the given value.
    fn bool_const(self, val: bool) -> Result<AnyExpr>;
    /// Create a new binary and expression with the given child expressions.
    fn and(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr>;
    /// Creates a new n-ary and expression with the given child expressions.
    fn and_n(self, childs: Vec<AnyExpr>) -> Result<AnyExpr>;
    /// Creates a new binary boolean equality expression with the given child expressions.
    fn bool_equals(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr>;
    /// Creates a new n-ary boolean equality expression with the given child expressions.
    fn bool_equals_n(self, childs: Vec<AnyExpr>) -> Result<AnyExpr>;
    /// Creates a new binary implies expression with the given child expressions.
    fn implies(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr>;
    /// Creates a new logical not expression for the given child expression.
    fn not(self, inner: AnyExpr) -> Result<AnyExpr>;
    /// Creates a new binary or expression for the given child expressions.
    fn or(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr>;
    /// Creates a new n-ary or expression for the given child expressions.
    fn or_n(self, childs: Vec<AnyExpr>) -> Result<AnyExpr>;
    /// Creates a new binary or expression for the given child expressions.
    fn xor(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr>;

    /// Creates a new binary array equality expression with the given child expressions.
    fn array_equals(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr>;
    /// Creates a new n-ary array equality expression with the given child expressions.
    fn array_equals_n(self, childs: Vec<AnyExpr>) -> Result<AnyExpr>;
    /// Creates a new binary array read expression on the given array
    /// child expression and at index child expression.
    fn array_read(self, array: AnyExpr, index: AnyExpr) -> Result<AnyExpr>;
    /// Creates a new ternary array write expression on the given array child
    /// expression at index child expression and write value child expression.
    fn array_write(self, array: AnyExpr, index: AnyExpr, value: AnyExpr) -> Result<AnyExpr>;

    /// Creates a new bitvec constant with the given type and value.
    fn bitvec_const<V>(self, ty: BitvecTy, value: V) -> Result<AnyExpr>
        where V: Into<expr::BitvecConst>;
    /// Creates a new unary bitvec negate expression for the given child expression.
    fn bitvec_neg(self, inner: AnyExpr) -> Result<AnyExpr>;
    /// Creates a new binary bitvec add expression with the given child expressions.
    fn bitvec_add(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr>;
    /// Creates a new n-ary bitvec add expression with the given child expressions.
    fn bitvec_add_n(self, childs: Vec<AnyExpr>) -> Result<AnyExpr>;
    /// Creates a new binary bitvec subtract expression for the given child expressions.
    fn bitvec_sub(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr>;
    /// Creates a new binary bitvec multiply expression with the given child expressions.
    fn bitvec_mul(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr>;
    /// Creates a new n-ary bitvec multiply expression with the given child expressions.
    fn bitvec_mul_n(self, childs: Vec<AnyExpr>) -> Result<AnyExpr>;
    /// Creates a new binary bitvec signed division expression for the given child expressions.
    fn bitvec_sdiv(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr>;
    /// Creates a new binary bitvec signed modulo expression for the given child expressions.
    fn bitvec_smod(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr>;
    /// Creates a new binary bitvec signed remainder expression for the given child expressions.
    fn bitvec_srem(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr>;
    /// Creates a new binary bitvec unsigned division expression for the given child expressions.
    fn bitvec_udiv(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr>;
    /// Creates a new binary bitvec unsigned remainder expression for the given child expressions.
    fn bitvec_urem(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr>;

    /// Creates a new unary bitwise not expression for the given child expression.
    fn bitvec_not(self, inner: AnyExpr) -> Result<AnyExpr>;
    /// Create a new binary bitwise and expression with the given child expressions.
    fn bitvec_and(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr>;
    /// Creates a new n-ary bitwise and expression with the given child expressions.
    fn bitvec_and_n(self, childs: Vec<AnyExpr>) -> Result<AnyExpr>;
    /// Create a new binary bitwise or expression with the given child expressions.
    fn bitvec_or(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr>;
    /// Creates a new n-ary bitwise or expression with the given child expressions.
    fn bitvec_or_n(self, childs: Vec<AnyExpr>) -> Result<AnyExpr>;
    /// Creates a new binary bitvec xor expression for the given child expressions.
    fn bitvec_xor(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr>;
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ExprTreeBuilder<F>(F)
    where F: ExprTreeFactory;

impl<F> ExprTreeBuilder<F>
    where F: ExprTreeFactory
{
    /// Returns the factory of this expression tree builder.
    #[inline]
    fn factory(self) -> F {
        self.0
    }

    /// Creates the given binary expression via the given factory.
    /// 
    /// This is just a utility method that helps with unwrapping the given
    /// child expressions before forwarding them to the factory method.
    fn create_binary_expr<L, R, C>(self, constructor: C, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError,
              C: Fn(F, AnyExpr, AnyExpr) -> Result<AnyExpr>
    {
        let lhs = lhs.into_any_expr_or_error()?;
        let rhs = rhs.into_any_expr_or_error()?;
        constructor(self.factory(), lhs, rhs)
    }

    /// Creates the given n-ary expression via the given factory.
    /// 
    /// This is just a utility method that helps with unwrapping the given
    /// child expressions before forwarding them to the factory method.
    fn create_nary_expr<I, E, C>(self, constructor: C, childs: I) -> Result<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError,
              C: Fn(F, Vec<AnyExpr>) -> Result<AnyExpr>
    {
        let childs = childs
            .into_iter()
            .map(|c| c.into_any_expr_or_error())
            .collect::<Result<Vec<AnyExpr>>>()?;
        constructor(self.factory(), childs)
    }
}

/// Generic expressions that can be created by this builder.
impl<F> ExprTreeBuilder<F>
    where F: ExprTreeFactory
{
    /// Creates a new if-then-else expression with the given condition expression
    /// then case expression and else case expression.
    pub fn cond<C, T, E>(self, cond: C, then_case: T, else_case: E) -> Result<AnyExpr>
        where C: IntoAnyExprOrError,
              T: IntoAnyExprOrError,
              E: IntoAnyExprOrError
    {
        let cond = cond.into_any_expr_or_error()?;
        let then_case = then_case.into_any_expr_or_error()?;
        let else_case = else_case.into_any_expr_or_error()?;
        self.factory().cond(cond, then_case, else_case)
    }

    /// Creates a new boolean variable expression with the given name.
    pub fn bool_var<S>(self, name: S) -> Result<AnyExpr>
        where S: Into<String> + AsRef<str>
    {
        self.factory().bool_var(name)
    }

    /// Creates a new bitvector variable expression with the given name.
    pub fn bitvec_var<S>(self, ty: BitvecTy, name: S) -> Result<AnyExpr>
        where S: Into<String> + AsRef<str>
    {
        self.factory().bitvec_var(ty, name)
    }

    /// Creates a new array variable expression with the given name.
    pub fn array_var<S>(self, ty: ArrayTy, name: S) -> Result<AnyExpr>
        where S: Into<String> + AsRef<str>
    {
        self.factory().array_var(ty, name)
    }
}

/// Formula expressions that can be created by this builder.
impl<F> ExprTreeBuilder<F>
    where F: ExprTreeFactory
{
    /// Creates a new constant boolean expression with the given value.
    pub fn bool_const(self, val: bool) -> Result<AnyExpr> {
        self.factory().bool_const(val)
    }

    /// Create a new binary and expression with the given child expressions.
    pub fn and<L, R>(self, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::and, lhs, rhs)
    }

    /// Creates a new n-ary and expression with the given child expressions.
    pub fn and_n<I, E>(self, childs: I) -> Result<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError
    {
        self.create_nary_expr(F::and_n, childs)
    }

    /// Creates a new binary boolean equality expression with the given child expressions.
    pub fn bool_equals<L, R>(self, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bool_equals, lhs, rhs)
    }

    /// Creates a new n-ary boolean equality expression with the given child expressions.
    pub fn bool_equals_n<I, E>(self, childs: I) -> Result<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError
    {
        self.create_nary_expr(F::bool_equals_n, childs)
    }

    /// Creates a new binary implies expression with the given child expressions.
    pub fn implies<L, R>(self, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::implies, lhs, rhs)
    }

    /// Create a new logical not expression for the given child expression.
    pub fn not<E>(self, inner: E) -> Result<AnyExpr>
        where E: IntoAnyExprOrError
    {
        let inner = inner.into_any_expr_or_error()?;
        self.factory().not(inner)
    }

    /// Creates a new binary or expression with the given child expressions.
    pub fn or<L, R>(self, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::or, lhs, rhs)
    }

    /// Creates a new n-ary or expression with the given child expressions.
    pub fn or_n<I, E>(self, childs: I) -> Result<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError
    {
        self.create_nary_expr(F::or_n, childs)
    }

    /// Creates a new binary xor expression with the given child expressions.
    pub fn xor<L, R>(self, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::xor, lhs, rhs)
    }
}

/// Array expressions that can be created by this builder.
impl<F> ExprTreeBuilder<F>
    where F: ExprTreeFactory
{
    /// Creates a new binary array equality expression with the given child expressions.
    pub fn array_equals<L, R>(self, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::array_equals, lhs, rhs)
    }

    /// Creates a new n-ary array equality expression with the given child expressions.
    pub fn array_equals_n<I, E>(self, childs: I) -> Result<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError
    {
        self.create_nary_expr(F::array_equals_n, childs)
    }

    /// Creates a new binary array read expression on the given array
    /// child expression and at index child expression.
    pub fn array_read<A, I>(self, array: A, index: I) -> Result<AnyExpr>
        where A: IntoAnyExprOrError,
              I: IntoAnyExprOrError
    {
        self.create_binary_expr(F::array_read, array, index)
    }

    /// Creates a new ternary array write expression on the given array child
    /// expression at index child expression and write value child expression.
    pub fn array_write<A, I, V>(self, array: A, index: I, value: V) -> Result<AnyExpr>
        where A: IntoAnyExprOrError,
              I: IntoAnyExprOrError,
              V: IntoAnyExprOrError
    {
        let array = array.into_any_expr_or_error()?;
        let index = index.into_any_expr_or_error()?;
        let value = value.into_any_expr_or_error()?;
        self.factory().array_write(array, index, value)
    }
}

/// Arithmetic bitvector expressions that can be created by this builder.
impl<F> ExprTreeBuilder<F>
    where F: ExprTreeFactory
{
    /// Creates a new bitvec constant with the given type and value.
    pub fn bitvec_const<V>(self, ty: BitvecTy, value: V) -> Result<AnyExpr>
        where V: Into<expr::BitvecConst>
    {
        self.factory().bitvec_const(ty, value)
    }

    /// Create a new bitvec negate expression for the given child expression.
    pub fn bitvec_neg<E>(self, inner: E) -> Result<AnyExpr>
        where E: IntoAnyExprOrError
    {
        let inner = inner.into_any_expr_or_error()?;
        self.factory().bitvec_neg(inner)
    }

    /// Creates a new binary bitvec add expression with the given child expressions.
    pub fn bitvec_add<L, R>(self, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_add, lhs, rhs)
    }

    /// Creates a new n-ary bitvec add expression with the given child expressions.
    pub fn bitvec_add_n<I, E>(self, childs: I) -> Result<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError
    {
        self.create_nary_expr(F::bitvec_add_n, childs)
    }

    /// Creates a new binary bitvec subtract expression with the given child expressions.
    pub fn bitvec_sub<L, R>(self, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_sub, lhs, rhs)
    }

    /// Creates a new binary bitvec multiply expression with the given child expressions.
    pub fn bitvec_mul<L, R>(self, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_mul, lhs, rhs)
    }

    /// Creates a new n-ary bitvec multiply expression with the given child expressions.
    pub fn bitvec_mul_n<I, E>(self, childs: I) -> Result<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError
    {
        self.create_nary_expr(F::bitvec_mul_n, childs)
    }

    /// Creates a new binary signed division expression with the given child expressions.
    pub fn bitvec_sdiv<L, R>(self, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_sdiv, lhs, rhs)
    }

    /// Creates a new binary signed modulo expression with the given child expressions.
    pub fn bitvec_smod<L, R>(self, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_smod, lhs, rhs)
    }

    /// Creates a new binary signed remainder expression with the given child expressions.
    pub fn bitvec_srem<L, R>(self, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_srem, lhs, rhs)
    }

    /// Creates a new binary unsigned division expression with the given child expressions.
    pub fn bitvec_udiv<L, R>(self, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_udiv, lhs, rhs)
    }

    /// Creates a new binary unsigned remainder expression with the given child expressions.
    pub fn bitvec_urem<L, R>(self, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_urem, lhs, rhs)
    }
}

/// Bitwise bitvector expressions that can be created by this builder.
impl<F> ExprTreeBuilder<F>
    where F: ExprTreeFactory
{
    /// Creates a new binary bitwise and expression with the given child expressions.
    pub fn bitvec_and<L, R>(self, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_and, lhs, rhs)
    }

    /// Creates a new n-ary bitwise and expression with the given child expressions.
    pub fn bitvec_and_n<I, E>(self, childs: I) -> Result<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError
    {
        self.create_nary_expr(F::bitvec_and_n, childs)
    }

    /// Creates a new binary bitwise or expression with the given child expressions.
    pub fn bitvec_or<L, R>(self, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_or, lhs, rhs)
    }

    /// Creates a new n-ary bitwise or expression with the given child expressions.
    pub fn bitvec_or_n<I, E>(self, childs: I) -> Result<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError
    {
        self.create_nary_expr(F::bitvec_or_n, childs)
    }

    /// Create a new bitwise not expression for the given child expression.
    pub fn bitvec_not<E>(self, inner: E) -> Result<AnyExpr>
        where E: IntoAnyExprOrError
    {
        let inner = inner.into_any_expr_or_error()?;
        self.factory().bitvec_not(inner)
    }

    /// Creates a new binary bitwise xor expression with the given child expressions.
    pub fn bitvec_xor<L, R>(self, lhs: L, rhs: R) -> Result<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_xor, lhs, rhs)
    }
}
