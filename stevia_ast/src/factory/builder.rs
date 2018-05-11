use crate::prelude::*;

/// Utility trait to be implemented by `AnyExpr` and `ExprResult<AnyExpr>`
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
    /// Converts `self` into the apropriate `ExprResult<AnyExpr>`.
    fn into_any_expr_or_error(self) -> ExprResult<AnyExpr>;
}

impl IntoAnyExprOrError for AnyExpr {
    /// Wraps `self` into `Result<Self>`.
    fn into_any_expr_or_error(self) -> ExprResult<AnyExpr> {
        Ok(self)
    }
}

impl IntoAnyExprOrError for ExprResult<AnyExpr> {
    /// Simply forwards `self` as is.
    fn into_any_expr_or_error(self) -> ExprResult<AnyExpr> {
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
    fn cond(&self, cond: AnyExpr, then_case: AnyExpr, else_case: AnyExpr) -> ExprResult<AnyExpr>;

    /// Creates a new boolean variable expression with the given name.
    fn bool_var<S>(&self, name: S) -> ExprResult<AnyExpr>
        where S: Into<String> + AsRef<str>;

    /// Creates a new bitvector variable expression with the given name and type.
    fn bitvec_var<S>(&self, ty: BitvecTy, name: S) -> ExprResult<AnyExpr>
        where S: Into<String> + AsRef<str>;

    /// Creates a new array variable expression with the given name and type.
    fn array_var<S>(&self, ty: ArrayTy, name: S) -> ExprResult<AnyExpr>
        where S: Into<String> + AsRef<str>;

    /// Creates a new constant boolean expression with the given value.
    fn bool_const(&self, val: bool) -> ExprResult<AnyExpr>;
    /// Create a new binary and expression with the given child expressions.
    fn and(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new n-ary and expression with the given child expressions.
    fn and_n(&self, children: Vec<AnyExpr>) -> ExprResult<AnyExpr>;
    /// Creates a new binary boolean equality expression with the given child expressions.
    fn bool_equals(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new n-ary boolean equality expression with the given child expressions.
    fn bool_equals_n(&self, children: Vec<AnyExpr>) -> ExprResult<AnyExpr>;
    /// Creates a new binary implies expression with the given child expressions.
    fn implies(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new logical not expression for the given child expression.
    fn not(&self, inner: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new binary or expression for the given child expressions.
    fn or(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new n-ary or expression for the given child expressions.
    fn or_n(&self, children: Vec<AnyExpr>) -> ExprResult<AnyExpr>;
    /// Creates a new binary or expression for the given child expressions.
    fn xor(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;

    /// Creates a new binary array read expression on the given array
    /// child expression and at index child expression.
    fn array_read(&self, array: AnyExpr, index: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new ternary array write expression on the given array child
    /// expression at index child expression and write value child expression.
    fn array_write(&self, array: AnyExpr, index: AnyExpr, value: AnyExpr) -> ExprResult<AnyExpr>;

    /// Creates a new binary bitvec equality expression with the given child expressions.
    fn bitvec_equals(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new n-ary bitvec equality expression with the given child expressions.
    fn bitvec_equals_n(&self, children: Vec<AnyExpr>) -> ExprResult<AnyExpr>;
    /// Creates a new bitvec constant with the given type and value.
    fn bitvec_const<V>(&self, ty: BitvecTy, value: V) -> ExprResult<AnyExpr>
        where V: Into<expr::BitvecConst>;
    /// Creates a new unary bitvec negate expression for the given child expression.
    fn bitvec_neg(&self, inner: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new binary bitvec add expression with the given child expressions.
    fn bitvec_add(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new n-ary bitvec add expression with the given child expressions.
    fn bitvec_add_n(&self, children: Vec<AnyExpr>) -> ExprResult<AnyExpr>;
    /// Creates a new binary bitvec subtract expression for the given child expressions.
    fn bitvec_sub(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new binary bitvec multiply expression with the given child expressions.
    fn bitvec_mul(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new n-ary bitvec multiply expression with the given child expressions.
    fn bitvec_mul_n(&self, children: Vec<AnyExpr>) -> ExprResult<AnyExpr>;
    /// Creates a new binary bitvec signed division expression for the given child expressions.
    fn bitvec_sdiv(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new binary bitvec signed modulo expression for the given child expressions.
    fn bitvec_smod(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new binary bitvec signed remainder expression for the given child expressions.
    fn bitvec_srem(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new binary bitvec unsigned division expression for the given child expressions.
    fn bitvec_udiv(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new binary bitvec unsigned remainder expression for the given child expressions.
    fn bitvec_urem(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;

    /// Creates a new unary bitwise not expression for the given child expression.
    fn bitvec_not(&self, inner: AnyExpr) -> ExprResult<AnyExpr>;
    /// Create a new binary bitwise and expression with the given child expressions.
    fn bitvec_and(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new n-ary bitwise and expression with the given child expressions.
    fn bitvec_and_n(&self, children: Vec<AnyExpr>) -> ExprResult<AnyExpr>;
    /// Create a new binary bitwise or expression with the given child expressions.
    fn bitvec_or(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new n-ary bitwise or expression with the given child expressions.
    fn bitvec_or_n(&self, children: Vec<AnyExpr>) -> ExprResult<AnyExpr>;
    /// Creates a new binary bitvec xor expression for the given child expressions.
    fn bitvec_xor(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;

    /// Creates a new binary bitvector concatenate expression with the given child expressions.
    fn bitvec_concat(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new unary bitvector extraction expression for the given child expression
    /// and the given hi and lo bit positions.
    fn bitvec_extract_hi_lo(&self, hi: usize, lo: usize, inner: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new unary bitvector sign-extension expression for the given child expression
    /// to the given bit width bits.
    fn bitvec_sext(&self, target_width: BitWidth, inner: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new unary bitvector zero-extension expression for the given child expression
    /// to the given bit width bits.
    fn bitvec_zext(&self, target_width: BitWidth, inner: AnyExpr) -> ExprResult<AnyExpr>;

    /// Creates a new binary signed greater-than-or-equals expression with the given child expressions.
    fn bitvec_sge(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new binary signed greater-than expression with the given child expressions.
    fn bitvec_sgt(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new binary signed less-than-or-equals expression with the given child expressions.
    fn bitvec_sle(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new binary signed less-than expression with the given child expressions.
    fn bitvec_slt(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new binary unsigned greater-than-or-equals expression with the given child expressions.
    fn bitvec_uge(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new binary unsigned greater-than expression with the given child expressions.
    fn bitvec_ugt(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new binary unsigned less-than-or-equals expression with the given child expressions.
    fn bitvec_ule(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new binary unsigned less-than expression with the given child expressions.
    fn bitvec_ult(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;

    /// Creates a new binary arithmetical right-shift expression with the given child expressions.
    fn bitvec_ashr(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new binary logical right-shift expression with the given child expressions.
    fn bitvec_lshr(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
    /// Creates a new binary left-shift expression with the given child expressions.
    fn bitvec_shl(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr>;
}

/// Interface for expression tree creation.
/// 
/// This wraps an `ExprTreeFactory` and uses it internally to construct
/// the expression tree.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ExprTreeBuilder<F>(F)
    where F: ExprTreeFactory;

impl<F> ExprTreeBuilder<F>
    where F: ExprTreeFactory
{
    pub fn new(factory: F) -> ExprTreeBuilder<F> {
        ExprTreeBuilder(factory)
    }
}

impl<F> ExprTreeBuilder<F>
    where F: ExprTreeFactory
{
    /// Returns the factory of this expression tree builder.
    #[inline]
    fn factory(&self) -> &F {
        &self.0
    }

    /// Creates the given binary expression via the given factory.
    /// 
    /// This is just a utility method that helps with unwrapping the given
    /// child expressions before forwarding them to the factory method.
    fn create_binary_expr<L, R, C>(&self, constructor: C, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError,
              C: Fn(&F, AnyExpr, AnyExpr) -> ExprResult<AnyExpr>
    {
        let lhs = lhs.into_any_expr_or_error()?;
        let rhs = rhs.into_any_expr_or_error()?;
        constructor(&self.factory(), lhs, rhs)
    }

    /// Creates the given n-ary expression via the given factory.
    /// 
    /// This is just a utility method that helps with unwrapping the given
    /// child expressions before forwarding them to the factory method.
    fn create_nary_expr<I, E, C>(&self, constructor: C, children: I) -> ExprResult<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError,
              C: Fn(&F, Vec<AnyExpr>) -> ExprResult<AnyExpr>
    {
        let children = children
            .into_iter()
            .map(|c| c.into_any_expr_or_error())
            .collect::<ExprResult<Vec<AnyExpr>>>()?;
        constructor(&self.factory(), children)
    }
}

/// Generic expressions that can be created by this builder.
impl<F> ExprTreeBuilder<F>
    where F: ExprTreeFactory
{
    /// Creates a new if-then-else expression with the given condition expression
    /// then case expression and else case expression.
    pub fn cond<C, T, E>(&self, cond: C, then_case: T, else_case: E) -> ExprResult<AnyExpr>
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
    pub fn bool_var<S>(&self, name: S) -> ExprResult<AnyExpr>
        where S: Into<String> + AsRef<str>
    {
        self.factory().bool_var(name)
    }

    /// Creates a new bitvector variable expression with the given name.
    pub fn bitvec_var<S>(&self, ty: BitvecTy, name: S) -> ExprResult<AnyExpr>
        where S: Into<String> + AsRef<str>
    {
        self.factory().bitvec_var(ty, name)
    }

    /// Creates a new array variable expression with the given name.
    pub fn array_var<S>(&self, ty: ArrayTy, name: S) -> ExprResult<AnyExpr>
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
    pub fn bool_const(&self, val: bool) -> ExprResult<AnyExpr> {
        self.factory().bool_const(val)
    }

    /// Create a new binary and expression with the given child expressions.
    pub fn and<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::and, lhs, rhs)
    }

    /// Creates a new n-ary and expression with the given child expressions.
    pub fn and_n<I, E>(&self, children: I) -> ExprResult<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError
    {
        self.create_nary_expr(F::and_n, children)
    }

    /// Creates a new binary boolean equality expression with the given child expressions.
    pub fn bool_equals<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bool_equals, lhs, rhs)
    }

    /// Creates a new n-ary boolean equality expression with the given child expressions.
    pub fn bool_equals_n<I, E>(&self, children: I) -> ExprResult<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError
    {
        self.create_nary_expr(F::bool_equals_n, children)
    }

    /// Creates a new binary implies expression with the given child expressions.
    pub fn implies<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::implies, lhs, rhs)
    }

    /// Create a new logical not expression for the given child expression.
    pub fn not<E>(&self, inner: E) -> ExprResult<AnyExpr>
        where E: IntoAnyExprOrError
    {
        let inner = inner.into_any_expr_or_error()?;
        self.factory().not(inner)
    }

    /// Creates a new binary or expression with the given child expressions.
    pub fn or<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::or, lhs, rhs)
    }

    /// Creates a new n-ary or expression with the given child expressions.
    pub fn or_n<I, E>(&self, children: I) -> ExprResult<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError
    {
        self.create_nary_expr(F::or_n, children)
    }

    /// Creates a new binary xor expression with the given child expressions.
    pub fn xor<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
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
    /// Creates a new binary array read expression on the given array
    /// child expression and at index child expression.
    pub fn array_read<A, I>(&self, array: A, index: I) -> ExprResult<AnyExpr>
        where A: IntoAnyExprOrError,
              I: IntoAnyExprOrError
    {
        self.create_binary_expr(F::array_read, array, index)
    }

    /// Creates a new ternary array write expression on the given array child
    /// expression at index child expression and write value child expression.
    pub fn array_write<A, I, V>(&self, array: A, index: I, value: V) -> ExprResult<AnyExpr>
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
    pub fn bitvec_const<V>(&self, ty: BitvecTy, value: V) -> ExprResult<AnyExpr>
        where V: Into<expr::BitvecConst>
    {
        self.factory().bitvec_const(ty, value)
    }

    /// Create a new bitvec negate expression for the given child expression.
    pub fn bitvec_neg<E>(&self, inner: E) -> ExprResult<AnyExpr>
        where E: IntoAnyExprOrError
    {
        let inner = inner.into_any_expr_or_error()?;
        self.factory().bitvec_neg(inner)
    }

    /// Creates a new binary bitvec add expression with the given child expressions.
    pub fn bitvec_add<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_add, lhs, rhs)
    }

    /// Creates a new n-ary bitvec add expression with the given child expressions.
    pub fn bitvec_add_n<I, E>(&self, children: I) -> ExprResult<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError
    {
        self.create_nary_expr(F::bitvec_add_n, children)
    }

    /// Creates a new binary bitvec subtract expression with the given child expressions.
    pub fn bitvec_sub<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_sub, lhs, rhs)
    }

    /// Creates a new binary bitvec multiply expression with the given child expressions.
    pub fn bitvec_mul<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_mul, lhs, rhs)
    }

    /// Creates a new n-ary bitvec multiply expression with the given child expressions.
    pub fn bitvec_mul_n<I, E>(&self, children: I) -> ExprResult<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError
    {
        self.create_nary_expr(F::bitvec_mul_n, children)
    }

    /// Creates a new binary signed division expression with the given child expressions.
    pub fn bitvec_sdiv<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_sdiv, lhs, rhs)
    }

    /// Creates a new binary signed modulo expression with the given child expressions.
    pub fn bitvec_smod<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_smod, lhs, rhs)
    }

    /// Creates a new binary signed remainder expression with the given child expressions.
    pub fn bitvec_srem<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_srem, lhs, rhs)
    }

    /// Creates a new binary unsigned division expression with the given child expressions.
    pub fn bitvec_udiv<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_udiv, lhs, rhs)
    }

    /// Creates a new binary unsigned remainder expression with the given child expressions.
    pub fn bitvec_urem<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
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
    pub fn bitvec_and<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_and, lhs, rhs)
    }

    /// Creates a new n-ary bitwise and expression with the given child expressions.
    pub fn bitvec_and_n<I, E>(&self, children: I) -> ExprResult<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError
    {
        self.create_nary_expr(F::bitvec_and_n, children)
    }

    /// Creates a new binary bitwise or expression with the given child expressions.
    pub fn bitvec_or<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_or, lhs, rhs)
    }

    /// Creates a new n-ary bitwise or expression with the given child expressions.
    pub fn bitvec_or_n<I, E>(&self, children: I) -> ExprResult<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError
    {
        self.create_nary_expr(F::bitvec_or_n, children)
    }

    /// Create a new bitwise not expression for the given child expression.
    pub fn bitvec_not<E>(&self, inner: E) -> ExprResult<AnyExpr>
        where E: IntoAnyExprOrError
    {
        let inner = inner.into_any_expr_or_error()?;
        self.factory().bitvec_not(inner)
    }

    /// Creates a new binary bitwise xor expression with the given child expressions.
    pub fn bitvec_xor<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_xor, lhs, rhs)
    }
}

/// Casting bitvector expressions that can be created by this builder.
impl<F> ExprTreeBuilder<F>
    where F: ExprTreeFactory
{
    /// Creates a new binary bitvector concatenate expression with the given child expressions.
    pub fn bitvec_concat<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_concat, lhs, rhs)
    }

    /// Creates a new unary bitvector extraction expression for the given child expression
    /// and the given hi and lo bit positions.
    pub fn bitvec_extract_hi_lo<E>(&self, hi: usize, lo: usize, inner: E) -> ExprResult<AnyExpr>
        where E: IntoAnyExprOrError
    {
        let inner = inner.into_any_expr_or_error()?;
        self.factory().bitvec_extract_hi_lo(hi, lo, inner)
    }

    /// Creates a new unary bitvector sign-extension expression for the given child expression
    /// to the given bit width bits.
    pub fn bitvec_sext<E>(&self, target_width: BitWidth, inner: E) -> ExprResult<AnyExpr>
        where E: IntoAnyExprOrError
    {
        let inner = inner.into_any_expr_or_error()?;
        self.factory().bitvec_sext(target_width, inner)
    }

    /// Creates a new unary bitvector zero-extension expression for the given child expression
    /// to the given bit width bits.
    pub fn bitvec_zext<E>(&self, target_width: BitWidth, inner: E) -> ExprResult<AnyExpr>
        where E: IntoAnyExprOrError
    {
        let inner = inner.into_any_expr_or_error()?;
        self.factory().bitvec_zext(target_width, inner)
    }
}

/// Comparison bitvector expressions that can be created by this builder.
impl<F> ExprTreeBuilder<F>
    where F: ExprTreeFactory
{
    /// Creates a new binary bitvector equality expression with the given child expressions.
    pub fn bitvec_equals<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_equals, lhs, rhs)
    }

    /// Creates a new n-ary bitvector equality expression with the given child expressions.
    pub fn bitvec_equals_n<I, E>(&self, children: I) -> ExprResult<AnyExpr>
        where I: IntoIterator<Item=E>,
              E: IntoAnyExprOrError
    {
        self.create_nary_expr(F::bitvec_equals_n, children)
    }

    /// Creates a new binary signed greater-than-or-equals expression with the given child expressions.
    pub fn bitvec_sge<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_sge, lhs, rhs)
    }

    /// Creates a new binary signed greater-than expression with the given child expressions.
    pub fn bitvec_sgt<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_sgt, lhs, rhs)
    }

    /// Creates a new binary signed less-than-or-equals expression with the given child expressions.
    pub fn bitvec_sle<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_sle, lhs, rhs)
    }

    /// Creates a new binary signed less-than expression with the given child expressions.
    pub fn bitvec_slt<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_slt, lhs, rhs)
    }

    /// Creates a new binary unsigned greater-than-or-equals expression with the given child expressions.
    pub fn bitvec_uge<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_uge, lhs, rhs)
    }

    /// Creates a new binary unsigned greater-than expression with the given child expressions.
    pub fn bitvec_ugt<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_ugt, lhs, rhs)
    }

    /// Creates a new binary unsigned less-than-or-equals expression with the given child expressions.
    pub fn bitvec_ule<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_ule, lhs, rhs)
    }

    /// Creates a new binary unsigned less-than expression with the given child expressions.
    pub fn bitvec_ult<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_ult, lhs, rhs)
    }
}

/// Shift bitvector expressions that can be created by this builder.
impl<F> ExprTreeBuilder<F>
    where F: ExprTreeFactory
{
    /// Creates a new binary arithmetical right-shift expression with the given child expressions.
    pub fn bitvec_ashr<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_ashr, lhs, rhs)
    }

    /// Creates a new binary logical right-shift expression with the given child expressions.
    pub fn bitvec_lshr<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_lshr, lhs, rhs)
    }

    /// Creates a new binary left-shift expression with the given child expressions.
    pub fn bitvec_shl<L, R>(&self, lhs: L, rhs: R) -> ExprResult<AnyExpr>
        where L: IntoAnyExprOrError,
              R: IntoAnyExprOrError
    {
        self.create_binary_expr(F::bitvec_shl, lhs, rhs)
    }
}
