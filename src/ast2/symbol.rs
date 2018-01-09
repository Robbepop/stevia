use ast2::prelude::*;

use string_interner;
use string_interner::{StringInterner};

use std::ops::Deref;
use std::cell::UnsafeCell;
use std::marker::PhantomData;

pub mod prelude {
    pub use super::{
        SymbolName,
        Symbol
    };
}

lazy_static! {
    /// The `StringInterner` specialized for interning symbol identifiers.
    static ref SYMBOL_INTERNER: SymbolInterner = SymbolInterner::default();
}

/// A `SymbolInterner` is a lazy-static optimized `StringInterner` for `SymbolName`
/// symbols used exclusively by `Symbol` expressions.
/// 
/// It requires mutable static access thus it is wrapped in an `UnsafeCell`.
struct SymbolInterner {
    cell: UnsafeCell<StringInterner<SymbolName>>,
}

impl Default for SymbolInterner {
    /// Returns an empty `SymbolInterner`.
    fn default() -> Self {
        SymbolInterner {
            cell: UnsafeCell::new(StringInterner::with_hasher(Default::default())),
        }
    }
}

unsafe impl Sync for SymbolInterner {}

/// Represents an identifier stored in a `StringInterner`
/// for efficient storage and access.
#[derive(Debug, Copy, Clone, PartialEq, PartialOrd, Ord, Eq, Hash)]
pub struct SymbolName{
    val: usize,
    not_send_sync: PhantomData<*const ()>
}

impl string_interner::Symbol for SymbolName {
    /// Returns a `SymbolName` from the given `usize`.
    #[inline]
    fn from_usize(val: usize) -> SymbolName {
        SymbolName{
            val,
            not_send_sync: PhantomData
        }
    }

    /// Converts this `SymbolName` to its associated `usize`.
    #[inline]
    fn to_usize(self) -> usize {
        self.val
    }
}

impl Deref for SymbolName {
    type Target = str;

    /// Dereferences this `SymbolName` to its associated `str`.
    /// 
    /// This is possible by having a dedicated `StringInterner` only for interning
    /// symbol names that is static for this library on execution.
    fn deref(&self) -> &Self::Target {
        let interner = SYMBOL_INTERNER.cell.get();
        let interner = unsafe{&*interner};
        unsafe{ interner.resolve_unchecked(*self) }
    }
}

/// The `Symbol` represents named variables such as "x" and "foo" in an 
/// SMT expression.
/// 
/// For this it stores its name efficiently via string interning.
/// It also has an associated type which it must not change during its lifetime.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Symbol {
    pub name: SymbolName,
    pub ty: Type
}

impl Symbol {
    /// Returns a new `Symbol` for the given name and type.
    pub fn new<S>(name: S, ty: Type) -> Symbol
        where S: Into<String> + AsRef<str>
    {
        let interner = SYMBOL_INTERNER.cell.get();
        let interner = unsafe{&mut *interner};
        Symbol{ty, name: interner.get_or_intern(name)}
    }
}

impl HasType for Symbol {
    fn ty(&self) -> Type {
        self.ty
    }
}

impl HasKind for Symbol {
    fn kind(&self) -> ExprKind {
        ExprKind::Symbol
    }
}

impl HasArity for Symbol {
    fn arity(&self) -> usize {
        0
    }
}

impl From<Symbol> for Expr {
    fn from(symbol: Symbol) -> Expr {
        Expr::Symbol(symbol)
    }
}

impl Childs for Symbol {
    fn childs(&self) -> ChildsIter {
        ChildsIter::none()
    }
}

impl ChildsMut for Symbol {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::none()
    }
}

impl IntoChilds for Symbol {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::none()
    }
}
