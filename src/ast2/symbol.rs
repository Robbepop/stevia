use ast2::prelude::*;

use string_interner;
use string_interner::{StringInterner};

use std::ops::Deref;
use std::marker::PhantomData;
use std::sync::Mutex;

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
    access: Mutex<StringInterner<SymbolName>>
}

unsafe impl Sync for SymbolInterner {}

impl Default for SymbolInterner {
    /// Returns an empty `SymbolInterner`.
    fn default() -> Self {
        SymbolInterner {
            access: Mutex::new(
                StringInterner::with_hasher(Default::default()))
        }
    }
}

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
        let lock_guard = SYMBOL_INTERNER.access.lock().unwrap();
        let interner_ref: &StringInterner<SymbolName> = &lock_guard;
        let interner_ptr: *const StringInterner<SymbolName> = interner_ref as *const StringInterner<SymbolName>;
        unsafe{ (&*interner_ptr).resolve_unchecked(*self) }
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
    /// 
    /// # Errors
    /// 
    /// - If the given type does not match the type cached in the
    ///   type context for symbols.
    pub fn new<S>(name: S, ty: Type) -> Result<Symbol, String>
        where S: Into<String> + AsRef<str>
    {
        let mut lock_guard = SYMBOL_INTERNER.access.lock().unwrap();
        let interner_ref: &mut StringInterner<SymbolName> = &mut lock_guard;
        let interner_ptr: *mut StringInterner<SymbolName> = interner_ref as *mut StringInterner<SymbolName>;
        let sym = unsafe{ &mut *interner_ptr }.get_or_intern(name);
        Ok(Symbol{ty, name: sym})
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

impl From<Symbol> for AnyExpr {
    fn from(symbol: Symbol) -> AnyExpr {
        AnyExpr::Symbol(symbol)
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
