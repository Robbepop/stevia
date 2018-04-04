use ast::prelude::*;

use string_interner;
use string_interner::{StringInterner};
use vec_map::{VecMap};

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
    /// The `VecMap` that maps from `SymbolName`s to actual values if existant.
    static ref TYPE_MAP: TypeMap = TypeMap::default();
}

#[derive(Debug)]
struct TypeMap {
    access: Mutex<VecMap<Type>>
}

impl Default for TypeMap {
    /// Returns an empty `TypeMap`.
    fn default() -> Self {
        TypeMap {
            access: Mutex::new(
                VecMap::new()
            )
        }
    }
}

impl TypeMap {
    /// Checks if for the given name the given type is already stored in the
    /// type map or otherwise inserts the given type into it.
    /// 
    /// This is used to verify that symbols with the same identifier are
    /// associated to the same underlying type.
    fn check_or_intern(&self, name: SymbolName, ty: Type) -> ExprResult<()> {
        use string_interner::Symbol;
        use vec_map::Entry::{Vacant, Occupied};
        let mut locked_map = TYPE_MAP.access.lock().unwrap();
        match locked_map.entry(name.to_usize()) {
            Vacant(slot) => {
                slot.insert(ty);
            }
            Occupied(value) => {
                expect_matching_symbol_type(*value.get(), ty, name)?;
            }
        };
        Ok(())
    }
}

/// A `SymbolInterner` is a lazy-static optimized `StringInterner` for `SymbolName`
/// symbols used exclusively by `Symbol` expressions.
/// 
/// It requires mutable static access thus it is wrapped in an `UnsafeCell`.
#[derive(Debug)]
struct SymbolInterner {
    access: Mutex<StringInterner<SymbolName>>
}

unsafe impl Sync for SymbolInterner {}

impl SymbolInterner {
    fn get_or_intern<S>(&self, name: S) -> SymbolName
        where S: Into<String> + AsRef<str>
    {
        self.access.lock().unwrap().get_or_intern(name)
    }

    fn resolve_symbol(&self, name: SymbolName) -> &'static str {
        let lock_guard = SYMBOL_INTERNER.access.lock().unwrap();
        let resolved = unsafe{ lock_guard.resolve_unchecked(name) };
        unsafe{ &* (resolved as *const str) }
    }
}

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
        SYMBOL_INTERNER.resolve_symbol(*self)
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
    pub fn new<S>(identifier: S, ty: Type) -> ExprResult<Symbol>
        where S: Into<String> + AsRef<str>
    {
        let name = SYMBOL_INTERNER.get_or_intern(identifier);
        TYPE_MAP.check_or_intern(name, ty)?;
        Ok(Symbol{ty, name})
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

impl Children for Symbol {
    fn children(&self) -> ChildrenIter {
        ChildrenIter::none()
    }
}

impl ChildrenMut for Symbol {
    fn children_mut(&mut self) -> ChildrenIterMut {
        ChildrenIterMut::none()
    }
}

impl IntoChildren for Symbol {
    fn into_children(self) -> IntoChildrenIter {
        IntoChildrenIter::none()
    }
}
