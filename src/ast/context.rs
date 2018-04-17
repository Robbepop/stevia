use ast::prelude::*;

use string_interner::{
    StringInterner,
};
use vec_map::{
    VecMap,
    Entry::{Occupied, Vacant}
};
use std::sync::{
    atomic::{
        AtomicUsize,
        Ordering
    },
    Arc,
    Mutex
};

/// Holds utility and infrastructure data structures that are important
/// for many different parts of the program.
#[derive(Debug)]
pub struct Context {
    /// Access to the symbol interner.
    pub interner: SymbolInterner,
    /// Access to the type map.
    pub symbol_types: TypeMap,
    /// Access to the symbol generator.
    pub symbol_id_gen: SymbolIdGenerator
}

/// An generic entity and its associated context.
#[derive(Debug, Copy, Clone)]
pub struct ContextAnd<'ctx, T>{
    /// The associated entity.
    pub entity: T,
    /// The associated context.
    pub ctx: &'ctx Context
}

/// Atomically ref-counted context.
pub type ArcContext = Arc<Context>;

impl Context {
    /// Returns a new `Context` stored within an `Arc` with default constructed internals.
    ///
    /// # How to use `Context` instances
    ///
    /// - Use `Arc<Context>` if you need to own the `Context` instance
    ///   because of a non-temporary lifetime or for mutability.
    /// - Use `&'a Context` if you only need read-only access to the `Context`
    ///   and if the lifetime `'a` is small.
    /// - Use `&'a mut Context` if you need mutable access to the `Context`
    ///   and if the lifetime `'a` is small.
    pub fn arced() -> Arc<Self> {
        Arc::new(Context {
            interner: SymbolInterner::default(),
            symbol_types: TypeMap::default(),
            symbol_id_gen: SymbolIdGenerator::default()
        })
    }

    /// Associates `self` with the given entity.
    pub fn assoc<T>(&self, entity: T) -> ContextAnd<T> {
        ContextAnd{ entity, ctx: self }
    }
}

#[derive(Debug)]
pub struct SymbolIdGenerator {
    current: AtomicUsize
}

impl Default for SymbolIdGenerator {
    /// Returns an new `SymbolIdGenerator`.
    fn default() -> Self {
        SymbolIdGenerator {
            current: AtomicUsize::new(0)
        }
    }
}

impl SymbolIdGenerator {
    /// Returns the next generated symbol id.
    pub fn gen_id(&self) -> GeneratedSymbolId {
        // TODO 2018-04-17: decide if we can relax the ordering in this place a bit.
        self.current.fetch_add(1, Ordering::SeqCst).into()
    }
}

/// Stores mappings between symbol names and types.
///
/// Allows for thread-safe access.
///
/// This is used to verify type integrity between symbols of the same name.
#[derive(Debug)]
pub struct TypeMap {
    /// Access to the internal thread-safe `Map` of `Type`.
    access: Mutex<VecMap<Type>>,
}

impl Default for TypeMap {
    /// Returns an empty `TypeMap`.
    fn default() -> Self {
        TypeMap {
            access: Mutex::new(VecMap::new()),
        }
    }
}

impl TypeMap {
    /// Insert an associtation between the given symbol name and the given type.
    ///
    /// This either ...
    ///
    /// - returns the already existing associated type to the given symbol name
    ///   if existent.
    /// - successfully creates an association between given entities if there does
    ///   not exist an association for the given symbol name already. Returns `None`
    ///   in this case.
    ///
    /// # Note
    ///
    /// Does not insert into the `TypeMap` if there already exists an association
    /// for the given symbol name.
    pub fn insert_or_get<T>(&self, name: NamedSymbolId, ty: T) -> Option<Type>
    where
        T: Into<Type>
    {
        let mut locked_map = self.access.lock().unwrap();
        match locked_map.entry(name.raw_repr()) {
            Occupied(occupied) => Some(*occupied.get()),
            Vacant(vacant) => {
                vacant.insert(ty.into());
                None
            }
        }
    }

    /// Returns the type associated to the given named symbol ID.
    /// 
    /// Returns `None` if there exists no associated type for the given name.
    pub fn get(&self, name: NamedSymbolId) -> Option<Type> {
        self.access.lock().unwrap().get(name.raw_repr()).cloned()
    }
}

/// A `SymbolInterner` is a `StringInterner` optimized for `Symbol` expressions.
///
/// Allows for thread-safe access.
#[derive(Debug)]
pub struct SymbolInterner {
    /// Access to the internal thread-safe `StringInterner`.
    access: Mutex<StringInterner<NamedSymbolId>>,
}

unsafe impl Sync for SymbolInterner {}

impl Default for SymbolInterner {
    fn default() -> Self {
        SymbolInterner {
            access: Mutex::new(StringInterner::new()),
        }
    }
}

impl SymbolInterner {
    /// Interns the given string within the `SymbolInterner` and returns
    /// the associated `Symbol` or returns an already associated `Symbol` for the
    /// given string.
    pub fn intern_or_get<S>(&self, name: S) -> NamedSymbolId
    where
        S: Into<String> + AsRef<str>,
    {
        self.access.lock().unwrap().get_or_intern(name)
    }

    /// Returns the associated string representation for the given symbol name.
    #[cfg_attr(feature = "cargo-clippy", allow(needless_lifetimes))]
    pub fn resolve_symbol<'a>(&'a self, name: NamedSymbolId) -> Option<&'a str> {
        self.access
            .lock()
            .unwrap()
            .resolve(name)
            .map(|resolved| unsafe{
                // Correct the lifetime of the resolved str to be the lifetime of self.
                // Otherwise this would have incorrectly been the lifetime of the lock guard.
                //
                // For soundness this depends on two things:
                // - The `SymbolInterner` and its underlying `StringInterner` are append-only.
                // - Already inserted `String` instances cannot be modified afterwards.
                &* (resolved as *const str)
            })
    }
}
