use crate::{
    expr,
    AnyExpr,
    GeneratedSymbolId,
    NamedSymbolId,
    ty::{
        HasType as _,
        Type,
    },
};
use string_interner::{
    StringInterner,
};
use vec_map::{
    VecMap,
    Entry::{Occupied, Vacant}
};
use std::{
    collections::HashMap,
    sync::{
        atomic::{
            AtomicUsize,
            Ordering
        },
        Arc,
        Mutex
    }
};

mod private {
    /// A simple marker to prevent construction of `Context` instances
    /// from outside this module without its named constructor `Context::arced`.
    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    pub struct PrivateMarker;
}

/// Holds utility and infrastructure data structures that are important
/// for many different parts of the program.
#[derive(Debug)]
pub struct Context {
    /// Access to the symbol interner.
    pub interner: SymbolInterner,
    /// Access to the type map.
    pub symbol_types: TypeMap,
    /// Access to the symbol generator.
    pub symbol_id_gen: SymbolIdGenerator,
    /// Access to the symbol proxy map.
    symbol_proxies: SymbolProxyMap,
    /// A marker to prevent constructing context instances without
    /// its named constructor `Context::arced`.
    marker: private::PrivateMarker
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
    /// - Use `ArcContext` if you need to own the `Context` instance
    ///   because of a non-temporary lifetime or for mutability.
    /// - Use `&'a Context` if you only need read-only access to the `Context`
    ///   and if the lifetime `'a` is small.
    /// - There is no need to use `&'a mut Context` since all accesses
    ///   are thread safe and thus only require a shared borrow.
    pub fn arced() -> ArcContext {
        Arc::new(Context {
            interner: SymbolInterner::default(),
            symbol_types: TypeMap::default(),
            symbol_id_gen: SymbolIdGenerator::default(),
            symbol_proxies: SymbolProxyMap::default(),
            marker: private::PrivateMarker
        })
    }

    /// Associates `self` with the given entity.
    pub fn assoc<T>(&self, entity: T) -> ContextAnd<T> {
        ContextAnd{ entity, ctx: self }
    }

    /// Registers a new proxy for the given expression and returns the proxy symbol.
    pub fn register_proxy(&self, expr: AnyExpr) -> expr::Symbol {
        let proxy_symbol_id = self.symbol_id_gen.gen_id();
        let ty = expr.ty();
        self.symbol_proxies.register(proxy_symbol_id, expr);
        expr::Symbol::from_raw_parts(ty, proxy_symbol_id)
    }
}

/// Generates symbol identifiers of unnamed symbols.
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

impl string_interner::Symbol for NamedSymbolId {
    fn from_usize(val: usize) -> Self {
        NamedSymbolId::from(val)
    }

    fn to_usize(self) -> usize {
        usize::from(self)
    }
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
    #[cfg_attr(feature = "cargo-clippy", allow(clippy::needless_lifetimes))]
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

/// Stores sub-tree expressions that have been temporarily replaced by a newly
/// generated symbol to mitigate exponential copy overhead in stevia for large
/// sub-tree expressions.
#[derive(Debug)]
pub struct SymbolProxyMap {
    /// Access to the internal thread-safe symbol proxy map.
    access: Mutex<HashMap<GeneratedSymbolId, SymbolProxy>>
}

/// The symbol proxy for the replaced expression of a single symbol.
#[derive(Debug, Hash)]
pub struct SymbolProxy {
    /// The expression that has been replaced by the symbol.
    expr: AnyExpr
}

impl SymbolProxy {
    /// Creates a new symbol proxy for the given expression.
    pub(in self) fn new(expr: AnyExpr) -> Self {
        Self{ expr }
    }
}

impl Default for SymbolProxyMap {
    fn default() -> Self {
        SymbolProxyMap{
            access: Mutex::new(HashMap::new())
        }
    }
}

impl SymbolProxyMap {
    /// Registers a new proxy symbol for the given expression.
    pub(in self) fn register(&self, id: GeneratedSymbolId, expr: AnyExpr) {
        self.access
            .lock()
            .unwrap()
            .insert(id, SymbolProxy::new(expr));
    }
}
