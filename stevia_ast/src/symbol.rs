use crate::prelude::*;

use std::fmt;

/// Symbol ID (identificator).
///
/// A symbol ID either represents a named or generated symbol.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SymbolId {
    /// A named symbol ID.
    Named(NamedSymbolId),
    /// A generated symbol ID.
    Generated(GeneratedSymbolId),
}

/// Identificator of named symbol expressions.
///
/// Named symbol IDs can be used in combination with their associated contexts
/// to resolve the name of the associated symbol.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NamedSymbolId(usize);

impl NamedSymbolId {
    /// Returns the raw representation of `self`.
    pub fn raw_repr(self) -> usize {
        self.0
    }
}

impl From<usize> for NamedSymbolId {
    fn from(raw_id: usize) -> Self {
        NamedSymbolId(raw_id)
    }
}

impl From<NamedSymbolId> for usize {
    fn from(id: NamedSymbolId) -> Self {
        id.raw_repr()
    }
}

/// Identificator of generated symbol expressions.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GeneratedSymbolId(usize);

impl GeneratedSymbolId {
    /// Returns the raw representation of `self`.
    pub fn raw_repr(self) -> usize {
        self.0
    }
}

impl From<usize> for GeneratedSymbolId {
    fn from(raw_id: usize) -> Self {
        GeneratedSymbolId(raw_id)
    }
}

impl From<NamedSymbolId> for SymbolId {
    fn from(id: NamedSymbolId) -> Self {
        SymbolId::Named(id)
    }
}

impl From<GeneratedSymbolId> for SymbolId {
    fn from(id: GeneratedSymbolId) -> Self {
        SymbolId::Generated(id)
    }
}

impl<'ctx> fmt::Display for ContextAnd<'ctx, SymbolId> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self.entity {
            SymbolId::Named(named) => self.ctx.assoc(named).fmt(f),
            SymbolId::Generated(gen) => self.ctx.assoc(gen).fmt(f),
        }
    }
}

impl<'ctx> fmt::Display for ContextAnd<'ctx, NamedSymbolId> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.ctx
            .interner
            .resolve_symbol(self.entity)
            .unwrap()
            .fmt(f)
    }
}

impl<'ctx> fmt::Display for ContextAnd<'ctx, GeneratedSymbolId> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "<gensym #{}>", self.entity.raw_repr())
    }
}

/// Symbol expression.
///
/// A symbol is either named or generated by the SMT solver.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Symbol {
    /// The symbol's identificator.
    pub id: SymbolId,
    /// The symbol's cached type.
    ///
    /// This exists to avoid calls into the context wide type table.
    pub ty: Type,
}

impl Symbol {
    /// Creates a new symbol expression for the given symbol ID.
    pub fn from_raw_parts<T, I>(ty: T, id: I) -> Self
    where
        T: Into<Type>,
        I: Into<SymbolId>,
    {
        Symbol {
            ty: ty.into(),
            id: id.into(),
        }
    }

    /// Returns a new named symbol expression for the given name.
    ///
    /// # Errors
    ///
    /// If there exists already a symbol with the same name but a different type.
    pub fn new_named<T, S>(ctx: &Context, ty: T, name: S) -> ExprResult<Self>
    where
        T: Into<Type>,
        S: AsRef<str> + Into<String>,
    {
        let ty = ty.into();
        let named_id = ctx.interner.intern_or_get(name);
        let symbol = Symbol::from_raw_parts(ty, named_id);
        if let Some(assoc_ty) = ctx.symbol_types.insert_or_get(named_id, ty) {
            // The same name was already interned.
            // We need to check for type collissions.
            if assoc_ty != ty {
                return Err(ExprError::unmatching_symbol_types(assoc_ty, ty, named_id));
            }
        }
        Ok(symbol)
    }

    /// Returns a new generated symbol expression.
    pub fn new_unnamed<T>(ctx: &Context, ty: T) -> Self
    where
        T: Into<Type>,
    {
        Symbol::from_raw_parts(ty, ctx.symbol_id_gen.gen_id())
    }
}

impl<'ctx> ContextAnd<'ctx, Symbol> {
    /// Resolves the name of the associated named symbol.
    ///
    /// Returns `None` for generated symbols.
    pub fn resolve_name(&self) -> Option<&str> {
        if let SymbolId::Named(named) = self.entity.id {
            return match self.ctx.interner.resolve_symbol(named) {
                None => {
                    error!(
                        target: "symbol_resolve_name",
                        "Encountered missing name in context for named symbol: {:?}",
                        self.entity
                    );
                    unreachable!(indoc!(
                        "\
                        Encountered missing name in context for a named symbol:

                         - This is an internal solver error and may be caused by \
                           using an incorrect context instance in this place.

                         - Look into the error-logs to find out more information \
                           under 'symbol_resolve_name'.
                        "
                    ))
                }
                resolved => resolved,
            };
        }
        None
    }

    /// Resolves the global type of the associated symbol.
    ///
    /// For generated symbols the global and local type is always the same.
    pub fn resolve_type(&self) -> Type {
        if let SymbolId::Named(named) = self.entity.id {
            return match self.ctx.symbol_types.get(named) {
                None => {
                    error!(
                        target: "symbol_resolve_type",
                        "Encountered missing type in context for named symbol: {:?}",
                        self.entity
                    );
                    unreachable!(indoc!(
                        "\
                        Encountered missing type in context for a named symbol:

                         - This is an internal solver error and may be caused by \
                           using an incorrect context instance in this place.

                         - Look into the error-logs to find out more information \
                           under 'symbol_resolve_type'.
                        "
                    ))
                }
                Some(resolved) => resolved,
            };
        }
        self.entity.ty
    }
}

impl<'ctx> fmt::Display for ContextAnd<'ctx, Symbol> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.ctx.assoc(self.entity.id).fmt(f)
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
	fn children_slice(&self) -> &[AnyExpr] {
		&[]
	}
}

impl ChildrenMut for Symbol {
	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		&mut []
	}
}

impl IntoChildren for Symbol {
    fn into_children_vec(self) -> Vec<AnyExpr> {
		Vec::new()
    }
}
