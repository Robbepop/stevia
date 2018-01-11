/// Generates all necessary trait impls for the given binary term expression.
/// 
/// This includes impls for
/// 
/// - `Childs`
/// - `ChildsMut`
/// - `IntoChilds`
/// - `HasType`
/// - `HasKind`
/// - `HasArity`
/// - `From<Self> for Expr`
/// 
/// # Note
/// 
/// This macro expects the given binary term expression to have a `width` field
/// of type `BitWidth` as well as another field `childs` of type `BinExprChilds`.
macro_rules! impl_traits_for_binary_term_expr {
    ($name:ident) => {
        impl Childs for $name {
            fn childs(&self) -> ChildsIter {
                self.childs.childs()
            }
        }

        impl ChildsMut for $name {
            fn childs_mut(&mut self) -> ChildsIterMut {
                self.childs.childs_mut()
            }
        }

        impl IntoChilds for $name {
            fn into_childs(self) -> IntoChildsIter {
                self.childs.into_childs()
            }
        }

        impl HasType for $name {
            fn ty(&self) -> Type {
                self.width.ty()
            }
        }

        impl HasKind for $name {
            fn kind(&self) -> ExprKind {
                ExprKind::$name
            }
        }

        impl HasArity for $name {
            fn arity(&self) -> usize {
                2
            }
        }

        impl From<$name> for AnyExpr {
            fn from(expr: $name) -> AnyExpr {
                AnyExpr::$name(expr)
            }
        }
    }
}

/// Generates all necessary trait impls for the given n-ary term expression.
/// 
/// This includes impls for
/// 
/// - `Childs`
/// - `ChildsMut`
/// - `IntoChilds`
/// - `HasType`
/// - `HasKind`
/// - `HasArity`
/// - `From<Self> for Expr`
/// 
/// # Note
/// 
/// This macro expects the given binary term expression to have a `width` field
/// of type `BitWidth` as well as another field `childs` of type `Vec<AnyExpr>`.
macro_rules! impl_traits_for_nary_term_expr {
    ($name:ident) => {
        impl Childs for $name {
            fn childs(&self) -> ChildsIter {
                ChildsIter::nary(&self.childs)
            }
        }

        impl ChildsMut for $name {
            fn childs_mut(&mut self) -> ChildsIterMut {
                ChildsIterMut::nary(&mut self.childs)
            }
        }

        impl IntoChilds for $name {
            fn into_childs(self) -> IntoChildsIter {
                IntoChildsIter::nary(self.childs)
            }
        }

        impl HasType for $name {
            fn ty(&self) -> Type {
                self.width.ty()
            }
        }

        impl HasKind for $name {
            fn kind(&self) -> ExprKind {
                ExprKind::$name
            }
        }

        impl HasArity for $name {
            fn arity(&self) -> usize {
                self.childs.len()
            }
        }

        impl From<$name> for AnyExpr {
            fn from(expr: $name) -> AnyExpr {
                AnyExpr::$name(expr)
            }
        }
    }
}
