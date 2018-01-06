use ast2::prelude::*;

pub struct BoolConst {
    pub val: bool
}

impl From<bool> for BoolConst {
    fn from(flag: bool) -> BoolConst {
        if flag { BoolConst::t() } else { BoolConst::f() }
    }
}

impl BoolConst {
    #[inline]
    pub fn t() -> BoolConst {
        BoolConst{ val: true }
    }

    #[inline]
    pub fn f() -> BoolConst {
        BoolConst{ val: false }
    }
}

impl Childs for BoolConst {
    fn childs(&self) -> ChildsIter {
        ChildsIter::none()
    }
}

impl ChildsMut for BoolConst {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::none()
    }
}

impl IntoChilds for BoolConst {
    fn into_childs(&mut self) -> IntoChildsIter {
        IntoChildsIter::none()
    }
}

impl HasType for BoolConst {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl HasKind for BoolConst {
    fn kind(&self) -> ExprKind {
        ExprKind::BoolConst
    }
}

impl HasArity for BoolConst {
    fn arity(&self) -> usize {
        0
    }
}

pub struct And {
    pub childs: Vec<Expr>
}

pub struct Or {
    pub childs: Vec<Expr>
}

pub struct Not {
    pub inner: P<Expr>
}

pub struct Implies {
    pub childs: P<BinExprChilds>
}
