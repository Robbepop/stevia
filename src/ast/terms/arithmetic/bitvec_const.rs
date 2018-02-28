use ast::prelude::*;

use apint::{ApInt, Width};

pub mod prelude {
    pub use super::BitvecConst;
}

/// A constant bitvec term expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitvecConst {
    /// The constant bitvec value.
    pub val: ApInt,
    /// The bit width of the const value.
    ///
    /// Used to verify the integrity of the bit width during
    /// the lifetime of an expression.
    pub bitvec_ty: BitvecTy,
}

impl BitvecConst {
    /// Creates a new `BitvecConst` for the given bit width with a value of zero.
    pub fn zero(ty: BitvecTy) -> BitvecConst {
        let val = ApInt::zero(ty.width().raw_width());
        BitvecConst::from(val)
    }

    /// Creates a new `BitvecConst` from the given `i8` with a bit width of 8 bits.
    pub fn from_i8(val: i8) -> BitvecConst {
        let val = ApInt::from_i8(val);
        BitvecConst {
            bitvec_ty: BitvecTy::from(val.width()),
            val,
        }
    }

    /// Creates a new `BitvecConst` from the given `u8` with a bit width of 8 bits.
    pub fn from_u8(val: u8) -> BitvecConst {
        let val = ApInt::from_u8(val);
        BitvecConst {
            bitvec_ty: BitvecTy::from(val.width()),
            val,
        }
    }

    /// Creates a new `BitvecConst` from the given `i16` with a bit width of 16 bits.
    pub fn from_i16(val: i16) -> BitvecConst {
        let val = ApInt::from_i16(val);
        BitvecConst {
            bitvec_ty: BitvecTy::from(val.width()),
            val,
        }
    }

    /// Creates a new `BitvecConst` from the given `u16` with a bit width of 16 bits.
    pub fn from_u16(val: u16) -> BitvecConst {
        let val = ApInt::from_u16(val);
        BitvecConst {
            bitvec_ty: BitvecTy::from(val.width()),
            val,
        }
    }

    /// Creates a new `BitvecConst` from the given `i32` with a bit width of 32 bits.
    pub fn from_i32(val: i32) -> BitvecConst {
        let val = ApInt::from_i32(val);
        BitvecConst {
            bitvec_ty: BitvecTy::from(val.width()),
            val,
        }
    }

    /// Creates a new `BitvecConst` from the given `u32` with a bit width of 32 bits.
    pub fn from_u32(val: u32) -> BitvecConst {
        let val = ApInt::from_u32(val);
        BitvecConst {
            bitvec_ty: BitvecTy::from(val.width()),
            val,
        }
    }

    /// Creates a new `BitvecConst` from the given `i64` with a bit width of 64 bits.
    pub fn from_i64(val: i64) -> BitvecConst {
        let val = ApInt::from_i64(val);
        BitvecConst {
            bitvec_ty: BitvecTy::from(val.width()),
            val,
        }
    }

    /// Creates a new `BitvecConst` from the given `u64` with a bit width of 64 bits.
    pub fn from_u64(val: u64) -> BitvecConst {
        let val = ApInt::from_u64(val);
        BitvecConst {
            bitvec_ty: BitvecTy::from(val.width()),
            val,
        }
    }
}

impl From<i8> for BitvecConst {
    fn from(val: i8) -> BitvecConst {
        BitvecConst::from_i8(val)
    }
}
impl From<u8> for BitvecConst {
    fn from(val: u8) -> BitvecConst {
        BitvecConst::from_u8(val)
    }
}
impl From<i16> for BitvecConst {
    fn from(val: i16) -> BitvecConst {
        BitvecConst::from_i16(val)
    }
}
impl From<u16> for BitvecConst {
    fn from(val: u16) -> BitvecConst {
        BitvecConst::from_u16(val)
    }
}
impl From<i32> for BitvecConst {
    fn from(val: i32) -> BitvecConst {
        BitvecConst::from_i32(val)
    }
}
impl From<u32> for BitvecConst {
    fn from(val: u32) -> BitvecConst {
        BitvecConst::from_u32(val)
    }
}
impl From<i64> for BitvecConst {
    fn from(val: i64) -> BitvecConst {
        BitvecConst::from_i64(val)
    }
}
impl From<u64> for BitvecConst {
    fn from(val: u64) -> BitvecConst {
        BitvecConst::from_u64(val)
    }
}

impl From<ApInt> for BitvecConst {
    /// Creates a new `BitvecConst` from the given `ApInt`.
    fn from(apint: ApInt) -> BitvecConst {
        BitvecConst {
            bitvec_ty: apint.width().into(),
            val: apint,
        }
    }
}

impl Childs for BitvecConst {
    fn childs(&self) -> ChildsIter {
        ChildsIter::none()
    }
}

impl ChildsMut for BitvecConst {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::none()
    }
}

impl IntoChilds for BitvecConst {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::none()
    }
}

impl HasType for BitvecConst {
    fn ty(&self) -> Type {
        self.bitvec_ty.ty()
    }
}

impl HasKind for BitvecConst {
    fn kind(&self) -> ExprKind {
        ExprKind::BitvecConst
    }
}

impl HasArity for BitvecConst {
    fn arity(&self) -> usize {
        0
    }
}

impl From<BitvecConst> for AnyExpr {
    fn from(bitvec_const: BitvecConst) -> AnyExpr {
        AnyExpr::BitvecConst(bitvec_const)
    }
}
