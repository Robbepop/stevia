use crate::{
    ty::{
        BitvecTy,
        HasType,
        Type,
    },
};
use stevia_bitvec::{
    Bitvec,
    BitWidth,
};

impl HasType for BitWidth {
	fn ty(&self) -> Type {
		Type::from(BitvecTy::from(self.len_bits()))
	}
}

impl HasType for Bitvec {
    fn ty(&self) -> Type {
        self.width().ty()
    }
}

impl From<&Bitvec> for BitvecTy {
	fn from(bv: &Bitvec) -> Self {
		bv.width().into()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
		
	mod bitvec_ty {
		use super::*;

		#[test]
		fn w1() {
			assert_eq!(BitvecTy::from(&Bitvec::from(true)), BitvecTy::w1())
		}

		#[test]
		fn w32() {
			assert_eq!(BitvecTy::from(&Bitvec::from(42_u32)), BitvecTy::w32())
		}
	}

	mod ty {
		use super::*;

		#[test]
		fn w1() {
			assert_eq!(Bitvec::from(true).ty(), Type::from(BitvecTy::w1()))
		}

		#[test]
		fn w32() {
			assert_eq!(Bitvec::from(42_u32).ty(), Type::from(BitvecTy::w32()))
		}
	}
}
