use ast2::{
    Type,
    HasType,
    BitWidth
};

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        expect_bitvec_ty
    };
}

/// Checks if the given typed param is of bitvec type
/// and returns its bit width if it is the case.
/// Returns an error otherwise.
pub fn expect_bitvec_ty<T>(genval: &T) -> Result<BitWidth, String>
    where T: HasType
{
    match genval.ty() {
        Type::Bitvec(width) => Ok(width),
        _ => Err("Expected bitvec type.".into())
    }
}
