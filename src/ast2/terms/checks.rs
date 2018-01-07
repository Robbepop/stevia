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
/// 
/// # Errors
/// 
/// - If the given typed param is not of bitvec type.
pub fn expect_bitvec_ty<T>(genval: &T) -> Result<BitWidth, String>
    where T: HasType
{
    match genval.ty() {
        Type::Bitvec(width) => Ok(width),
        _ => Err("Expected bitvec type.".into())
    }
}

/// Checks if the given typed param is of bitvec type
/// with the given expected bit width.
/// 
/// # Errors
/// 
/// - If the given typed param is not of bitvec type.
/// - If the given typed param is of bitvec type but has not the expected bit width.
pub fn expect_bitvec_ty_and_width<T>(genval: &T, expected_width: BitWidth) -> Result<(), String>
    where T: HasType
{
    let bw = expect_bitvec_ty(genval)?;
    if bw != expected_width {
        return Err(format!("Expected bitvec with an expected bit width of {:?}", bw))
    }
    Ok(())
}
