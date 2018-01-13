use ast2::{
    ArrayTy,
    BitvecTy,
    Type,
    HasType
};

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        expect_bitvec_ty
    };
}

/// Checks if the given typed param is of array type
/// and returns its concrete array type if it is the case.
/// 
/// # Errors
/// 
/// - If the given typed param is not of array type.
pub fn expect_array_ty<T>(genval: &T) -> Result<ArrayTy, String>
    where T: HasType
{
    match genval.ty() {
        Type::Array(array_ty) => Ok(array_ty),
        _ => Err("Expected array type.".into())
    }
}

/// Checks if the given typed param is of array type
/// with the given expected index and value bit width.
/// 
/// # Errors
/// 
/// - If the given typed param is not of array type.
/// - If the given typed param is of array type but has not the expected index or value bit width.
pub fn expect_concrete_array_ty<T>(genval: &T, req_array_ty: ArrayTy) -> Result<(), String>
    where T: HasType
{
    let act_array_ty = expect_array_ty(genval)?;
    if act_array_ty != req_array_ty {
        return Err(format!("Expected concrete array type with index width of {:?} and value width of {:?}",
            req_array_ty.index_width(),
            req_array_ty.value_width()))
    }
    Ok(())
}

/// Checks if the given typed params are of the same array type.
/// 
/// # Errors
/// 
/// - If the given typed params are not of array type.
/// - If the given typed params are not of the same array type.
pub fn expect_common_array_ty<L, R>(lhs: &L, rhs: &R) -> Result<ArrayTy, String>
    where L: HasType,
          R: HasType
{
    let lhs_arrty = expect_array_ty(lhs)?;
    let rhs_arrty = expect_array_ty(lhs)?;
    if lhs_arrty != rhs_arrty {
        return Err(format!("Expected equal array types for {:?} and {:?}.",
            lhs_arrty, rhs_arrty))
    }
    Ok(lhs_arrty)
}

/// Checks if the given typed param is of bitvec type
/// and returns its bit width if it is the case.
/// 
/// # Errors
/// 
/// - If the given typed param is not of bitvec type.
pub fn expect_bitvec_ty<T>(genval: &T) -> Result<BitvecTy, String>
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
pub fn expect_concrete_bitvec_ty<T>(genval: &T, req_bitvec_ty: BitvecTy) -> Result<(), String>
    where T: HasType
{
    let act_bitvec_ty = expect_bitvec_ty(genval)?;
    if act_bitvec_ty != req_bitvec_ty {
        return Err(format!("Expected bitvec with an expected bit width of {:?}", req_bitvec_ty))
    }
    Ok(())
}

/// Checks if the given typed params are of the same bitvector type.
/// 
/// # Errors
/// 
/// - If the given typed params are not of bitvector type.
/// - If the given typed params are not of the same bitvector type.
pub fn expect_common_bitvec_ty<L, R>(lhs: &L, rhs: &R) -> Result<BitvecTy, String>
    where L: HasType,
          R: HasType
{
    let lhs_bvty = expect_bitvec_ty(lhs)?;
    let rhs_bvty = expect_bitvec_ty(lhs)?;
    if lhs_bvty != rhs_bvty {
        return Err(format!("Expected equal bitvector types for {:?} and {:?}.",
            lhs_bvty, rhs_bvty))
    }
    Ok(lhs_bvty)
}
