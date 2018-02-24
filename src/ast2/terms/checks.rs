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
    let rhs_bvty = expect_bitvec_ty(rhs)?;
    if lhs_bvty != rhs_bvty {
        return Err(format!("Expected equal bitvector types for {:?} and {:?}.",
            lhs_bvty, rhs_bvty))
    }
    Ok(lhs_bvty)
}

/// Checks if the given iterator of typed items are all of the same bitvector type.
/// 
/// # Errors
/// 
/// - If the given iterator yields no elements.
/// - If not all yielded typed items are of the same bitvector type.
pub fn expect_common_bitvec_ty_n<'t, I, T>(ty_iter: I) -> Result<BitvecTy, String>
	where I: IntoIterator<Item=&'t T>,
	      T: HasType + 't
{
    let mut ty_iter = ty_iter.into_iter();
	match ty_iter.next() {
		None => Err("Expected at least one item in the given iterator over typed entities.".into()),
        Some(ty) => {
            let head_bvty = expect_bitvec_ty(&ty.ty())?;
            for ty in ty_iter {
                expect_concrete_bitvec_ty(&ty.ty(), head_bvty)?;
            }
            Ok(head_bvty)
        }
	}
}
