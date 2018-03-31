use ast::prelude::*;

use std::fmt;

/// Module for exports of commonly used items of this module.
pub mod prelude {
    pub use super::{
        common_ty,
        expect_array_ty,
        expect_bitvec_ty,
        expect_bool_ty,
        expect_common_bitvec_ty,
        expect_common_bitvec_ty_n,
        expect_common_ty,
        expect_concrete_bitvec_ty,
        have_common_ty,
    };
}

/// Returns `true` if the `Type`s of `lhs` and `rhs` are equal.
///
/// # Note
///
/// - `BitVec` types are equal if their `BitWidth`s are equal.
/// - `Array` types are equal if their index-width and value-width are equal.
pub fn have_common_ty<T1, T2>(lhs: &T1, rhs: &T2) -> bool
where
    T1: HasType,
    T2: HasType,
{
    common_ty(lhs, rhs).is_some()
}

/// Returns the common type of the given `lhs` and `rhs` typed instances
/// if it exists.
///
/// # Note
///
/// - `BitVec` types are equal if their `BitWidth`s are equal.
/// - `Array` types are equal if their index-width and value-width are equal.
pub fn common_ty<T1, T2>(lhs: &T1, rhs: &T2) -> Option<Type>
where
    T1: HasType,
    T2: HasType,
{
    use self::Type::*;
    match (lhs.ty(), rhs.ty()) {
        (Bool, Bool) => Some(Bool),
        (Bitvec(b1), Bitvec(b2)) if b1 == b2 => Some(Bitvec(b1)),
        (Array(a1), Array(a2)) if a1 == a2 => Some(Array(a1)),
        _ => None,
    }
}

/// Checks if the given typed params share the same type.
///
/// # Returns
///
/// The type of both typed params.
///
/// # Errors
///
/// - If the given typed params do not have the same type.
pub fn expect_common_ty<T>(lhs: &T, rhs: &T) -> TypeResult<Type, T>
where
    T: HasType + Clone + fmt::Debug,
{
    common_ty(lhs, rhs).ok_or(TypeError::type_mismatch(lhs.clone(), rhs.clone()))
}

/// Checks if the given typed param is of boolean type.
///
/// # Errors
///
/// - If the given typed param is not of boolean type.
pub fn expect_bool_ty<T>(genval: &T) -> Result<(), String>
where
    T: HasType,
{
    match genval.ty() {
        Type::Bool => Ok(()),
        _ => Err("Expected boolean type.".into()),
    }
}

/// Checks if the given typed param is of array type
/// and returns its concrete array type if it is the case.
///
/// # Errors
///
/// - If the given typed param is not of array type.
pub fn expect_array_ty<T>(genval: &T) -> Result<ArrayTy, String>
where
    T: HasType,
{
    match genval.ty() {
        Type::Array(array_ty) => Ok(array_ty),
        _ => Err("Expected array type.".into()),
    }
}

/// Checks if the given typed param is of bitvec type
/// and returns its bit width if it is the case.
///
/// # Errors
///
/// - If the given typed param is not of bitvec type.
pub fn expect_bitvec_ty<T>(genval: &T) -> Result<BitvecTy, String>
where
    T: HasType,
{
    match genval.ty() {
        Type::Bitvec(width) => Ok(width),
        _ => Err("Expected bitvec type.".into()),
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
where
    T: HasType,
{
    let act_bitvec_ty = expect_bitvec_ty(genval)?;
    if act_bitvec_ty != req_bitvec_ty {
        return Err(format!(
            "Expected bitvec with an expected bit width of {:?}",
            req_bitvec_ty
        ));
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
where
    L: HasType,
    R: HasType,
{
    let lhs_bvty = expect_bitvec_ty(lhs)?;
    let rhs_bvty = expect_bitvec_ty(rhs)?;
    if lhs_bvty != rhs_bvty {
        return Err(format!(
            "Expected equal bitvector types for {:?} and {:?}.",
            lhs_bvty, rhs_bvty
        ));
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
where
    I: IntoIterator<Item = &'t T>,
    T: HasType + 't,
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
