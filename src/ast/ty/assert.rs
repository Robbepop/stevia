use ast::prelude::*;

/// Checks if the given typed params share the same type.
///
/// # Returns
///
/// The type of both typed params.
///
/// # Errors
///
/// - If the given typed params do not have the same type.
pub fn expect_common_ty<T1, T2>(lhs: &T1, rhs: &T2) -> TypeResult<Type>
where
    T1: HasType,
    T2: HasType
{
    use self::Type::*;
    match (lhs.ty(), rhs.ty()) {
        (Bool, Bool) => Ok(Bool),
        (Bitvec(b1), Bitvec(b2)) if b1 == b2 => Ok(Bitvec(b1)),
        (Array(a1), Array(a2)) if a1 == a2 => Ok(Array(a1)),
        _ => Err(TypeError::type_mismatch(lhs.ty(), rhs.ty()))
    }
}

/// Checks if the given typed param is of array type
/// and returns its concrete array type if it is the case.
///
/// # Errors
///
/// - If the given typed param is not of array type.
pub fn expect_array_ty<T>(typed: &T) -> TypeResult<ArrayTy>
where
    T: HasType,
{
    match typed.ty() {
        Type::Array(array_ty) => Ok(array_ty),
        _ => Err(TypeError::unexpected_type_kind(
            TypeKind::Array,
            typed.ty(),
        )),
    }
}

/// Checks if the given typed param is of bitvec type
/// and returns its bit width if it is the case.
///
/// # Errors
///
/// - If the given typed param is not of bitvec type.
pub fn expect_bitvec_ty<T>(typed: &T) -> TypeResult<BitvecTy>
where
    T: HasType,
{
    match typed.ty() {
        Type::Bitvec(width) => Ok(width),
        _ => Err(TypeError::unexpected_type_kind(
            TypeKind::Bitvec,
            typed.ty(),
        )),
    }
}

/// Checks if the given typed param is of bitvec type
/// with the given expected bit width.
///
/// # Errors
///
/// - If the given typed param is not of bitvec type.
/// - If the given typed param is of bitvec type but has not the expected bit width.
pub fn expect_type<T1, T2>(expected_ty: T1, found_ty: &T2) -> TypeResult<()>
where
    T1: Into<Type>,
    T2: HasType
{
    let expected_ty = expected_ty.into();
    if expected_ty != found_ty.ty() {
        return Err(TypeError::unexpected_type(
            expected_ty,
            found_ty.ty()
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
pub fn expect_common_bitvec_ty<T1, T2>(lhs: &T1, rhs: &T2) -> TypeResult<BitvecTy>
where
    T1: HasType,
    T2: HasType
{
    let lhs_bvty = expect_bitvec_ty(lhs)?;
    let rhs_bvty = expect_bitvec_ty(rhs)?;
    expect_common_ty(&lhs_bvty, &rhs_bvty)?;
    Ok(lhs_bvty)
}

/// Checks if the given iterator of typed items are all of the same bitvector type.
///
/// # Errors
///
/// - If the given iterator yields no elements.
/// - If not all yielded typed items are of the same bitvector type.
pub fn expect_common_bitvec_ty_n<'t, I, T>(typed_vals: I) -> TypeResult<Option<BitvecTy>>
where
    I: IntoIterator<Item = &'t T>,
    T: HasType + 't,
{
    let mut typed_vals = typed_vals.into_iter();
    match typed_vals.next() {
        None => Ok(None),
        Some(ty) => {
            let head_bvty = expect_bitvec_ty(ty)?;
            for ty in typed_vals {
                expect_type(head_bvty, &ty.ty())?;
            }
            Ok(Some(head_bvty))
        }
    }
}
