use ast::{
    HasType,
    Type
};

pub mod prelude {
    pub use super::{
        expect_bool_ty
    };
}

/// Checks if the given typed param is of boolean type.
/// 
/// # Errors
/// 
/// - If the given typed param is not of boolean type.
pub fn expect_bool_ty<T>(genval: &T) -> Result<(), String>
    where T: HasType
{
    match genval.ty() {
        Type::Bool => Ok(()),
        _ => Err("Expected boolean type.".into())
    }
}
