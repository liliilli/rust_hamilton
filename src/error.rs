use thiserror::Error;

use crate::Radian;

#[derive(Error, Debug)]
pub enum EError {
    #[error("Given vector must not be zero or almost zero length.")]
    ZeroLengthVector,
    #[error("Related length (width, height, depth) '{0}' value must not be negative.")]
    NegativeLength(f32),
    #[error("Given value '{0}' is not normal floating value.")]
    NotNormalFloatingValue(f32),
    #[error("Given radian angle '{0}' is invalid.")]
    InvalidRadian(Radian),
    #[error("Given near '{0}' and far '{1}' are no invalid or swapped.")]
    InvalidNearFar(f32, f32),
    #[error("Given argument is not valid.")]
    InvalidArgument,
}
