use thiserror::Error;

#[derive(Error, Debug)]
pub enum EError {
    #[error("Given vector must not be zero or almost zero length.")]
    ZeroLengthVector,
    #[error("Related length (width, height, depth) '{0}' value must not be negative.")]
    NegativeLength(f32),
}
