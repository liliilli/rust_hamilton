use thiserror::Error;

#[derive(Error, Debug)]
pub enum EError {
    #[error("Given vector must not be zero or almost zero length.")]
    ZeroLengthVector,
}
