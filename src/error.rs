use thiserror::Error;

#[derive(Debug, Error, PartialEq)]
pub enum Errors {
    #[error("Unexpected token at {0}:{1}")]
    UnexpectedToken(i64, i64),
    #[error("{0}")]
    RuntimeException(String),
    #[error("Unknown error")]
    Unknown,
}
