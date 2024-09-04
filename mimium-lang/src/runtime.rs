use crate::compiler;
use crate::interner::ToSymbol;
use crate::utils::{error::ReportableError, metadata::Span};

pub mod scheduler;
// pub mod hir_interpreter;
pub mod builtin_fn;

pub mod vm;

#[derive(Debug)]
pub enum ErrorKind {
    Unknown,
}

impl std::fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ErrorKind::Unknown => write!(f, "Unknown Error"),
        }
    }
}
#[derive(Debug)]
pub struct Error(pub ErrorKind, pub Span);
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let _ = write!(f, "Runtime Error: ");
        self.0.fmt(f)
    }
}

impl std::error::Error for Error {}

impl ReportableError for Error {
    fn get_span(&self) -> std::ops::Range<usize> {
        self.1.clone()
    }
}
