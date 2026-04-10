//! C12: WebAssembly Error Handling
//!
//! This module provides crate-specific error types and utilities using
//! the trait-based error design from the common crate.

use common::{impl_into_unified_error, impl_rust_lang_error, ErrorCode};
use thiserror::Error;

/// C12 crate-specific error type
#[derive(Error, Debug, Clone)]
pub enum WasmError {
    #[error("compilation error: {0}")]
    Compilation(String),
    
    #[error("runtime error: {0}")]
    Runtime(String),
    
    #[error("memory error: {0}")]
    Memory(String),
    
    #[error("import error: {0}")]
    Import(String),
    
    #[error("export error: {0}")]
    Export(String),
    
    #[error("WASI error: {0}")]
    Wasi(String),
    
    #[error("bindgen error: {0}")]
    Bindgen(String),
}

impl_rust_lang_error!(WasmError, ErrorCode::Wasm);
impl_into_unified_error!(WasmError);

/// Re-export common error types for convenience
pub use common::{
    CommonError, DynamicResult, ErrorContext, ErrorRecovery, Result, RustLangError,
    UnifiedError,
};

/// C12 crate's result type
pub type C12Result<T> = Result<T>;

/// Create WASM compilation error
pub fn wasm_compilation_error<T: Into<String>>(msg: T) -> WasmError {
    WasmError::Compilation(msg.into())
}

/// Create WASM runtime error
pub fn wasm_runtime_error<T: Into<String>>(msg: T) -> WasmError {
    WasmError::Runtime(msg.into())
}

/// Create WASM memory error
pub fn wasm_memory_error<T: Into<String>>(msg: T) -> WasmError {
    WasmError::Memory(msg.into())
}

/// Create WASM import error
pub fn wasm_import_error<T: Into<String>>(msg: T) -> WasmError {
    WasmError::Import(msg.into())
}

/// Create WASM export error
pub fn wasm_export_error<T: Into<String>>(msg: T) -> WasmError {
    WasmError::Export(msg.into())
}

/// Create WASI error
pub fn wasi_error<T: Into<String>>(msg: T) -> WasmError {
    WasmError::Wasi(msg.into())
}

/// Create wasm-bindgen error
pub fn bindgen_error<T: Into<String>>(msg: T) -> WasmError {
    WasmError::Bindgen(msg.into())
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_creation() {
        let err = wasm_compilation_error("test");
        assert!(matches!(err, WasmError::Compilation(_)));
        assert_eq!(err.error_code(), ErrorCode::Wasm);
    }

    #[test]
    fn test_error_conversion() {
        let err = wasm_runtime_error("test");
        let unified: UnifiedError = err.into();
        assert!(matches!(unified, UnifiedError::Custom(_)));
    }
}
