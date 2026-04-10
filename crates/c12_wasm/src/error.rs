//! C12: WebAssembly 错误处理

pub use common::{
    WasmError, RustLangError, Result,
    ErrorContext, ErrorRecovery,
};

/// C12 crate 的结果类型
pub type C12Result<T> = Result<T>;

/// 创建 WASM 编译错误
pub fn wasm_compilation_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Wasm(WasmError::Compilation(msg.into()))
}

/// 创建 WASM 运行时错误
pub fn wasm_runtime_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Wasm(WasmError::Runtime(msg.into()))
}

/// 创建 WASM 内存错误
pub fn wasm_memory_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Wasm(WasmError::Memory(msg.into()))
}

/// 创建 WASM 导入错误
pub fn wasm_import_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Wasm(WasmError::Import(msg.into()))
}

/// 创建 WASM 导出错误
pub fn wasm_export_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Wasm(WasmError::Export(msg.into()))
}

/// 创建 WASI 错误
pub fn wasi_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Wasm(WasmError::Wasi(msg.into()))
}

/// 创建 wasm-bindgen 错误
pub fn bindgen_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Wasm(WasmError::Bindgen(msg.into()))
}
