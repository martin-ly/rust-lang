//! # WebAssembly 2.0 + Rust 1.90 集成库
//!
//! 本库提供了 Rust 1.90 新特性与 WebAssembly 2.0 的完整集成实现。
//! This library provides complete integration of Rust 1.90 new features with WebAssembly 2.0.

pub mod types;
pub mod rust_189_features;
pub mod error_handling;

// 重新导出主要类型和功能
// Re-export main types and functions
pub use types::{
    Value, ValueType, Module, Function, FunctionType, Memory, Table, 
    Instruction, BulkMemoryOperations, TailCall, HostBinding, 
    HostBindingType, InterfaceType, RecordField, ValidationError
};

pub use rust_189_features::{
    WasmArrayBuilder, BulkMemoryManager, TailCallOptimizer, 
    HostBindingManager, InterfaceTypeHandler, SimdProcessor, 
    SimdInstruction, Rust190Wasm2Integration, TestResult
};

pub use error_handling::{
    WebAssemblyError, ErrorSeverity, RecoveryStrategy, ErrorHandler, 
    ErrorStatistics, ErrorLogEntry
};
