#![allow(clippy::type_complexity)]
#![allow(clippy::empty_line_after_doc_comments)]
#![allow(clippy::duplicated_attributes)]

// 导出所有主要模块
pub mod initial_object;
pub mod performance;
pub mod primitive_types;
pub mod terminal_object;
pub mod type_class;
pub mod type_composition;
pub mod type_decomposition;
pub mod type_operation;
pub mod type_transformation;
pub mod type_variance;
pub mod r#unsafe;

// 导出归档模块（包含旧版本特性）
pub mod archive;

// 导出 Rust 1.94 特性模块
pub mod rust_194_features;

// 重新导出Rust 1.94特性
pub use rust_194_features::*;

// 导出 WebAssembly 支持模块
pub mod wasm_support;

// 导出高级模式匹配模块
pub mod advanced_pattern_matching;

// 导出高级错误处理模块
pub mod advanced_error_handling;

// 导出类型系统验证工具模块
pub mod type_system_validator;

// 导出性能优化技巧模块
pub mod performance_optimization;

// 导出并发和异步高级特性模块
pub mod concurrent_async_advanced;

// 导出内存安全高级演示模块
pub mod memory_safety_advanced;

// 导出高级宏系统模块
pub mod advanced_macros;

// 导出示例模块
pub mod examples;

// 导出练习模块（仅测试时编译）
#[cfg(test)]
pub mod exercises;
