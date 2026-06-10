// [来源: Rust Reference / TRPL]
//! Type system fundamentals: enums, structs, traits, and pattern matching.
//! # Rust Type System Learning Module
//!
//! This crate demonstrates Rust's type system concepts from basic primitives
//! to advanced variance and composition patterns.
//!
//! ## Module Overview
//!
//! - `primitive_types`: Scalar and compound type basics
//! - `type_composition` / `type_decomposition`: Building and breaking down types
//! - `type_class`: Trait-based polymorphism (type classes)
//! - `type_variance`: Subtyping relationships in generics
//! - `type_operation`: Type-level computations and transformations
//! - `advanced_pattern_matching`: Exhaustive pattern matching techniques
//! - `r#unsafe`: Safe abstractions over unsafe operations
//! - `rust_196_features`: Rust 1.96 stable feature demonstrations
//!
//! ## Key Concepts Covered
//!
//! | Concept | Module | Rust Feature |
//! |:---|:---|:---|
//! | Algebraic Data Types | `type_composition` | `enum`, `struct` |
//! | Parametric Polymorphism | `type_class` | `trait`, `impl` |
//! | Variance | `type_variance` | `covariant`, `contravariant`, `invariant` |
//! | Unsafe Abstraction | `r#unsafe` | `unsafe`, `raw pointers` |
#![allow(clippy::type_complexity)]
#![feature(never_type)]
#![feature(derive_coerce_pointee)]

// 导出所有主要模块
pub mod error;
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
pub mod rust_193_features;
pub mod rust_194_features;

// 导出 Rust 1.95/1.96 特性模块
pub mod rust_186_features;
pub mod rust_187_features;
pub mod rust_188_features;
pub mod rust_189_features;
pub mod rust_192_features;
pub mod rust_195_features;
pub mod rust_196_features;
pub mod rust_197_features;
pub mod rust_198_features;

// 注意: rust_196_tuple_coercion 模块包含的内容与 Rust 实际稳定特性不符，
// 将在后续版本中清理或重命名。当前保留仅为兼容性。
pub mod rust_196_tuple_coercion; // 待清理: 非标准特性模块

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

#[cfg(test)]
pub mod miri_tests;

// 导出高级宏系统模块
pub mod advanced_macros;

// 导出 use<..> precise capturing 深度指南
pub mod precise_capturing_guide;

// 导出类型系统前沿概念模块
pub mod type_system_frontier;

// 导出示例模块
pub mod examples;

// 导出练习模块（仅测试时编译）
#[cfg(test)]
pub mod exercises;

// test touch
