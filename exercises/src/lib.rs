//! # Rust 编程练习库
//!
//! 本库提供按主题分类的编程练习题，覆盖 Rust 核心概念：
//! - 所有权与借用
//! - 类型系统
//! - 泛型与特质
//! - 并发编程
//! - 异步编程
//! - 错误处理
//! - 宏系统
//! - Unsafe Rust
//!
//! 每道练习题对应 `docs/` 下的说明文档和 `tests/` 下的测试用例。

pub mod ownership_borrowing;
pub mod type_system;
pub mod generics_traits;
pub mod concurrency;
pub mod async_programming;
pub mod error_handling;
pub mod macros;
pub mod unsafe_rust;
