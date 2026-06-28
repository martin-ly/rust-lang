//! Rust所有权与可判定性分析 - 示例代码库
//!
//! 本库包含所有权系统的各种示例和练习

pub mod advanced_patterns;
pub mod concurrency;
pub mod async_patterns;
pub mod unsafe_patterns;
pub mod ffi_patterns;
pub mod macro_patterns;
pub mod typestate;
pub mod design_patterns;

// Re-export常用类型
pub use advanced_patterns::*;
pub use concurrency::*;
