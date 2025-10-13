//! 性能优化模块
//! 
//! 这个模块提供了全面的性能优化功能，包括内存使用优化、
//! CPU性能提升、I/O性能改进等 Rust 1.90 新特性

#[cfg(feature = "async")]
pub mod enhanced;

#[cfg(feature = "async")]
pub use enhanced::*;
