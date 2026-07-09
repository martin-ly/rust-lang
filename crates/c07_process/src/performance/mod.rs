//! 性能优化模块
//! performanceoptimization module
//!
//! 这个模块提供了全面的性能优化功能，包括内存使用优化、
//! module surface performance optimization functionality ，memory optimization 、
//! CPU性能提升、I/O性能改进等 Rust 1.90 新特性
//! CPUperformance 、I/Operformance etc. Rust 1.90 feature
#[cfg(feature = "async-support")]
pub mod enhanced;

#[cfg(feature = "async-support")]
pub use enhanced::*;
