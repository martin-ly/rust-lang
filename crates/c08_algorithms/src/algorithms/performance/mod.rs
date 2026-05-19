//! # 性能分析模块
//!
//! 本模块提供算法性能分析的工具和方法。
pub mod benchmarking;
pub mod optimization;
pub mod profiling;

// 重新导出性能分析相关类型
pub use benchmarking::*;
pub use optimization::*;
pub use profiling::*;
