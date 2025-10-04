/// 性能基准测试框架
///
/// 提供系统性能测试和基准测试工具

pub mod load_generator;
pub mod latency_analyzer;
pub mod throughput_meter;

// 重新导出常用类型
pub use load_generator::{LoadGenerator, LoadPattern};
pub use latency_analyzer::{LatencyAnalyzer, LatencyMetrics};
pub use throughput_meter::{ThroughputMeter, ThroughputMetrics};

