//! # OpenTelemetry Protocol (OTLP) Implementation for Rust 1.90
//! 
//! 本库提供了基于Rust 1.90语言特性的OpenTelemetry协议(OTLP)完整实现，
//! 支持同步和异步结合的遥测数据收集、处理和传输。
//! 
//! ## 核心特性
//! 
//! - **异步优先设计**: 利用Rust 1.90的async/await特性实现高性能异步处理
//! - **同步兼容**: 提供同步API接口，支持传统同步代码集成
//! - **多传输协议**: 支持gRPC和HTTP/JSON两种OTLP传输方式
//! - **类型安全**: 利用Rust类型系统确保编译时安全性
//! - **零拷贝优化**: 使用Rust 1.90的内存管理特性优化性能
//! - **并发安全**: 基于Rust的所有权系统实现无锁并发
//! 
//! ## 架构设计
//! 
//! ```text
//! ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
//! │   数据收集层     │    │   数据处理层     │    │   数据传输层     │
//! │  (Collection)   │───▶│  (Processing)   │───▶│  (Transport)    │
//! │                 │    │                 │    │                 │
//! │ • Traces        │    │ • 过滤/聚合      │    │ • gRPC          │
//! │ • Metrics       │    │ • 批处理        │    │ • HTTP/JSON     │
//! │ • Logs          │    │ • 压缩          │    │ • 重试机制      │
//! └─────────────────┘    └─────────────────┘    └─────────────────┘
//! ```
//! 
//! ## 使用示例
//! 
//! ```rust
//! use c21_otlp::{OtlpClient, OtlpConfig, TelemetryData};
//! use opentelemetry::trace::Tracer;
//! 
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     // 创建OTLP客户端
//!     let config = OtlpConfig::default()
//!         .with_endpoint("http://localhost:4317")
//!         .with_timeout(std::time::Duration::from_secs(5));
//!     
//!     let client = OtlpClient::new(config).await?;
//!     
//!     // 发送遥测数据
//!     let data = TelemetryData::trace("example-operation")
//!         .with_attribute("service.name", "my-service")
//!         .with_attribute("service.version", "1.0.0");
//!     
//!     client.export(data).await?;
//!     
//!     Ok(())
//! }
//! ```

pub mod client;
pub mod config;
pub mod data;
pub mod error;
pub mod exporter;
pub mod processor;
pub mod transport;
pub mod utils;

// 重新导出主要类型
pub use client::OtlpClient;
pub use config::OtlpConfig;
pub use data::{TelemetryData, TraceData, MetricData, LogData};
pub use error::{OtlpError, Result};
pub use exporter::{OtlpExporter, ExportResult};
pub use processor::{OtlpProcessor, ProcessingConfig};
pub use transport::{Transport, GrpcTransport, HttpTransport};

// 版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const RUST_VERSION: &str = "1.90";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_version_info() {
        assert!(!VERSION.is_empty());
        assert_eq!(RUST_VERSION, "1.90");
    }
}
