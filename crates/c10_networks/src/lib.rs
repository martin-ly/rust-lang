//! # C10 Networks - Rust 网络编程库
//! 
//! 本库提供了基于 Rust 1.89 的现代网络编程功能，包括：
//! - 异步网络通信
//! - 多种网络协议支持
//! - 高性能网络编程工具
//! - 安全的网络通信
//! 
//! ## 特性
//! 
//! - 🚀 基于 Rust 1.89 最新特性
//! - ⚡ 异步/await 支持
//! - 🔒 内置安全功能
//! - 📊 性能监控
//! - 🧪 完整的测试覆盖

pub mod asynchronous_communication;
pub mod epoll;
pub mod error;
pub mod mac;
pub mod network_topology;
pub mod packet;
pub mod performance;
pub mod protocol;
pub mod socket;
pub mod p2p;
pub mod unified_api;
#[path = "diagnostics.rs"]
pub mod diagnostics;

// 重新导出常用类型
pub use error::{NetworkError, NetworkResult, ProtocolError, PerformanceError, SecurityError};

/// 库版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// 库名称
pub const NAME: &str = env!("CARGO_PKG_NAME");
