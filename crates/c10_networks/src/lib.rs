//! Lib

// [来源: Rust Standard Library / RFCs]
//! Network programming: TCP/UDP, HTTP, WebSocket, and async I/O.
#![allow(clippy::type_complexity)]
#![allow(clippy::needless_borrows_for_generic_args)]

//! # C10 Networks - Rust 网络编程库
//! - 异步网络通信
//! - async network
//! - 多种网络协议支持
//! - network protocol
//! - 高性能网络编程工具
//! - high performance network programming tool
//! - performance network programming tool
//! - 高performancenetwork programmingtool
//! - 安全的网络通信
//! - network
//! ## 特性
//! ## feature
//! - 🚀 基于 Rust 1.95.0+ 最新特性 (Edition 2024)
//! - 🚀 Rust 1.95.0+ feature (Edition 2024)
//! - 🚀 Based on Rust 1.95.0+ 最新feature (Edition 2024)
//! - 📅 对齐日期: 2026-05-12
//! - 📅 to date : 2026-05-12
//! - 📅 to齐date: 2026-05-12
//! - ⚡ 异步/await 支持
//! - ⚡ async /await
//! - 🔒 内置安全功能
//! - 🔒 inside functionality
//! - 📊 性能监控
//! - 📊 performance
//! - 🧪 完整的测试覆盖
//! - 🧪 complete
pub mod asynchronous_communication;
#[path = "diagnostics.rs"]
pub mod diagnostics;
pub mod epoll;
pub mod error;
pub mod error_unified;
pub mod http3_quic;
pub mod io_uring_demo;
pub mod mac;
pub mod network_topology;
pub mod p2p;
pub mod packet;
pub mod performance;
pub mod protocol;
pub mod security;
pub mod semantics;
pub mod telemetry;

// Rust 1.91 新特性模块
pub mod archive;
pub use archive::rust_191_features;

// Rust 1.92.0 新特性模块
pub use archive::rust_192_features;
pub mod io_uring_advanced; // io_uring 深度实践
#[cfg(feature = "libp2p")]
pub mod libp2p_advanced; // libp2p 深度集成
pub mod quic_advanced; // QUIC/HTTP3 完整实现
pub mod rust_186_features;
pub mod rust_187_features;
pub mod rust_188_features;
pub mod rust_189_features;
pub mod rust_190_features;
pub mod rust_193_features;
pub mod rust_194_features;
pub mod rust_195_features; // Rust 1.95 特性 (网络场景)
pub mod rust_196_features;
pub mod rust_197_features;

pub mod cargo_semver_checks_guide;
#[cfg(feature = "sniff")]
pub mod sniff;
pub mod socket;
pub mod unified_api;
pub mod zero_copy_networking;

// 重新导出常用类型
pub use error::{NetworkError, NetworkResult, PerformanceError, ProtocolError, SecurityError};
pub use security::acme::{AcmeManager, Http01MemoryStore};
#[cfg(feature = "tls")]
pub use security::tls_reload::TlsReloader;
pub use unified_api::NetClient;

/// 库版本信息
/// library this
///
/// ```
/// use c10_networks::VERSION;
///
/// assert!(!VERSION.is_empty());
/// ```
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// 库名称
/// library
///
/// ```
/// use c10_networks::NAME;
///
/// assert_eq!(NAME, "c10_networks");
/// ```
pub const NAME: &str = env!("CARGO_PKG_NAME");

// 导出由 tonic-build 生成的 protobuf/gRPC 模块
pub mod hello {
    tonic::include_proto!("hello");
}

#[cfg(test)]
pub mod miri_tests;
