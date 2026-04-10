#![allow(clippy::empty_line_after_doc_comments)]
#![allow(clippy::type_complexity)]
#![allow(clippy::needless_borrows_for_generic_args)]

//! # C10 Networks - Rust 网络编程库
//!
//! 本库提供了基于 Rust 1.92.0 的现代网络编程功能，包括：
//! - 异步网络通信
//! - 多种网络协议支持
//! - 高性能网络编程工具
//! - 安全的网络通信
//!
//! ## 特性
//!
//! - 🚀 基于 Rust 1.92.0 最新特性
//! - ⚡ 异步/await 支持
//! - 🔒 内置安全功能
//! - 📊 性能监控
//! - 🧪 完整的测试覆盖
pub mod asynchronous_communication;
#[path = "diagnostics.rs"]
pub mod diagnostics;
pub mod epoll;
pub mod error;
pub mod error_unified;
pub mod mac;
pub mod network_topology;
pub mod p2p;
pub mod packet;
pub mod performance;
pub mod protocol;
pub mod security;
pub mod semantics;

// Rust 1.91 新特性模块
pub mod archive;
pub use archive::rust_191_features;

// Rust 1.92.0 新特性模块
pub use archive::rust_192_features;
pub mod rust_194_features;
pub mod rust_196_features;
#[cfg(any(feature = "sniff", feature = "offline", feature = "pcap_live"))]
pub mod sniff;
pub mod socket;
pub mod unified_api;

// 重新导出常用类型
pub use error::{NetworkError, NetworkResult, PerformanceError, ProtocolError, SecurityError};
pub use security::acme::AcmeManager;
pub use security::acme::Http01MemoryStore;
#[cfg(feature = "tls")]
pub use security::tls_reload::TlsReloader;
pub use unified_api::NetClient;

/// 库版本信息
///
/// # Examples
///
/// ```
/// use c10_networks::VERSION;
///
/// assert!(!VERSION.is_empty());
/// ```
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// 库名称
///
/// # Examples
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
