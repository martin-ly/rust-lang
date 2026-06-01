//! async-std 历史归档（已移除，推荐使用 tokio）
//! async-std （， tokio）
//!
//! # 状态: 已归档 (2025-03)
//! # state : (2025-03)
//!
//! [async-std](https://async.rs/) 已于 **2025 年 3 月** 停止维护。
//! 本项目的所有异步运行时依赖已统一迁移至 [Tokio](https://tokio.rs/)。
//! this project all async runtime [Tokio](https://tokio.rs/)。
//!
//! # 迁移路径
//! #
//!
//! | async-std API | Tokio 等价 API |
//! |---------------|---------------|
//! | `async_std::task::spawn` | `tokio::spawn` |
//! | `async_std::task::sleep` | `tokio::time::sleep` |
//! | `async_std::fs::read` | `tokio::fs::read` |
//! | `async_std::net::TcpStream` | `tokio::net::TcpStream` |
//! | `async_std::sync::Mutex` | `tokio::sync::Mutex` |
//! | `async_std::channel` | `tokio::sync::mpsc` |
//!
//! # 历史参考
//! # reference
//!
//! async-std 曾是 Rust 异步生态的重要参与者，提供了与标准库镜像的异步 API。
//! async-std Rust async ecosystem important and ，and standard library async API。
//! 其设计哲学（API 与 std 一致）影响了后续的 Tokio 和 smol 发展。
//! its design （API and std ）impact after Tokio and smol 。
//!
//! # 替代方案
//! #
//!
//! - **Tokio** (推荐): 生态最丰富，生产环境首选
//! - **Tokio** (): ecosystem ，environment
//! - **smol**: async-std 的底层运行时，轻量级
//! - **smol**: async-std runtime ，
//! - **glommio**: 线程 per core，适合高吞吐场景
//! - **glommio**: thread per core，scenario
//!
//! # 参考
//! # reference
//! - [async-std 归档公告](https://github.com/async-rs/async-std)
//! - [Tokio 迁移指南](https://tokio.rs/tokio/topics/bridging)

use std::time::Duration;

/// 保留的兼容接口（内部已使用 Tokio 实现）
/// （inside Tokio ）
pub async fn demo_sleep() -> u64 {
    tokio::time::sleep(Duration::from_millis(1)).await;
    1
}
