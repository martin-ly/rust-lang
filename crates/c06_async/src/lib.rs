//! # c06_async - Rust 异步编程学习模块
//!
//! 本 crate 提供 Rust 异步编程的理论与实践指南，涵盖 async/await、Future、Stream、
//! Actor/Reactor/CSP 并发模型、Tokio / Smol / Glommio 运行时，以及异步性能优化、
//! 调试监控与生态集成。
//!
//! ## 模块组织
//!
//! ### 理论基础
//! - [`async_semantics_theory`] - 异步语义理论与形式化定义
//! - [`async_recursion_analysis`] - 异步递归、尾递归优化与迭代等价
//! - [`actor_reactor_patterns`] - Actor/Reactor 模式与调度机制
//! - [`csp_model_comparison`] - CSP 模型对比
//! - [`formal_verification`] - 不变式、终止性与死锁检测
//!
//! ### 核心异步原语
//! - [`futures`] - Future 状态机与组合子
//! - [`streams`] - Stream 异步流与背压
//! - [`r#await`] - async/await 语义
//! - [`tokio`] - Tokio 运行时
//! - [`smol`] - Smol 轻量级运行时
//! - [`actix`] - Actix Actor 框架
//!
//! ### 高级工具与模式
//! - [`utils`] - 重试、超时、限流、熔断
//! - [`advanced_tools`] - 批处理、任务管理、重试引擎
//!
//! ### 生态与版本特性
//! - [`async_runtime`] - 运行时对比与选择
//! - [`async_runtime_examples`] - 运行时示例
//! - [`async_ecosystem_comprehensive`] - 异步生态分析
//! - [`rust_186_features`]..[`rust_198_features`] - 按 Rust 版本组织的特性示例
//!
//! ## 快速开始
//!
//! ```no_run
//! use c06_async::utils::ExecStrategyBuilder;
//! use std::time::Duration;
//!
//! #[tokio::main]
//! async fn main() -> anyhow::Result<()> {
//!     let runner = ExecStrategyBuilder::new()
//!         .concurrency(8)
//!         .attempts(5)
//!         .start_delay(Duration::from_millis(100))
//!         .timeout(Duration::from_secs(2))
//!         .build();
//!
//!     let result = runner
//!         .run(
//!             |attempt| async move {
//!                 Ok::<_, anyhow::Error>(format!("成功于第 {} 次尝试", attempt))
//!             },
//!             None::<fn(&anyhow::Error) -> bool>,
//!         )
//!         .await?;
//!
//!     Ok(())
//! }
//! ```

// [来源: Rust Reference / RFC 2394 / RFC 3185]
#![allow(clippy::type_complexity)]
#![allow(clippy::assertions_on_constants)]
// Nightly 预研特性（仅用于 rust_198_features 等 async iterator 模块）
// 这些特性在 stable 编译器下会被条件编译排除
#![cfg_attr(nightly, feature(async_iterator, async_for_loop))]

// ============================================================================
// 理论基础模块
// ============================================================================

/// 异步语义理论：形式化定义、等价关系与语义模型。
pub mod async_semantics_theory;

/// 异步递归分析：递归与迭代等价、尾递归优化与形式证明。
pub mod async_recursion_analysis;

/// 统一错误处理模块。
pub mod error;

/// Actor 与 Reactor 模式：并发模型、调度机制与实现对比。
pub mod actor_reactor_patterns;

/// CSP 模型对比：Rust vs Golang、通道语义与并发原语。
pub mod csp_model_comparison;

/// 形式化验证与证明：不变式、终止性与死锁检测。
pub mod formal_verification;

// ============================================================================
// 核心异步原语
// ============================================================================

/// Actix Actor 框架。
pub mod actix;

/// 异步运行时对比与选择。
pub mod async_runtime;

// async-std 历史归档（已移除，使用 tokio）
// mod async_std_archive;

/// async/await 关键字语义。
pub mod r#await;

/// Future 状态机与组合子。
pub mod futures;

/// Stream 异步流。
pub mod streams;

/// Tokio 运行时。
pub mod tokio;

/// Smol 轻量级运行时。
pub mod smol;

/// Glommio 高性能运行时（Linux only，基于 io_uring）。
#[cfg(target_os = "linux")]
pub mod glommio;

// ============================================================================
// 高级工具与模式
// ============================================================================

/// 实用工具：重试、超时、限流、熔断与监督树。
pub mod utils;

/// 高级异步工具库。
///
/// ⚠️ **关于 `async_trait` 的使用说明**：
/// 本 crate 的部分示例代码仍使用 `#[async_trait::async_trait]`，原因如下：
/// - Rust 1.75.0 AFIT（async fn in trait）已稳定，但**不支持 trait object（`dyn Trait`）**。
/// - 教学代码需要在 `dyn Trait` 场景下演示，因此 `async_trait` 仍是必要 workaround。
/// - 原生 AFIDT（async fn in dyn trait）仍处于 nightly 实验（rust-lang/rust#133119），未进入 stable。
/// - `dynosaur 0.3.1` 提供 stable 兼容的 dyn async trait 方案，但本 crate 暂不引入，继续以 `async_trait` 作为教学示例。
/// - 详见 [`afit_dyn_tracking`] 模块的对比分析。
pub mod advanced_tools;

// ============================================================================
// Rust 历史特性模块
// ============================================================================

pub mod archive;

/// AFIT / dyn async trait 跟踪模块（nightly-only 预览）。
#[cfg(nightly)]
pub mod afit_dyn_tracking;

/// Async Closures 预览模块（nightly-only）。
#[cfg(nightly)]
pub mod async_closures_preview;

/// Async Closures 可编译示例（1.85.0+ stable，对应 concept/03_advanced/24_async_closures.md）。
pub mod async_closures_stable;

// ============================================================================
// 异步生态系统模块
// ============================================================================

/// 异步生态系统全面分析。
pub mod async_ecosystem_comprehensive;

pub mod rust_186_features;
pub mod rust_187_features;
pub mod rust_188_features;
pub mod rust_189_features;
pub mod rust_192_features;
pub mod rust_193_features;

/// Rust 1.94 历史特性（异步场景）。
pub mod rust_194_features;

/// Rust 1.95.0 异步特性（if let guards 场景）。
pub mod rust_195_features;

pub mod rust_196_features;
pub mod rust_197_features;

/// Rust 1.98.0 预览特性（异步迭代器，需要 nightly）。
#[cfg(nightly)]
pub mod rust_198_features;

/// 异步运行时示例。
pub mod async_runtime_examples;

/// 异步运行时内部原理概念。
pub mod async_runtime_internals;

/// 异步集成框架。
pub mod async_integration_framework;

/// 简化异步集成框架。
pub mod async_runtime_integration_framework_simple;

/// 异步日志与调试。
pub mod async_logging_debugging;

/// 高级异步调试。
pub mod async_debugging_advanced;

/// 异步生态系统集成。
pub mod async_ecosystem_integration;

#[cfg(test)]
pub mod miri_tests;
