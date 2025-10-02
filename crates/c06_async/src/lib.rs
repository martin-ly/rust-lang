//! # C06 Async - Rust 异步编程全面解析
//!
//! 本 crate 提供 Rust 1.90 异步编程的全面、深入的理论与实践指南。
//!
//! ## 模块组织
//!
//! ### 理论基础模块 (Theoretical Foundations)
//!
//! - [`async_semantics_theory`] - 异步语义理论、形式化定义、等价关系证明
//! - [`async_recursion_analysis`] - 异步递归深度分析、尾递归优化、迭代等价
//! - [`actor_reactor_patterns`] - Actor/Reactor 模式、调度机制、并发模型
//! - [`csp_model_comparison`] - CSP 模型对比 (Rust vs Golang)、语义差异
//!
//! ### 核心异步原语 (Core Async Primitives)
//!
//! - [`futures`] - Future 状态机、组合子、调度机制
//! - [`streams`] - Stream 处理、异步迭代器、背压控制
//! - [`r#await`] - async/await 语义、控制流分析
//! - [`tokio`] - Tokio 运行时、同步原语、I/O 抽象
//! - [`smol`] - Smol 轻量级运行时
//! - [`async_std`] - async-std 运行时
//! - [`async_runtime`] - 运行时对比与选择
//!
//! ### Actor 模型与消息传递 (Actor Model)
//!
//! - [`actix`] - Actix Actor 框架基础
//!
//! ### 高级工具与模式 (Advanced Tools)
//!
//! - [`utils`] - 重试、超时、限流、熔断、监督树
//! - [`advanced_tools`] - 批处理、任务管理、重试引擎
//!
//! ### Rust 1.90 特性 (Rust 1.90 Features)
//!
//! - [`rust_190_features`] - Rust 1.90 异步新特性
//! - [`rust_190_real_features`] - 真实稳定特性实现
//! - [`rust_190_real_stable_features`] - 稳定特性详解
//! - [`rust_190_advanced_features`] - 高级异步特性
//! - [`improved_async_features`] - 改进的异步实现
//! - [`async_control_flow_190`] - 控制流分析
//! - [`performance_optimization_190`] - 性能优化技术
//!
//! ### 生态系统集成 (Ecosystem Integration)
//!
//! - [`async_ecosystem_comprehensive`] - 生态系统全面分析
//! - [`async_ecosystem_integration`] - 生态系统集成
//! - [`async_runtime_examples`] - 运行时示例
//! - [`async_integration_framework`] - 集成框架
//! - [`async_runtime_integration_framework_simple`] - 简化集成
//! - [`async_logging_debugging`] - 日志与调试
//! - [`async_debugging_advanced`] - 高级调试技术
//!
//! ## 快速开始
//!
//! ### 理论学习路径
//!
//! ```rust
//! use c06_async::async_semantics_theory;
//! use c06_async::async_recursion_analysis;
//! use c06_async::actor_reactor_patterns;
//! use c06_async::csp_model_comparison;
//!
//! #[tokio::main]
//! async fn main() {
//!     // 1. 学习异步语义理论
//!     async_semantics_theory::run_all_examples().await;
//!     
//!     // 2. 理解异步递归
//!     async_recursion_analysis::run_all_examples().await;
//!     
//!     // 3. 掌握并发模式
//!     actor_reactor_patterns::run_all_examples().await;
//!     
//!     // 4. 对比 CSP 模型
//!     csp_model_comparison::run_all_examples().await;
//! }
//! ```
//!
//! ### 实践应用路径
//!
//! ```rust
//! use c06_async::utils::ExecStrategyBuilder;
//! use std::time::Duration;
//!
//! #[tokio::main]
//! async fn main() -> anyhow::Result<()> {
//!     // 构建执行策略
//!     let runner = ExecStrategyBuilder::new()
//!         .concurrency(8)
//!         .attempts(5)
//!         .start_delay(Duration::from_millis(100))
//!         .timeout(Duration::from_secs(2))
//!         .build();
//!
//!     // 执行任务
//!     let result = runner.run(
//!         |attempt| async move {
//!             // 您的异步任务
//!             Ok::<_, anyhow::Error>(format!("成功于第 {} 次尝试", attempt))
//!         },
//!         None::<fn(&anyhow::Error) -> bool>,
//!     ).await?;
//!
//!     Ok(())
//! }
//! ```
//!
//! ## 示例索引
//!
//! - 基础示例: `examples/tokio_smoke.rs`, `examples/futures_smoke.rs`
//! - Actor 示例: `examples/actix_basic.rs`
//! - 工具示例: `examples/utils_strategy_smoke.rs`
//! - 混合模式: `examples/actor_csp_hybrid_minimal.rs`
//! - API 网关: `examples/async_api_gateway_2025.rs`
//!
//! 提示：更多示例请查看 `examples/` 目录及各模块顶部文档注释。

// ============================================================================
// 理论基础模块 (Theoretical Foundations)
// ============================================================================

/// 异步语义理论 - 形式化定义、等价关系、语义模型
pub mod async_semantics_theory;

/// 异步递归分析 - 递归与迭代等价、尾递归优化、形式证明
pub mod async_recursion_analysis;

/// Actor 与 Reactor 模式 - 并发模型、调度机制、实现对比
pub mod actor_reactor_patterns;

/// CSP 模型对比 - Rust vs Golang、通道语义、并发原语
pub mod csp_model_comparison;

/// 形式化验证与证明 - 不变式、终止性、死锁检测
pub mod formal_verification;

// ============================================================================
// 核心异步原语 (Core Async Primitives)
// ============================================================================

/// Actix Actor 框架
pub mod actix;

/// 异步运行时
pub mod async_runtime;

/// async-std 运行时
pub mod async_std;

/// async/await 关键字
pub mod r#await;

/// Future 与组合子
pub mod futures;

/// Stream 异步流
pub mod streams;

/// Tokio 运行时
pub mod tokio;

/// Smol 轻量级运行时
pub mod smol;

// ============================================================================
// 高级工具与模式 (Advanced Tools)
// ============================================================================

/// 实用工具: 重试、超时、限流、熔断
pub mod utils;

/// 高级异步工具库
pub mod advanced_tools;

// ============================================================================
// Rust 1.90 特性模块 (Rust 1.90 Features)
// ============================================================================

/// Rust 1.90 异步特性
pub mod rust_190_features;

/// Rust 1.90 真实特性实现
pub mod rust_190_real_features;

/// Rust 1.90 真实稳定特性
pub mod rust_190_real_stable_features;

/// Rust 1.90 高级异步特性
pub mod rust_190_advanced_features;

/// 改进的异步特性实现
pub mod improved_async_features;

/// 异步控制流分析 (Rust 1.90)
pub mod async_control_flow_190;

/// 性能优化技术 (Rust 1.90)
pub mod performance_optimization_190;

// ============================================================================
// 异步生态系统模块 (Async Ecosystem)
// ============================================================================

/// 异步生态系统全面分析
pub mod async_ecosystem_comprehensive;

/// 异步运行时示例
pub mod async_runtime_examples;

/// 异步集成框架
pub mod async_integration_framework;

/// 简化异步集成框架
pub mod async_runtime_integration_framework_simple;

/// 异步日志与调试
pub mod async_logging_debugging;

/// 高级异步调试
pub mod async_debugging_advanced;

/// 异步生态系统集成
pub mod async_ecosystem_integration;