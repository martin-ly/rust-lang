// [来源: Rust Reference / RFC 2394 / RFC 3185]
//! Async/await, futures, streams, and runtime integrations (Tokio, Smol).
#![allow(clippy::type_complexity)]
#![allow(clippy::assertions_on_constants)]
// Nightly 预研特性（仅用于 async_closures_preview 和 afit_dyn_tracking 模块）
// 这些特性在 stable 编译器下会被条件编译排除
#![feature(async_iterator, async_for_loop)]

//! # C06 Async - Rust 异步编程全面解析
//! # C06 Async - Rust async surface
//!
//! 本 crate 提供 Rust 1.95.0 异步编程的全面、深入的理论与实践指南。
//! This crate provides a comprehensive and in-depth theoretical and practical guide to Rust 1.95.0 async programming.
//!
//! ## 模块组织
//! ## Module Organization
//!
//! ### 理论基础模块 (Theoretical Foundations)
//! ### Theoretical Foundations Modules
//! - [`async_semantics_theory`] - Async semantics theory, formal definitions, equivalence proofs
//! - [`async_recursion_analysis`] - 异步递归深度分析、尾递归优化、迭代等价
//! - [`async_recursion_analysis`] - Async recursion deep analysis, tail recursion optimization, iteration equivalence
//! - [`actor_reactor_patterns`] - Actor/Reactor 模式、调度机制、并发模型
//!
//! ### 核心异步原语 (Core Async Primitives)
//! ### Core Async Primitives
//! - [`futures`] - Future state machines, combinators, scheduling mechanisms
//! - [`streams`] - Stream 处理、异步迭代器、背压控制
//! - [`streams`] - Stream handling, async iterators, backpressure control
//! - `r#await` - async/await 语义、控制流分析
//! - `r#await` - async/await semantics, control flow analysis
//! - [`tokio`] - Tokio runtime, synchronization primitives, I/O
//! - [`smol`] - Smol 轻量级运行时
//! - [`smol`] - Smol lightweight runtime
//! - `async-std` - async-std 运行时（已于 2025-03 停止维护）
//! - `async-std` - async-std runtime (maintenance ended 2025-03)
//! - [`async_runtime`] - 运行时对比与选择
//! - [`async_runtime`] - Runtime comparison and selection
//!
//! ### Actor 模型与消息传递 (Actor Model)
//! ### Actor Model and Message Passing
//!
//! ### 高级工具与模式 (Advanced Tools)
//! ### Advanced Tools and Patterns
//!
//! - [`utils`] - 重试、超时、限流、熔断、监督树
//! - [`utils`] - Retry, timeout, rate limiting, circuit breaker, supervision trees
//! - [`advanced_tools`] - 批处理、任务管理、重试引擎
//! - [`advanced_tools`] - Batch processing, task management, retry engines
//!
//! ### Rust 1.95 特性 (Rust 1.95 Features)
//! ### Rust 1.95 Features
//!   - if let guards 用于异步状态机匹配
//!   - if let guards for async state machine matching
//!   - bool 转浮点数用于异步数值计算
//!   - bool to float for async numeric computation
//!   - RangeInclusive 优化用于异步迭代
//!   - RangeInclusive optimization for async iteration
//!
//! ### Rust 1.94 历史特性 (Rust 1.94 Historical Features)
//! ### Rust 1.94 Historical Features
//!   - array_windows 用于异步数据流处理
//!   - array_windows for async data flow processing
//!   - LazyCell/LazyLock 用于异步缓存
//!   - Mathematical constants for async algorithms
//!
//! ### 生态系统集成 (Ecosystem Integration)
//! ### Ecosystem Integration
//! - [`async_ecosystem_comprehensive`] - Comprehensive ecosystem analysis
//! - [`async_runtime_examples`] - 运行时示例
//! - [`async_runtime_examples`] - Runtime examples
//! - [`async_runtime_integration_framework_simple`] - 简化集成
//! - [`async_debugging_advanced`] - 高级调试技术
//! ## Quick Start
//!
//! ### 理论学习路径
//! ### Theory Learning Path
//!
//! ```no_run
//! use c06_async::{
//!     actor_reactor_patterns, async_recursion_analysis, async_semantics_theory,
//!     csp_model_comparison,
//! };
//!
//! #[tokio::main]
//! async fn main() {
//!     // 1. 学习异步语义理论
//!     // 1. learn async theory
//!     async_semantics_theory::run_all_examples().await;
//!
//!     // 2. 理解异步递归
//!     // 2. async
//!     async_recursion_analysis::run_all_examples().await;
//!
//!     // 3. 掌握并发模式
//!     // 3. Master concurrency patterns
//!     actor_reactor_patterns::run_all_examples().await;
//!
//!     // 4. 对比 CSP 模型
//!     // 4. to CSP
//!     csp_model_comparison::run_all_examples().await;
//! }
//! ```
//!
//! ### 实践应用路径
//! ### Practice Application Path
//!
//! ```no_run
//! use c06_async::utils::ExecStrategyBuilder;
//! use std::time::Duration;
//!
//! #[tokio::main]
//! async fn main() -> anyhow::Result<()> {
//!     // 构建执行策略
//!     // Build execution strategy
//!     let runner = ExecStrategyBuilder::new()
//!         .concurrency(8)
//!         .attempts(5)
//!         .start_delay(Duration::from_millis(100))
//!         .timeout(Duration::from_secs(2))
//!         .build();
//!
//!     // 执行任务
//!     // task
//!     let result = runner
//!         .run(
//!             |attempt| async move {
//!                 // 您的异步任务
//!                 // async task
//!                 Ok::<_, anyhow::Error>(format!("成功于第 {} 次尝试", attempt))
//!             },
//!             None::<fn(&anyhow::Error) -> bool>,
//!         )
//!         .await?;
//!
//!     Ok(())
//! }
//! ```
//!
//! ## 核心文档 (2025年10月最新)
//! ## core (202510)
//!
//! ### 🌟 必读文档
//! ### 🌟
//!
//! - **[知识分类体系](../docs/COMPREHENSIVE_ASYNC_KNOWLEDGE_CLASSIFICATION_2025.md)** ⭐⭐⭐
//! - complete: languagefeaturesfeatureslibraryfeaturesdesignpattern pattern
//!   - 113+ 个知识点分类，180+ 个代码示例
//! - 113+ 180+ example
//!   - 学习路径建议 (8周完整课程)
//!   - learn (8complete )
//!
//! - **[最终报告 2025-10-06](../异步编程全面梳理最终报告_2025_10_06.md)** ⭐⭐⭐
//! - **[ultimately 2025-10-06](../async surface ultimately _2025_10_06.md)** ⭐⭐⭐
//!   - 中文详细报告，包含所有实现细节
//!   - in ，all
//!   - Reactor、Actor、CSP 三大模式完整分析
//! - ReactorActorCSP largepatterncomplete analysis
//!   - 设计模式、性能优化、错误处理完整实现
//!
//! - **[快速入门指南](../异步编程全面梳理_README_2025_10_06.md)** ⭐⭐
//! - **[fast ](../async surface _README_2025_10_06.md)** ⭐⭐
//!   - 快速开始和文件结构
//!   - fast and structure
//!   - 推荐阅读顺序
//!   - order
//!   - 学习路径建议
//!   - learn
//!
//! - **[实现总结](../docs/COMPREHENSIVE_ASYNC_IMPLEMENTATION_SUMMARY_2025.md)** ⭐
//! - pattern analysis
//!   - 完整度统计
//!   - complete
//!   - 快速查找指南
//!   - fast
//!
//! ## 示例索引
//! ## example
//!
//! ### 🎯 2025年核心示例 (强烈推荐)
//! ### 🎯 2025core example ()
//!
//! - **[Reactor 模式完整实现](../examples/reactor_pattern_comprehensive_2025.rs)** ⭐⭐⭐
//!   cargo run --example reactor_pattern_comprehensive_2025
//!   ```
//!   - 1,800+ 行完整实现，包含形式化定义和性质证明
//!   - 优先级调度、批处理优化、性能基准测试
//!   - 网络I/O、定时器、用户输入等实际应用示例
//!
//! - **[Actor 模式完整实现](../examples/actor_pattern_comprehensive_2025.rs)** ⭐⭐⭐
//!   cargo run --example actor_pattern_comprehensive_2025
//!   ```
//!   - 2,100+ 行完整实现，包含形式化定义和性质证明
//!   - 银行账户系统应用 (存款、取款、转账、事务回滚)
//!   - Actor 生命周期管理、监督策略、性能测试
//! - Actor lifetimemanagementperformance test
//!
//! - **[终极理论与实践指南 2025](../examples/ultimate_async_theory_practice_2025.rs)** ⭐⭐⭐
//!   cargo run --example ultimate_async_theory_practice_2025
//!   ```
//!   - Actor/Reactor/CSP 三种模式的数学模型和完整实现
//! - Actor/Reactor/CSP patterncomplete implementation
//!   - 异步设计模式 (Builder, Factory, Adapter, Strategy, Observer)
//!   - 1,500+
//!
//! - **[Tokio & Smol 最新特性 2025](../examples/tokio_smol_latest_features_2025.rs)** ⭐⭐⭐
//!   cargo run --example tokio_smol_latest_features_2025
//!   ```
//!   - Tokio 1.41+ 新特性: JoinSet, TaskLocal, Runtime Metrics
//!   - 性能对比和基准测试
//! - performance test
//!
//! - **[异步性能优化完整指南 2025](../examples/async_performance_optimization_2025.rs)** ⭐⭐
//!   cargo run --example async_performance_optimization_2025 --release
//!   ```
//!   - 对象池 (减少 50-80% 分配开销)
//!   - to ( 50-80% overhead )
//!   - 零拷贝技术 (Bytes 库)
//!   - technique (Bytes library )
//!   - SIMD 向量化 (2-8x 性能提升)
//!   - SIMD vectorization (2-8x performance )
//!
//! - **[异步调试与监控完整指南 2025](../examples/async_debugging_monitoring_2025.rs)** ⭐⭐
//!   cargo run --example async_debugging_monitoring_2025
//!   ```
//!   - Tracing 结构化日志
//!   - Tracing structure
//!   - 性能指标收集 (Metrics)
//!   - performance indicator (Metrics)
//!   - 健康检查系统
//! - system
//!
//! - **[综合异步模式 2025](../examples/comprehensive_async_patterns_2025.rs)** ⭐⭐
//!   cargo run --example comprehensive_async_patterns_2025
//!   ```
//!   - Actor、Reactor、CSP 模式实际应用
//! - ActorReactorCSP pattern application
//!   - async design 、architecture
//!   - 1,100+ 行完整注释代码
//!   - 1,100+ complete
//!
//! - **[CSP 模式完整实现](../examples/csp_pattern_comprehensive_2025.rs)** ⭐⭐⭐
//!   cargo run --example csp_pattern_comprehensive_2025
//!   ```
//!   - 1,100+ 行完整实现，包含形式化定义和性质证明
//!   - 数据处理流水线、分布式任务调度、实时日志聚合
//!   - pipeline 、distribution task 、aggregation
//!   - 基本通信、Select 多路复用、性能基准测试
//! - Select multipleperformance test
//!
//! ### 📚 基础示例
//! ### example
//!
//! - 基础示例: `examples/tokio_smoke.rs`, `examples/futures_smoke.rs`
//! - 工具示例: `examples/utils_strategy_smoke.rs`
//! - API 网关: `examples/async_api_gateway_2025.rs`
//! hint ：example `examples/` and module 。
// ============================================================================
// 理论基础模块 (Theoretical Foundations)
// ============================================================================

/// 异步语义理论 - 形式化定义、等价关系、语义模型
/// async theory - definition 、etc. 、
pub mod async_semantics_theory;

/// 异步递归分析 - 递归与迭代等价、尾递归优化、形式证明
pub mod async_recursion_analysis;

/// 统一错误处理模块
pub mod error;

/// Actor 与 Reactor 模式 - 并发模型、调度机制、实现对比
/// Actor and Reactor - concurrency 、mechanism 、to
pub mod actor_reactor_patterns;

/// CSP 模型对比 - Rust vs Golang、通道语义、并发原语
/// CSP to - Rust vs Golang、channel 、concurrency
pub mod csp_model_comparison;

/// 形式化验证与证明 - 不变式、终止性、死锁检测
pub mod formal_verification;

// ============================================================================
// 核心异步原语 (Core Async Primitives)
// ============================================================================

/// Actix Actor 框架
/// Actix Actor framework
pub mod actix;

/// 异步运行时
/// Async Runtime
pub mod async_runtime;

// async-std 历史归档（已移除，使用 tokio）
// mod async_std_archive;

/// async/await 关键字
pub mod r#await;

/// Future 与组合子
/// Future and combination
pub mod futures;

/// Stream 异步流
/// Stream async stream
pub mod streams;

/// Tokio 运行时
/// Tokio runtime
pub mod tokio;

/// Smol 轻量级运行时
/// Smol lightweight runtime
pub mod smol;

/// Glommio 高性能运行时 (Linux only, 基于 io_uring)
#[cfg(target_os = "linux")]
pub mod glommio;

// ============================================================================
// 高级工具与模式 (Advanced Tools)
// ============================================================================

/// 实用工具: 重试、超时、限流、熔断
/// tool : 、、stream 、
pub mod utils;

/// 高级异步工具库
/// async tool library
///
/// ⚠️ **关于 `async_trait` 的使用说明**:
/// ⚠️ **about `async_trait` explain **:
/// 本 crate 的部分示例代码仍使用 `#[async_trait::async_trait]`，原因如下：
/// this crate part example `#[async_trait::async_trait]`，cause under ：
/// - Rust 1.75.0 AFIT (async fn in trait) 已稳定，但**不支持 trait object (`dyn Trait`)**
/// - 教学代码需要在 `dyn Trait` 场景下演示，因此 `async_trait` 仍是必要 workaround
/// - in `dyn Trait` scenario under demonstration ，therefore `async_trait` workaround
/// - 详见 [`afit_dyn_tracking`] 模块的对比分析
/// - [`afit_dyn_tracking`] module analysis
pub mod advanced_tools;

// ============================================================================
// Rust 1.94 历史特性模块 (Rust 1.94 Historical Features)
// ============================================================================

pub mod archive;

pub mod afit_dyn_tracking;
/// Async Closures 实现模块 (1.85.0+ 稳定)
pub mod async_closures_preview;
// AFIDT 跟踪模块 (rust-lang/rust#133119, nightly)
// ============================================================================
// 异步生态系统模块 (Async Ecosystem)
// ============================================================================

/// 异步生态系统全面分析
/// Async Ecosystem Comprehensive Analysis
pub mod async_ecosystem_comprehensive;
pub mod rust_186_features;
pub mod rust_187_features;
pub mod rust_188_features;
pub mod rust_189_features;
pub mod rust_190_features;
pub mod rust_191_features;
pub mod rust_192_features;
pub mod rust_193_features;
/// Rust 1.95.0 异步特性 (if let guards 场景)
/// : 1.94 historicalfeatures rust_194_features module
pub mod rust_194_features;
pub mod rust_195_features; // Rust 1.95.0 特性 (async 场景 if let guards)
pub mod rust_196_features;
pub mod rust_197_features;
pub mod rust_198_features;

/// 异步运行时示例
/// asyncruntime example
pub mod async_runtime_examples;

/// 异步运行时内部原理概念
/// async runtime inside concept
pub mod async_runtime_internals;

/// 异步集成框架
/// asyncintegration framework
pub mod async_integration_framework;

/// 简化异步集成框架
pub mod async_runtime_integration_framework_simple;

/// 异步日志与调试
/// async and
pub mod async_logging_debugging;

/// 高级异步调试
/// async
pub mod async_debugging_advanced;

/// 异步生态系统集成
/// async ecosystem system
pub mod async_ecosystem_integration;

#[cfg(test)]
pub mod miri_tests;
