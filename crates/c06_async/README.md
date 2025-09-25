# c06_async - Rust 1.90 异步专题

> 导航：返回 [`rust-formal-engineering-system`](../../rust-formal-engineering-system/README.md) · 质量保障 [`10_quality_assurance/00_index.md`](../../rust-formal-engineering-system/10_quality_assurance/00_index.md) · 异步范式 [`02_async/00_index.md`](../../rust-formal-engineering-system/02_programming_paradigms/02_async/00_index.md) · 同步范式 [`01_synchronous/00_index.md`](../../rust-formal-engineering-system/02_programming_paradigms/01_synchronous/00_index.md) · 最小基准指南 [`11_benchmark_minimal_guide.md`](../../rust-formal-engineering-system/02_programming_paradigms/11_benchmark_minimal_guide.md)

本包系统演示 Rust 1.90 语境下的异步编程（Tokio/futures 生态），包含最新的异步编程特性：

## 0. 目录（严格编号）

1. 介绍与范围
2. 2025 年新增功能
3. Rust 1.90 新特性（异步相关）
4. 快速上手
5. 示例与运行脚本
6. 测试与基准
7. 文档导航（Tokio/Smol/Cookbook/语言特性）
8. Rust 1.90 要点（异步相关）
9. 基准与指标说明

注：仓内所有文档逐步采用“严格编号章节 + 可点击目录”的统一格式。

- 基础：async/await、Future/Stream、Tokio 运行时
- 并发：select/try_join/JoinSet、结构化并发
- 同步：Mutex/RwLock/Notify、mpsc/oneshot
- 控制：超时、取消、限流（Semaphore）、背压（bounded mpsc）
- I/O 并发：buffer_unordered 并发抓取、错误处理
- 调试与观测：tracing、（可选）tokio-console
- 语言/编译器：Rust 1.90 相关语法/诊断改进与注意事项
- 批处理与调度：窗口批处理、管道限速
- 基准：mpsc bounded vs unbounded、Semaphore 管道吞吐
- 工具：utils（重试/超时/限流），可复用
- 分布式：分布式锁、流式处理、背压控制
- 微服务：服务发现、负载均衡、熔断降级
- 云原生：配置管理、健康检查、Kubernetes 探针

## 2. 🆕 2025年新增功能

### 异步生态系统全面分析

- **运行时对比分析**：std、smol、async-std、tokio 等库的深度对比
- **概念定义和属性关系**：每个库的核心概念、特性、使用场景
- **集成框架共性**：运行时共性、设计模式、性能特征分析
- **异步同步转换**：完整的转换机制和最佳实践
- **聚合组合设计模式**：顺序、并行、管道、扇出、扇入等模式

### 异步日志调试和跟踪系统

- **结构化日志记录**：基于 tracing 的高性能日志系统
- **异步任务跟踪**：完整的任务生命周期监控
- **性能监控**：实时性能指标收集和分析
- **本地调试工具**：断点设置、调试信息收集
- **分布式追踪支持**：为微服务架构提供追踪能力

### 综合演示和示例

- **完整示例代码**：涵盖所有异步库的使用场景
- **性能基准测试**：并发、内存、错误处理等基准
- **最佳实践指南**：2025年最新的异步编程建议
- **运行脚本**：一键运行所有演示和测试

## 3. Rust 1.90 新特性

- **异步Drop**: 异步资源清理机制
- **异步生成器**: AsyncIterator 生态支持
- **改进的借用检查器**: Polonius 借用检查器优化
- **下一代特质求解器**: 性能优化和算法改进
- **并行前端**: 编译优化和并行处理
- **改进的对齐检查**: 内存对齐优化
- **枚举判别值规范**: 显式判别值支持
- **生命周期转换**: 增强的生命周期管理
- **异步控制流增强**: 异步状态机、资源管理、错误处理
- **性能优化**: 并行编译、特质求解器、借用检查器优化

## 4. 快速上手

Windows PowerShell：

```powershell
cd .\crates\c06_async
cargo build
```

## 5. 示例与运行脚本（更多见 `docs/run_guide.md`）

```powershell
# 异步生态系统综合演示（推荐）
cargo run --example async_ecosystem_comprehensive_demo

# 使用脚本运行完整演示
.\scripts\run_comprehensive_demo.ps1

# Rust 1.90 综合演示
cargo run --example rust_190_comprehensive_demo

# 基础异步示例
cargo run --bin tokio_select_exp01
cargo run --bin tokio_try_join_exp01
cargo run --bin tokio_joinset_exp01

# 高级模式示例
cargo run --bin distributed_lock_exp01
cargo run --bin stream_processing_exp01
cargo run --bin microservice_patterns_exp01
cargo run --bin cloud_native_exp01
cargo run --bin event_sourcing_exp01
cargo run --bin distributed_consensus_exp01

# 完整示例列表见 docs/run_guide.md
```

新增模式示例：

```powershell
cargo run --example tokio_patterns
cargo run --example smol_patterns
cargo run --example distributed_lock_redis
cargo run --example stream_processing_backpressure
cargo run --example microservice_patterns
cargo run --example metrics_collection_prometheus
```

## 6. 测试和基准

```powershell
# 运行综合测试
cargo test --test rust_190_comprehensive_tests

# 基准（仅编译或运行）
cargo bench --no-run
# cargo bench
```

## 7. 文档导航

- 运行指南：`docs/run_guide.md`
- 最佳实践：`docs/async_best_practices.md`
- Tokio 最佳实践（2025）：`docs/tokio_best_practices_2025.md`
- Smol 最佳实践（2025）：`docs/smol_best_practices_2025.md`
- Async Cookbook（Tokio/Smol 片段）：`docs/async_cookbook_tokio_smol.md`
- Tokio Console 与 Tracing 指南：`docs/tokio_console_and_tracing.md`
- 语言特性（Rust 1.90）：`docs/async_rust_190_overview.md` · `docs/async_language_features_190.md`
- 异步风格规范：`docs/async_style_guide.md`
- 异步基础语法与实践：`docs/async_basics_guide.md`
- 异步进阶主题：`docs/async_advanced_topics.md`
- 模式与陷阱：`docs/async_patterns_and_pitfalls.md`
- 工具参考：`docs/utils_reference.md`
- 基准结果：`docs/benchmark_results.md`
- 高级模式：`docs/advanced_patterns_summary.md`
- 形式化与语义边界：`docs/formal_methods_async.md`
- MSRV 与兼容性：`docs/msrv_and_compatibility.md`
- 基准测试分析指南：`docs/benchmark_analysis_guide.md`

## 8. Rust 1.90 要点（异步相关）

- 生态与兼容性：Tokio、futures、tracing 在 1.90 正常工作；本仓示例保持 1.89 可编译。
- 诊断与可读性：1.90 提升了一些编译器提示的可读性，利于 async/await 错误定位（如生命周期/Send 约束）。
- 规范与风格：推荐在 1.90 环境下统一使用 `#[tokio::main(flavor = "multi_thread")]` 作为默认入口，并通过 `JoinSet`/`select!` 构建结构化并发。
- 文档与实践：详见 `docs/async_rust_190_overview.md` 与 `docs/async_style_guide.md`。

## 9. 基准与指标说明

- 基准集：
  - mpsc（bounded vs unbounded）与 Semaphore 管道吞吐
  - 扩展：select/JoinSet、背压容量与限流并发参数化（见 `benches/async_benches.rs`）
  - 建议：先 `cargo bench --no-run` 验证，再按需 `cargo bench`

- 指标：
  - Actix `/metrics` 暴露 Prometheus 文本格式（requests_total、avg_latency_ns）
  - 结合 `Logger` 与示例中的 p50/p95 打点，辅助定位延迟问题
