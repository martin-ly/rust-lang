# c06_async - Rust 1.90 异步专题（兼容 1.89）

> 导航：返回 [`rust-formal-engineering-system`](../../rust-formal-engineering-system/README.md) · 质量保障 [`10_quality_assurance/00_index.md`](../../rust-formal-engineering-system/10_quality_assurance/00_index.md) · 异步范式 [`02_async/00_index.md`](../../rust-formal-engineering-system/02_programming_paradigms/02_async/00_index.md) · 同步范式 [`01_synchronous/00_index.md`](../../rust-formal-engineering-system/02_programming_paradigms/01_synchronous/00_index.md) · 最小基准指南 [`11_benchmark_minimal_guide.md`](../../rust-formal-engineering-system/02_programming_paradigms/11_benchmark_minimal_guide.md)

本包系统演示 Rust 1.90 语境下的异步编程（Tokio/futures 生态），并保持对 1.89 的兼容：

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

## 快速上手

Windows PowerShell：

```powershell
cd .\crates\c06_async
cargo build
```

运行示例（更多见 docs/run_guide.md）：

```powershell
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

基准（仅编译或运行）：

```powershell
cargo bench --no-run
# cargo bench
```

更多说明：

- 运行指南：`docs/run_guide.md`
- 最佳实践：`docs/async_best_practices.md`
- 语言特性（Rust 1.90）：`docs/async_rust_190_overview.md` · `docs/async_language_features_190.md`
- 异步风格规范：`docs/async_style_guide.md`
- 异步基础语法与实践：`docs/async_basics_guide.md`
- 异步进阶主题：`docs/async_advanced_topics.md`
- 模式与陷阱：`docs/async_patterns_and_pitfalls.md`
- 工具参考：`docs/utils_reference.md`
- 基准结果：`docs/benchmark_results.md`
- 高级模式：`docs/advanced_patterns_summary.md`

## Rust 1.90 要点（异步相关）

- 生态与兼容性：Tokio、futures、tracing 在 1.90 正常工作；本仓示例保持 1.89 可编译。
- 诊断与可读性：1.90 提升了一些编译器提示的可读性，利于 async/await 错误定位（如生命周期/Send 约束）。
- 规范与风格：推荐在 1.90 环境下统一使用 `#[tokio::main(flavor = "multi_thread")]` 作为默认入口，并通过 `JoinSet`/`select!` 构建结构化并发。
- 文档与实践：详见 `docs/async_rust_190_overview.md` 与 `docs/async_style_guide.md`。

## 基准与指标说明

- 基准集：
  - mpsc（bounded vs unbounded）与 Semaphore 管道吞吐
  - 扩展：select/JoinSet、背压容量与限流并发参数化（见 `benches/async_benches.rs`）
  - 建议：先 `cargo bench --no-run` 验证，再按需 `cargo bench`

- 指标：
  - Actix `/metrics` 暴露 Prometheus 文本格式（requests_total、avg_latency_ns）
  - 结合 `Logger` 与示例中的 p50/p95 打点，辅助定位延迟问题
