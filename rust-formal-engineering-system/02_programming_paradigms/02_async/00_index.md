# 异步范式（Asynchronous Paradigm）索引

## 目的

- 系统化整理 Rust 异步编程模型及其适用边界。
- 与同步范式建立可对照的选择指南与迁移策略。
- 汇总仓库内相关示例、基准与最佳实践。

## 术语

- 异步（Async）：任务挂起而不阻塞线程，由运行时在就绪时继续执行。
- Future：可被轮询的计算；`Pin`、`Unpin` 与状态机语义。
- 运行时（Runtime）：任务调度器与 I/O 驱动（如 Tokio）。
- 背压（Backpressure）：通过容量/信号限制生产速度以匹配消费能力。

## 核心概念

- 执行模型：`async/await` → 状态机 → 由运行时调度。
- 并发原语：`select!`、`JoinSet`、`try_join!`、`mpsc`/`oneshot`。
- 同步桥接：`spawn_blocking`、`block_in_place`、`ReceiverStream`。
- I/O 策略：高并发 I/O、长尾延迟、需要细颗粒调度时优选异步。
- 可观测性：`tracing`、`tokio-console`、自定义指标导出。

## 仓库内相关

- 异步模块：`crates/c06_async/README.md`、`crates/c06_async/docs/`、`crates/c06_async/benches/`
- 同步对照：`crates/c05_threads/README.md`
- 网络与服务：`crates/c10_networks/`、`crates/c13_microservice/`

## 同步 vs 异步（简要对照）

- 低并发/CPU 受限：同步简洁、开销低；异步收益有限。
- 高并发/I/O 受限：异步显著降低线程数与上下文切换。
- 可调度性：异步细粒度调度与取消更灵活；同步调试更直接。
- 迁移策略：从同步开始→识别 I/O 热点→按边界渐进引入异步。

## 设计建议

- 结构化并发：优先 `JoinSet`/`scope` 管理任务生命周期。
- 背压优先：有限容量通道 + 超时/丢弃/信号量策略。
- 限制阻塞：阻塞调用封装为 `spawn_blocking`，并批量化处理。
- 指标先行：为关键任务添加 p50/p95、错误率与重试计数。

## 导航

- 返回根：[`rust-formal-engineering-system/README.md`](../../README.md)
- 同步范式：[`01_synchronous/00_index.md`](../01_synchronous/00_index.md)
- c06_async：[`crates/c06_async/`](../../../crates/c06_async/)
- c05_threads：[`crates/c05_threads/`](../../../crates/c05_threads/)
