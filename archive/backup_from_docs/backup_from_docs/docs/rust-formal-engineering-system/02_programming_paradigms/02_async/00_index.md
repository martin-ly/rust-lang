# 异步范式（Asynchronous Paradigm）索引

## 📊 目录

- [异步范式（Asynchronous Paradigm）索引](#异步范式asynchronous-paradigm索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [术语](#术语)
  - [核心概念](#核心概念)
  - [常见陷阱](#常见陷阱)
  - [渐进迁移清单（同步 → 异步）](#渐进迁移清单同步--异步)
  - [仓库内相关](#仓库内相关)
    - [文件级清单（精选）](#文件级清单精选)
    - [具体示例（可点击）](#具体示例可点击)
  - [同步 vs 异步（简要对照）](#同步-vs-异步简要对照)
  - [设计建议](#设计建议)
  - [最小模板提示](#最小模板提示)
  - [导航](#导航)

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

## 常见陷阱

- 在异步上下文中执行阻塞操作，导致运行时工作线程被占满（需用 `spawn_blocking`）。
- 忽略 `Send`/`Sync` 边界，在线程间移动 `!Send` future 产生未定义行为风险（编译器会阻止）。
- 任务泄漏：`spawn` 的任务未被取消或 join，在停机与错误路径上悬挂。
- 缺乏背压：无界通道或缓冲导致内存膨胀与尾延迟增大。
- 锁争用放大：在 `async` 中使用阻塞锁（而非异步锁）导致调度非公平。

## 渐进迁移清单（同步 → 异步）

1. 识别 I/O 热点与 tail latency，定义 p95/p99 目标与并发上限。
2. 以边界为单位抽象接口（I/O 端口、存储、网络），先提供兼容实现。
3. 将阻塞调用通过 `spawn_blocking` 适配，验证正确性与回压策略。
4. 引入结构化并发（`JoinSet`/`scope`）与取消语义，完善清理。
5. 建立观测面板（`tracing` + 指标），再扩大异步覆盖范围。

## 仓库内相关

- 异步模块：`crates/c06_async/README.md`、`crates/c06_async/docs/`、`crates/c06_async/benches/`
- 同步对照：`crates/c05_threads/README.md`
- 网络与服务：`crates/c10_networks/`、`crates/c13_microservice/`

### 文件级清单（精选）

- 示例（`crates/c06_async/examples/`）：
  - `tokio_exp01.rs`：基础 async/await 与任务协作
  - `axum_exp01.rs`：基于 Axum 的 HTTP 端点与并发处理
- 基准（`crates/c06_async/benches/`）：
  - `async_benches.rs`：mpsc（bounded/unbounded）、Semaphore 管道吞吐参数化

### 具体示例（可点击）

- 基础 async/await：[`c06_async/src/bin/async_await_exp01.rs`](../../../crates/c06_async/src/bin/async_await_exp01.rs) ・ [`async_await_exp02.rs`](../../../crates/c06_async/src/bin/async_await_exp02.rs)
- Future 与轮询：[`c06_async/src/futures/future01.rs`](../../../crates/c06_async/src/futures/future01.rs)
- Tokio 基础与通道：[`tokio_exp01.rs`](../../../crates/c06_async/src/bin/tokio_exp01.rs) ・ [`tokio_chan_exp01.rs`](../../../crates/c06_async/src/bin/tokio_chan_exp01.rs) ・ [`tokio_mpsc_backpressure_exp01.rs`](../../../crates/c06_async/src/bin/tokio_mpsc_backpressure_exp01.rs)
- 结构化并发：[`task_scope_structured_concurrency_exp01.rs`](../../../crates/c06_async/src/bin/task_scope_structured_concurrency_exp01.rs) ・ [`joinset_cancel_on_error_exp01.rs`](../../../crates/c06_async/src/bin/joinset_cancel_on_error_exp01.rs)
- 超时与取消：[`tokio_timeout_cancel_exp01.rs`](../../../crates/c06_async/src/bin/tokio_timeout_cancel_exp01.rs) ・ [`timeout_cancel_scope_exp01.rs`](../../../crates/c06_async/src/bin/timeout_cancel_scope_exp01.rs)
- 背压与限速：[`semaphore_mpsc_pipeline_exp01.rs`](../../../crates/c06_async/src/bin/semaphore_mpsc_pipeline_exp01.rs) ・ [`tokio_semaphore_limit_exp01.rs`](../../../crates/c06_async/src/bin/tokio_semaphore_limit_exp01.rs)
- 观测与调试：[`tracing_console_exp01.rs`](../../../crates/c06_async/src/bin/tracing_console_exp01.rs)
- 微服务与实践：[`microservice_patterns_exp01.rs`](../../../crates/c06_async/src/bin/microservice_patterns_exp01.rs) ・ [`graceful_shutdown_exp01.rs`](../../../crates/c06_async/src/bin/graceful_shutdown_exp01.rs)
- 基准入口：[`benches/async_benches.rs`](../../../crates/c06_async/benches/async_benches.rs)

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

## 最小模板提示

- 建议子文档均包含：目的、术语、核心概念、实践、参考、导航。
- 新增示例后，请在本页“仓库内相关”或上级总索引补充链接。

## 导航

- 返回总索引：[`../00_index.md`](../00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
- 同步范式：[`../01_synchronous/00_index.md`](../01_synchronous/00_index.md)
- c06_async：[`../../../crates/c06_async/`](../../../crates/c06_async/)
- c05_threads：[`../../../crates/c05_threads/`](../../../crates/c05_threads/)
