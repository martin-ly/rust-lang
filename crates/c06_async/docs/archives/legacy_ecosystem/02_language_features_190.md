# Rust 1.90 异步相关语言特性与实践对照

> 目标：在 Rust 1.90 语境下，按语言要素梳理 async/await、trait bound、Send/Sync、Pin、Future、Stream 等，并给出简短示例与链接到本仓可运行代码。

## 目录

- [Rust 1.90 异步相关语言特性与实践对照](#rust-190-异步相关语言特性与实践对照)
  - [目录](#目录)
  - [1. async/await 与返回类型](#1-asyncawait-与返回类型)
  - [2. Future 与 Pin](#2-future-与-pin)
  - [3. Send/Sync 边界](#3-sendsync-边界)
  - [4. 选择与并发组合器](#4-选择与并发组合器)
  - [5. 结构化并发与 JoinSet](#5-结构化并发与-joinset)
  - [6. 超时与时间 API](#6-超时与时间-api)
  - [7. 通道与背压](#7-通道与背压)
  - [8. 锁与共享状态](#8-锁与共享状态)
  - [9. 错误处理、取消与清理](#9-错误处理取消与清理)
  - [10. 观测与调试](#10-观测与调试)

## 1. async/await 与返回类型

- `async fn foo() -> T` 实际返回 `impl Future<Output = T>`。
- `async { ... }` 创建匿名 Future，适合内联组合与 `select!` 分支。

注意：不要在同步函数里直接 `await`；需将函数改为 `async fn` 或在异步入口中调用。

## 2. Future 与 Pin

- `core::future::Future` 定义 `poll(self: Pin<&mut Self>, cx: &mut Context<'_>)`。
- 大多数情况下无需手写 `Pin`；库会封装。自定义 Future 或需要自引用时才关注 `Pin` 不动性。

链接：`src/futures/future01.rs`

## 3. Send/Sync 边界

- 跨线程 `tokio::spawn` 的闭包与捕获值要满足 `Send + 'static`。
- `!Send` 类型（如 `Rc<...>`、`RefCell<...>`）不应跨线程移动；在同线程的 `LocalSet` 中可以执行。

示例：`src/bin/tokio_joinset_exp01.rs`（跨线程并发任务）、`src/bin/localset_nonsend_exp01.rs`（LocalSet 运行 !Send）

## 4. 选择与并发组合器

- `tokio::select!` 进行多路等待；未选中分支会被取消。
- `tokio::join!`/`try_join!` 并发等待多个已知 Future。

示例：`src/bin/tokio_select_exp01.rs`、`tokio_try_join_exp01.rs`

## 5. 结构化并发与 JoinSet

- `tokio::task::JoinSet` 管理动态任务集合，统一 `join_next()` 收集结果。
- 出错时可触发整体取消，避免“僵尸任务”。

示例：`src/bin/joinset_cancel_on_error_exp01.rs`

## 6. 超时与时间 API

- `tokio::time::timeout`、`sleep`、`sleep_until` 与 `Instant`/`Duration`。
- 组合 `select!` 实现超时回退与快速失败。

示例：`src/bin/tokio_timeout_cancel_exp01.rs`、`select_timeout_fallback_exp01.rs`

## 7. 通道与背压

- `tokio::sync::mpsc` 建议优先使用有界通道（bounded）。
- `Semaphore` 控制并发度，配合窗口批处理实现稳态吞吐。

示例：`src/bin/tokio_mpsc_backpressure_exp01.rs`、`semaphore_mpsc_pipeline_exp01.rs`

## 8. 锁与共享状态

- `tokio::sync::{Mutex, RwLock}`；避免持锁 `await`。
- `Notify` 用于单向条件通知。

示例：`src/bin/tokio_sync_mutex_exp01.rs`、`tokio_sync_rwlock_exp01.rs`、`tokio_sync_notify_exp01.rs`

## 9. 错误处理、取消与清理

- `anyhow::Result`/`thiserror`；`try_join!` 配合 `?` 短路。
- 被取消的分支应在 Drop 中进行必要释放（文件描述符、Semaphore 许可等）。

示例：`src/bin/cancel_propagation_exp01.rs`

## 10. 观测与调试

- 启动 `tracing`，为关键路径打点；开发期可启用 `tokio-console`。

示例：`src/bin/tracing_console_exp01.rs`

---

进一步阅读：`docs/async_basics_guide.md`、`docs/async_rust_190_overview.md`、`docs/advanced_patterns_summary.md`
