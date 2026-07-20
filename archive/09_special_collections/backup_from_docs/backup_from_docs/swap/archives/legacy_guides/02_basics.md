# Rust 异步基础语法与实践指南（Rust 1.90）

> 目标：用最小但完整的示例，系统讲清 async/await、Future、任务、运行时、常见同步原语与控制结构；给出规范写法、详细中文注释与可运行代码索引。

## 📊 目录

- [Rust 异步基础语法与实践指南（Rust 1.90）](#rust-异步基础语法与实践指南rust-190)
  - [📊 目录](#-目录)
  - [1. 基本术语](#1-基本术语)
  - [2. 最小可运行示例（带注释）](#2-最小可运行示例带注释)
  - [3. await 的语义与常见误区](#3-await-的语义与常见误区)
  - [4. 任务创建与结构化并发](#4-任务创建与结构化并发)
  - [5. 超时、取消与截止时间](#5-超时取消与截止时间)
  - [6. 同步原语与通道（Tokio）](#6-同步原语与通道tokio)
  - [7. 背压、限流与窗口批处理](#7-背压限流与窗口批处理)
  - [8. 错误处理与诊断](#8-错误处理与诊断)
  - [9. 运行时选择与阻塞代码隔离](#9-运行时选择与阻塞代码隔离)
  - [10. 风格与规范（摘要）](#10-风格与规范摘要)

## 1. 基本术语

- async fn：声明异步函数，返回 `impl Future<Output = T>`。
- async 块：`async { ... }` 生成匿名 Future，便于内联组合。
- await：在异步上下文中“让出”当前任务，等待另一个 Future 完成。
- 运行时（Runtime）：如 Tokio，提供任务调度器、计时器、异步 IO 等能力。
- 任务（Task）：由运行时调度的异步执行单元；`tokio::spawn` 创建新任务。
- 并发与并行：并发是“同时进行中的多个任务”，并行是“同一时刻在不同 CPU 上执行”。

## 2. 最小可运行示例（带注释）

参见：`src/bin/async_minimal_exp01.rs`

该示例展示：

- `#[tokio::main]` 创建多线程运行时作为入口
- `async fn` 与 `await` 基本用法
- `tokio::time::sleep` 的非阻塞延迟
- 使用 `tokio::spawn` 并发执行多个任务

快速运行：

```powershell
cargo run --bin async_minimal_exp01
```

## 3. await 的语义与常见误区

- await 会“让出”当前任务执行权，不会阻塞线程；因此高并发下 CPU 能被更有效利用。
- await 只能出现在异步上下文（`async fn` 或 `async {}`）中。
- 在 `Drop` 中不要 `await`（编译器也不允许）。资源释放逻辑应保持同步或转移到异步路径。
- 不要在异步函数中执行阻塞调用（如 `std::thread::sleep` 或阻塞 IO）；需要用 `spawn_blocking` 或专用线程池。

## 4. 任务创建与结构化并发

- 动态任务集合：`tokio::task::JoinSet` 管理一批异步任务，收集结果并在出错时统一取消。
- 多路等待：`tokio::select!` 同时等待多个 Future，先完成者优先，其它分支会被自动取消（注意资源释放）。
- 组合器：`tokio::try_join!`/`tokio::join!` 并发等待多个已知 Future，前者在错误时短路。

示例：

- `src/bin/tokio_select_exp01.rs`
- `src/bin/tokio_try_join_exp01.rs`
- `src/bin/tokio_joinset_exp01.rs`

## 5. 超时、取消与截止时间

- 超时：`tokio::time::timeout(dur, fut)`；若超时返回 `Elapsed` 错误。
- 截止：用 `Instant` 与 `sleep_until(deadline)` 控制整体截止时间。
- 取消：`select!` 选中某分支后，未选中分支自动取消；也可用 `JoinSet::shutdown` 主动取消。

示例：

- `src/bin/tokio_timeout_cancel_exp01.rs`
- `src/bin/timeout_cancel_scope_exp01.rs`
- `src/bin/select_timeout_fallback_exp01.rs`

## 6. 同步原语与通道（Tokio）

- Mutex/RwLock：保护共享可变状态；仅在临界区内持锁，避免持锁执行 `await`。
- Notify：轻量级单向唤醒原语，适合条件通知。
- mpsc/oneshot/watch/broadcast：多对一/一次性/广播式消息传递，各有使用场景。

示例：

- `src/bin/tokio_sync_mutex_exp01.rs`
- `src/bin/tokio_sync_rwlock_exp01.rs`
- `src/bin/tokio_sync_notify_exp01.rs`
- `src/bin/tokio_chan_exp01.rs`、`tokio_chan_oneshot_exp01.rs`、`tokio_watch_exp01.rs`、`tokio_broadcast_exp01.rs`

## 7. 背压、限流与窗口批处理

- 首选 bounded mpsc（有容量上限），作为自然背压；避免无界队列导致 OOM。
- 用 `Semaphore` 控制并发度；失败时可退避重试或降级。
- 窗口批处理（window batching）在高吞吐流中减少开销。

示例：

- `src/bin/tokio_mpsc_backpressure_exp01.rs`
- `src/bin/semaphore_mpsc_pipeline_exp01.rs`
- `src/bin/window_batch_semaphore_exp01.rs`
- `src/bin/mpsc_backpressure_compare_exp01.rs`

## 8. 错误处理与诊断

- 推荐 `anyhow::Result<T>` 作为示例层快速落地；库层用 `thiserror` 定义细化错误。
- 异步并发下优先短路：`tokio::try_join!` 与 `?` 组合；在 `select!` 中显式处理取消与清理。
- 开启 `tracing`，打印关键路径、打点 p50/p95；开发期可选 `tokio-console`。

示例：

- `src/bin/concurrent_fetch_error_handling_exp01.rs`
- `src/bin/tracing_console_exp01.rs`

## 9. 运行时选择与阻塞代码隔离

- 统一入口：`#[tokio::main(flavor = "multi_thread")]`，根据需要调整 `worker_threads`。
- 阻塞隔离：CPU 密集或阻塞 IO 放到 `tokio::task::spawn_blocking` 或独立线程池。
- 与 Actix 集成：见 `src/bin/actix_exp01.rs` 与 `src/actix/`。

## 10. 风格与规范（摘要）

- 函数签名：精简 `async fn` 的返回类型，必要时定义显式错误类型。
- 可读性：给 `select!`/`JoinSet` 分支起清晰名字；抽出重复逻辑为小函数。
- 资源管理：避免在持锁期间 `await`；使用作用域最小化锁持有时间。

完整风格建议参见：`docs/async_style_guide.md` 与 `docs/async_best_practices.md`。

---

配套示例与更多进阶主题见：

- `docs/async_language_features_190.md`
- `docs/advanced_patterns_summary.md`
- `docs/async_rust_190_overview.md`
