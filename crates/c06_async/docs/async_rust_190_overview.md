# Rust 1.90 异步语言特性与生态要点概览

> 目标：在 Rust 1.90 环境下梳理 async/await 的语法要点、诊断改进与生态使用注意事项，并对照本包示例导航。

## 1. 基础语法回顾（适用于 1.90）

- async/await：`async fn` 与 `async { ... }` 返回 `impl Future<Output = T>`；`await` 仅能在 async 上下文使用。
- Future/Pin：一般无需手写 Pin；跨线程任务需满足 `Send + 'static`。
- Stream：采用 `futures::Stream` 与 `tokio_stream`（如 `wrappers`、`iter`）。
- select/JoinSet：`tokio::select!` 多路等待；`tokio::task::JoinSet` 管理动态任务集合。

## 2. Rust 1.90 影响点（与 1.89 对比）

- 生态兼容：Tokio/futures/tracing 在 1.90 正常工作；本包代码在 1.89/1.90 均可编译运行。
- 诊断可读性：部分错误提示（trait bound/生命周期）更清晰，便于定位 `Send` 边界与 `!Send` 捕获问题。
- 工具链与解析：配合 2024 edition、`resolver = 3` 的工作区依赖解析更稳定，建议锁定 workspace 版本。

> 参阅 `docs/run_guide.md` 执行命令与 `src/bin/*` 示例对应关系。

## 3. 常见陷阱与对策

- 阻塞陷阱：CPU 密集或阻塞 I/O 放入 `spawn_blocking` 或专用线程池。
- 取消语义：`select!` 选中分支后，其它分支自动取消；使用 `Drop`/许可令牌确保资源释放。
- 背压设计：优先 bounded mpsc；必要时配合 `Semaphore` 与窗口批处理（window batching）。
- 错误传播：`anyhow::Result`/自定义错误配合 `?` 与 `try_join!`，快速失败并保留上下文。

## 4. 结构化并发与超时

- 任务作用域：以 `JoinSet`/自定义作用域统一收集结果与错误，失败即驱动整体取消。
- 截止与超时：`tokio::time::timeout`、`sleep_until`；结合重试与退避策略（见 utils）。

## 5. 示例导航（本包）

- 入门：`src/bin/tokio_select_exp01.rs`、`tokio_try_join_exp01.rs`、`tokio_joinset_exp01.rs`
- 取消/超时：`timeout_cancel_scope_exp01.rs`、`tokio_timeout_cancel_exp01.rs`
- 背压/限流：`tokio_mpsc_backpressure_exp01.rs`、`tokio_semaphore_limit_exp01.rs`、`window_batch_semaphore_exp01.rs`
- 同步原语：`tokio_sync_mutex_exp01.rs`、`tokio_sync_rwlock_exp01.rs`、`tokio_sync_notify_exp01.rs`
- 分布式/微服务：`distributed_lock_exp01.rs`、`microservice_patterns_exp01.rs`、`cloud_native_exp01.rs`

## 6. 1.90 项目检查清单

- 入口：`#[tokio::main(flavor = "multi_thread")]`；仅在需要时显式配置 `worker_threads`。
- Send 边界：跨线程 `spawn` 的闭包和捕获值满足 `Send + 'static`。
- 通道容量：为每个 mpsc 明确容量、背压策略、峰值流量假设。
- 可观测性：启用 `tracing`，打 p50/p95；开发期可用 `tokio-console`。
- 故障恢复：全链路超时、重试退避、熔断降级与隔离（bulkhead）。

---

更多风格与规范建议见：`docs/async_style_guide.md`。
