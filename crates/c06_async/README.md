# c06_async - Rust 1.89 异步专题

本包系统演示 Rust 1.89 语境下的异步编程（Tokio/futures 生态）：

- 基础：async/await、Future/Stream、Tokio 运行时
- 并发：select/try_join/JoinSet、结构化并发
- 同步：Mutex/RwLock/Notify、mpsc/oneshot
- 控制：超时、取消、限流（Semaphore）、背压（bounded mpsc）
- I/O 并发：buffer_unordered 并发抓取、错误处理
- 调试与观测：tracing、（可选）tokio-console
- 批处理与调度：窗口批处理、管道限速
- 基准：mpsc bounded vs unbounded、Semaphore 管道吞吐
- 工具：utils（重试/超时/限流），可复用

## 快速上手

Windows PowerShell：

```powershell
cd .\crates\c06_async
cargo build
```

运行示例（更多见 docs/run_guide.md）：

```powershell
cargo run --bin tokio_select_exp01
cargo run --bin tokio_try_join_exp01
cargo run --bin tokio_joinset_exp01
cargo run --bin tokio_timeout_cancel_exp01
cargo run --bin tracing_console_exp01
cargo run --bin tokio_select_prefs_exp01
cargo run --bin cancel_propagation_exp01
cargo run --bin select_timeout_fallback_exp01
cargo run --bin tokio_semaphore_limit_exp01
cargo run --bin tokio_mpsc_backpressure_exp01
cargo run --bin semaphore_mpsc_pipeline_exp01
cargo run --bin mpsc_backpressure_compare_exp01
cargo run --bin concurrent_fetch_error_handling_exp01
cargo run --bin window_batch_semaphore_exp01
cargo run --bin retry_backoff_exp01
cargo run --bin task_scope_structured_concurrency_exp01
cargo run --bin actix_web_exp01
```

基准（仅编译或运行）：

```powershell
cargo bench --no-run
# cargo bench
```

更多说明：

- 运行指南：`docs/run_guide.md`
- 最佳实践：`docs/async_best_practices.md`
