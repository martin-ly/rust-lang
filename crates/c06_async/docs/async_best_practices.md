# Rust 异步最佳实践（多线程/多任务）

- 并发控制：优先使用 `Semaphore` 限流；通道容量应与处理速率匹配。
- 背压策略：`mpsc::channel`（有界）可传递背压；`unbounded` 适合少量突发但需注意内存增长。
- 取消与超时：统一使用 `timeout` + 取消信号（如 `AbortHandle`）在出错/超时时快速收尾。
- 结构化并发：使用 `JoinSet` 在作用域内启动/等待任务；出错时 `abort_all`。
- select 策略：必要时用 `biased;` 控制偏好；为每分支设计超时/降级路径。
- I/O 并发：`buffer_unordered` 合理设置并发度；对失败结果分类处理。
- 批处理与限速：窗口化 + `Semaphore` 控制批量处理并发与节奏。
- 观测与调试：集成 `tracing`，必要时配合 console/metrics；记录超时和取消原因。

参见示例：`*_exp01.rs` 系列与 `benches/async_benches.rs`。
