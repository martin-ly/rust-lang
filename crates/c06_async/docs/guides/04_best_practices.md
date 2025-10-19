# Rust 异步最佳实践（多线程/多任务）

## 1. 并发与背压

- 通道容量匹配吞吐：生产速率 ≤ 消费速率 × 容量/延迟；优先 bounded mpsc
- 限流优先级：先 `Semaphore` 控并发，再按需速率限制（token bucket/interval）
- 并发流：`buffer_unordered(N)` 控制在途 N 个，配合有界队列形成稳态

示例：`tokio_mpsc_backpressure_exp01.rs`、`semaphore_mpsc_pipeline_exp01.rs`、`stream_buffer_unordered_exp01.rs`

## 2. 结构化并发

- 入口统一：`#[tokio::main(flavor = "multi_thread")]`
- 动态集合：`JoinSet` 收集结果，错误即触发作用域内取消
- 已知组合：优先 `try_join!` 短路错误

示例：`tokio_joinset_exp01.rs`、`tokio_try_join_exp01.rs`

## 3. 超时与取消

- 外层总超时：请求级/批次级；内层步骤分别设置合理超时
- 取消传播：`select!` 驱动快速收敛；Drop 中释放资源（许可、FD）
- 统一工具：封装 `with_timeout` + `CancelScope` 形成一致语义

示例：`tokio_timeout_cancel_exp01.rs`、`timeout_cancel_scope_exp01.rs`

## 4. 错误处理与重试

- 错误分级：可重试（5xx/网络抖动）vs 不可重试（4xx/语义错误）
- 重试上限 + 指数退避；结合熔断避免雪崩
- 日志要带上下文：URL、重试次数、最终失败原因

示例：`retry_backoff_exp01.rs`、`concurrent_fetch_error_handling_exp01.rs`

## 5. 共享状态与锁

- 避免持锁 await；缩小临界区
- 读多写少用 `RwLock`；需要原子复合操作用 `Mutex` + 批量处理
- 事件通知用 `Notify`，替代忙等

示例：`tokio_sync_mutex_exp01.rs`、`tokio_sync_rwlock_exp01.rs`、`tokio_sync_notify_exp01.rs`

## 6. !Send 与 LocalSet

- `Rc/RefCell` 等 !Send 放在 `LocalSet`；跨线程必须 `Send + 'static`
- 与运行时交叉时，明确切换边界（`spawn_local` vs `spawn`）

示例：`localset_nonsend_exp01.rs`

## 7. 可观测性

- `tracing` 埋点：入队/出队/开始/结束/错误；统计 p50/p95
- 开发期可启用 `tokio-console`；生产接入 metrics 导出

示例：`tracing_console_exp01.rs`

## 8. 性能与基准

- 在 `benches/async_benches.rs` 参数化并发度与容量；记录吞吐与尾延迟
- 报告落地至 `docs/benchmark_results.md`，与配置联动

## 9. 代码风格

- 小函数、显式命名、早返回；出错路径和取消路径显式
- 避免在持锁与 Drop 内复杂逻辑

参见：`docs/async_style_guide.md`、`docs/async_advanced_topics.md`
