# 常见模式与陷阱（Rust 1.90）：并发、超时、取消、背压

> 目标：以实用为导向梳理异步并发的常见模式与易错点，覆盖 select/join/JoinSet、超时与取消传播、mpsc 背压与限流、锁使用规范，并链接到本仓的可运行示例。


## 📊 目录

- [1. 并发模式](#1-并发模式)
- [2. 超时与取消](#2-超时与取消)
- [3. 背压与限流](#3-背压与限流)
  - [并发流（buffer_unordered）](#并发流buffer_unordered)
- [4. 锁与共享状态](#4-锁与共享状态)
- [5. 错误处理与重试](#5-错误处理与重试)
- [6. 观测与调试](#6-观测与调试)


## 1. 并发模式

- 已知任务集合并发：`tokio::join!` / `try_join!`
- 动态任务集合并发：`tokio::task::JoinSet`（支持随时 spawn、统一收集结果）
- 多路等待：`tokio::select!`（先完成者优先，未选分支被取消）

示例：`src/bin/tokio_try_join_exp01.rs`、`tokio_joinset_exp01.rs`、`tokio_select_exp01.rs`

## 2. 超时与取消

- 超时包装：`tokio::time::timeout(d, fut)`
- 取消传播：用 `select!` 把错误与超时在作用域内快速传播，避免悬挂
- 资源清理：取消后的分支要在 Drop 中释放资源（如信号量许可）

示例：`src/bin/tokio_timeout_cancel_exp01.rs`、`timeout_cancel_scope_exp01.rs`、`select_timeout_fallback_exp01.rs`

## 3. 背压与限流

- 首选有界 mpsc：容量代表系统能承受的在途请求上限
- 限流：`Semaphore` 控制并发度；与窗口批处理结合以稳态吞吐
- 避免：无界队列在峰值下可能 OOM；使用 backpressure 反馈给上游

示例：`src/bin/tokio_mpsc_backpressure_exp01.rs`、`semaphore_mpsc_pipeline_exp01.rs`、`mpsc_backpressure_compare_exp01.rs`

### 并发流（buffer_unordered）

- 对一组异步任务构造流，`buffer_unordered(N)` 控制同时在途的任务数为 N，结果乱序到达
- 适合高并发抓取/处理场景；结合有界通道或限流器形成稳态背压

示例：`src/bin/stream_buffer_unordered_exp01.rs`

## 4. 锁与共享状态

- 避免持锁 await：容易造成死锁与长时间饥饿；应缩小临界区或复制数据到局部
- RwLock 读多写少场景更合适；Mutex 对简单互斥最直接
- `Notify` 用于条件通知，替代忙等

示例：`src/bin/tokio_sync_mutex_exp01.rs`、`tokio_sync_rwlock_exp01.rs`、`tokio_sync_notify_exp01.rs`

## 5. 错误处理与重试

- 并发组合优先用 `try_join!` 短路失败
- 重试需设置上限与退避；与超时组合成“快速失败 + 有界重试”

示例：`src/bin/retry_backoff_exp01.rs`、`concurrent_fetch_error_handling_exp01.rs`

## 6. 观测与调试

- 对关键路径埋点：请求进入、出队、开始处理、完成/失败；打 p50/p95
- 开发期可用 `tracing` + `tokio-console`

---

延伸阅读：`docs/async_best_practices.md`、`docs/async_style_guide.md`、`docs/async_advanced_topics.md`
