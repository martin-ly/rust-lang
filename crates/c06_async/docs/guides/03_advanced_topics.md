# 异步进阶主题（Rust 1.90）：Future/Pin/Send-Sync/阻塞隔离/运行时选择

> 目标：从语言与运行时边界出发，系统解释 Future/Pin、Send/Sync、阻塞代码隔离策略、运行时（Tokio）的选择与配置，并链接到可运行示例。


## 📊 目录

- [1. Future 与手写 poll 的场景](#1-future-与手写-poll-的场景)
- [2. Pin 的不动性与何时关心](#2-pin-的不动性与何时关心)
- [3. Send/Sync 与跨线程任务](#3-sendsync-与跨线程任务)
- [4. 阻塞代码隔离](#4-阻塞代码隔离)
- [5. 运行时选择与配置](#5-运行时选择与配置)
- [6. 取消语义与资源清理](#6-取消语义与资源清理)
- [7. 可观测性与性能](#7-可观测性与性能)


## 1. Future 与手写 poll 的场景

- 大多数业务无需手写 Future；标准 async/await 足够。
- 需要自定义 Future 的典型场景：
  - 自引用结构或需要精细状态机控制
  - 与外部事件源（回调/FD）整合，提供 poll 驱动
- 关键接口：`Future::poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<T>`

参考：`src/futures/future01.rs`

## 2. Pin 的不动性与何时关心

- `Pin<&mut T>` 保证 T 在内存中的地址在被 pin 期间不变；用于自引用或底层 IO 对象。
- async/await 自动生成的状态机已处理好 Pin；普通业务无需显式使用 Pin。

## 3. Send/Sync 与跨线程任务

- 跨线程 `tokio::spawn` 需要 `Send + 'static`；否则使用 `LocalSet` 在同线程内运行。
- 常见 `!Send` 类型：`Rc<T>`、`RefCell<T>`、非线程安全 FFI 句柄。建议改为 `Arc<T>`、`Mutex/RwLock` 或设计为局部任务。

示例：`src/bin/joinset_cancel_on_error_exp01.rs`

## 4. 阻塞代码隔离

- 原则：不要在 async 任务中做阻塞操作（`std::fs::read`、`std::thread::sleep`）。
- 手段：
  - `tokio::task::spawn_blocking`：把 CPU 密集/阻塞 IO 放入专门的阻塞线程池
  - 使用异步 API（`tokio::fs`、`reqwest`）替换阻塞版本
  - 在服务边界设置超时与降级策略

示例：`src/bin/retry_backoff_exp01.rs`、`src/bin/concurrent_fetch_error_handling_exp01.rs`

## 5. 运行时选择与配置

- 入口：`#[tokio::main(flavor = "multi_thread")]` 作为默认；可按 CPU 调整 `worker_threads`
- 单线程局部执行：`LocalSet` 配合 `!Send` 任务
- 计时器、IO、调度：Tokio 提供时间轮与 mio/uring 后端，统一通过 async/await 使用

## 6. 取消语义与资源清理

- `select!` 未选中分支被取消；`JoinSet` 停止收集可触发任务结束
- 清理策略：在 `Drop` 中释放外部资源（许可、文件句柄）；必要时显式 abort 并等待回收

参考：`src/bin/timeout_cancel_scope_exp01.rs`、`src/bin/tokio_timeout_cancel_exp01.rs`

## 7. 可观测性与性能

- 启用 `tracing`，对关键路径埋点；对高并发通道与 Semaphore 配置 p50/p95 指标
- 基准：在 `benches/` 中评估 mpsc 有界容量与并发度对吞吐与尾延迟的影响

---

延伸阅读：`docs/async_language_features_190.md`、`docs/async_basics_guide.md`、`docs/advanced_patterns_summary.md`
