# Rust 1.89 并发/异步特性对标

## 语言与稳定面

- 所有权/借用/生命周期 与 `Send`/`Sync` 自动推导
- `Future`/`Pin`/`Waker`/`Poll` 语义，`async/await` 状态机降糖
- `Drop` 顺序、`?`/`From`/`thiserror` 错误模型
- 避免依赖未稳定特性（specialization、async Drop 等）

## 同步模型

- 线程与工作窃取（rayon 数据并行）
- 同步原语：`Mutex`/`RwLock`/`Condvar` 与 `parking_lot`
- 消息传递：`std::sync::mpsc`（教学）与 `crossbeam-channel`（工程）
- 内存序：Acquire/Release/SeqCst 与 `Atomic*`

## 异步模型

- 多运行时生态：Tokio/async-std/smol/Monoio，对 I/O/计时/调度能力的分层
- 取消与结构化并发：`CancellationToken`、`timeout`、`select`、`JoinSet`/`scope`
- 背压与容量：有界通道、信号量、Tower 中间件（限流/重试/熔断）

## 可观测性与验证

- tracing/metrics、tokio-console
- 并发验证：`loom`；属性测试：`proptest`；基准：`criterion`

## 参考

- Async Book、Rustonomicon、Tokio/Hyper/Tower 文档
- RustBelt、Stacked Borrows、Pin 设计讨论、Polonius 研究
