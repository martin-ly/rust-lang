# 同步范式（Synchronous Paradigm）索引


## 📊 目录

- [目的](#目的)
- [术语](#术语)
- [核心概念](#核心概念)
- [实践与示例（仓库内）](#实践与示例仓库内)
  - [文件级清单（精选）](#文件级清单精选)
  - [具体示例（可点击）](#具体示例可点击)
- [设计建议](#设计建议)
- [常见陷阱](#常见陷阱)
- [渐进迁移清单（同步 → 异步）](#渐进迁移清单同步-异步)
- [参考资料](#参考资料)
- [最小模板提示](#最小模板提示)
- [导航](#导航)


## 目的

- 明确同步执行模型在 Rust 的定位与适用场景。
- 统一同步相关术语，建立与异步、并发模型的映射关系。
- 汇总仓库中与同步范式相关的示例与深度文章。

## 术语

- 同步（Synchronous）：调用方在当前线程阻塞直至结果就绪。
- 阻塞 I/O（Blocking I/O）：系统调用占用线程直至完成。
- 直线化控制流（Straight-line control flow）：顺序执行，控制流无显式调度点。
- 同步并发（Synchronous Concurrency）：通过多线程和阻塞原语实现的并发。

## 核心概念

- 执行模型：主线程→函数调用→阻塞/返回；避免复杂调度器开销。
- 线程与栈：每个线程持有独立栈帧；调用链易于调试与剖析。
- 同步原语：`Mutex`、`RwLock`、`Condvar`、`Barrier`、`mpsc` 等。
- I/O 策略：小规模并发或 I/O 比例低的任务优先采用同步。
- 与异步对比：小而快的场景同步优势明显；大规模 I/O 并发异步更优。

## 实践与示例（仓库内）

- 基础并发与同步原语：参见 `crates/c05_threads/src/` 与示例 `crates/c05_threads/examples/`。
- 控制流与函数：参见 `crates/c03_control_fn/src/`。
- 算法与 I/O 核心路径同步实现：参见 `crates/c08_algorithms/src/`。
- 基准参考：参见 `crates/c05_threads/benches/`（线程/锁/通道开销对比）。

### 文件级清单（精选）

- 示例（`crates/c05_threads/examples/`）：
  - `message_passing_demo.rs`：标准库 channel、crossbeam mpsc、watch 对比
  - `priority_channels_demo.rs`：带优先级的消息传递
  - `stream_backpressure_demo.rs`：同步流 + 丢弃型背压
  - `stream_rate_batch_demo.rs`：限速与批处理消费
  - `backpressure_overview_demo.rs`：四种背压策略行为对比
- 基准（`crates/c05_threads/benches/`）：
  - `concurrency_benchmark.rs`：线程/锁/通道基准
  - `priority_channels_bench.rs`：优先级通道吞吐
  - `backpressure_bench.rs`：不同背压策略性能

### 具体示例（可点击）

- 线程基础与演示：[`c05_threads/src/bin/basic_threads_demo.rs`](../../../crates/c05_threads/src/bin/basic_threads_demo.rs) ・ [`c05_threads/src/threads/creation/mod.rs`](../../../crates/c05_threads/src/threads/creation/mod.rs)
- 线程管理与 Join：[`c05_threads/src/threads/joining/mod.rs`](../../../crates/c05_threads/src/threads/joining/mod.rs)
- 线程池与调度：[`c05_threads/src/threads/thread_pool/mod.rs`](../../../crates/c05_threads/src/threads/thread_pool/mod.rs) ・ [`c05_threads/src/concurrency/work_stealing.rs`](../../../crates/c05_threads/src/concurrency/work_stealing.rs)
- 同步原语集合：[`c05_threads/src/synchronization/mutex/mod.rs`](../../../crates/c05_threads/src/synchronization/mutex/mod.rs) ・ [`rw_lock`](../../../crates/c05_threads/src/synchronization/rw_lock/mod.rs) ・ [`condvar`](../../../crates/c05_threads/src/synchronization/condition_variable/mod.rs) ・ [`barrier`](../../../crates/c05_threads/src/synchronization/barrier/mod.rs)
- 消息传递与背压：[`c05_threads/src/message_passing/mpsc/mod.rs`](../../../crates/c05_threads/src/message_passing/mpsc/mod.rs) ・ [`backpressure_handling.rs`](../../../crates/c05_threads/src/message_passing/backpressure_handling.rs)
- 无锁结构：[`lockfree_queue.rs`](../../../crates/c05_threads/src/lockfree/lockfree_queue.rs) ・ [`lockfree_stack.rs`](../../../crates/c05_threads/src/lockfree/lockfree_stack.rs)
- 性能基准入口：[`benches/concurrency_benchmark.rs`](../../../crates/c05_threads/benches/concurrency_benchmark.rs) ・ [`benches/backpressure_bench.rs`](../../../crates/c05_threads/benches/backpressure_bench.rs) ・ [`benches/priority_channels_bench.rs`](../../../crates/c05_threads/benches/priority_channels_bench.rs)

> 如有新增示例或文档，请在本索引追加链接与简述。

## 设计建议

- 以同步为默认：在未证明异步可显著受益前，优先同步实现。
- 清晰的边界：在 I/O 层或适配器层进行同步/异步边界切换。
- 可观测性：同步路径优先纳入度量（计时、日志、火焰图）。
- 退化路径：为异步系统准备同步退化实现，便于调试与应急。

## 常见陷阱

- 在持锁区域调用可能阻塞的 I/O，导致长时间锁占用与级联延迟。
- 在同步路径中错误地混入异步 API（或反之）造成死锁或饥饿。
- 线程爆炸：为每个请求创建线程而未限制并发与队列容量。
- 忽略超时/取消：阻塞调用缺乏超时与中断机制，导致资源泄漏。
- 使用无背压的 `mpsc`/队列，使生产速度远超消费能力。

## 渐进迁移清单（同步 → 异步）

1. 度量 I/O 等待时间与连接数量，识别真正的异步收益点。
2. 在 I/O 边界引入异步适配层，保持核心业务仍为同步实现。
3. 将阻塞 I/O 封装为接口，提供异步实现（或通过运行时适配）。
4. 批量化/限速/超时策略先就位，再扩大异步覆盖面。
5. 建立回退路径：异步失效时可切换到同步降级模式。

## 参考资料

- Rust 标准库并发原语：`std::sync`、`std::thread`、`std::sync::mpsc`
- Rust 异步对照阅读：`crates/c06_async/README.md`
- 并发设计权衡：Amdahl 定律、C10K/C10M 背景资料

## 最小模板提示

- 建议子文档均包含：目的、术语、核心概念、实践、参考、导航。
- 新增示例后，请在本页“实践与示例”或上级总索引补充链接。

## 导航

- 返回总索引：[`../00_index.md`](../00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
- 异步范式：[`../02_async/00_index.md`](../02_async/00_index.md)
- 线程与并发（示例）：[`../../../crates/c05_threads/`](../../../crates/c05_threads/)
