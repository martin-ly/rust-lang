# 同步范式（Synchronous Paradigm）索引

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

> 如有新增示例或文档，请在本索引追加链接与简述。

## 设计建议

- 以同步为默认：在未证明异步可显著受益前，优先同步实现。
- 清晰的边界：在 I/O 层或适配器层进行同步/异步边界切换。
- 可观测性：同步路径优先纳入度量（计时、日志、火焰图）。
- 退化路径：为异步系统准备同步退化实现，便于调试与应急。

## 参考资料

- Rust 标准库并发原语：`std::sync`、`std::thread`、`std::sync::mpsc`
- Rust 异步对照阅读：`crates/c06_async/README.md`
- 并发设计权衡：Amdahl 定律、C10K/C10M 背景资料

## 导航

- 返回根：[`rust-formal-engineering-system/README.md`](../../README.md)
- 异步范式：[`02_programming_paradigms/02_async/`](../02_async/)
- 线程与并发（示例）：[`crates/c05_threads/`](../../../crates/c05_threads/)
