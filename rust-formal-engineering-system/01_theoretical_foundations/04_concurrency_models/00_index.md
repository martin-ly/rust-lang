# 并发模型（Concurrency Models）索引

## 目的

- 梳理 Rust 并发编程的理论基础与实现模型。
- 对比不同并发模型的适用场景与性能特征。

## 核心概念

- 线程模型：OS 线程、绿色线程、异步任务
- 同步原语：互斥锁、读写锁、条件变量、信号量
- 消息传递：通道、Actor 模型、CSP 模型
- 内存模型：原子操作、内存序、数据竞争
- 结构化并发：任务生命周期管理、取消机制

## 与 Rust 的关联

- 所有权与借用：天然防止数据竞争
- `Send`/`Sync` 标记：跨线程安全保证
- 异步编程：Future/async-await 模型
- 零成本抽象：并发原语的零成本抽象

## 术语（Terminology）

- 并发（Concurrency）、并行（Parallelism）
- 数据竞争（Data Race）、竞态条件（Race Condition）
- 原子操作（Atomic Operation）、内存序（Memory Ordering）
- 结构化并发（Structured Concurrency）

## 形式化与证明（Formalization）

- 数据竞争自由：`∀r1, r2. ¬(write(r1) ∧ access(r2) ∧ alias(r1, r2))`
- 内存一致性：基于 C++11 内存模型
- 死锁检测：通过所有权系统避免循环等待

## 实践与样例（Practice）

- 线程与同步：参见 [crates/c05_threads](../../../crates/c05_threads/)
- 异步编程：[crates/c06_async](../../../crates/c06_async/)
- 分布式系统：[crates/c20_distributed](../../../crates/c20_distributed/)

## 相关索引

- 内存安全：[`../02_memory_safety/00_index.md`](../02_memory_safety/00_index.md)
- 所有权与借用：[`../03_ownership_borrowing/00_index.md`](../03_ownership_borrowing/00_index.md)
- 编程范式（并发）：[`../../02_programming_paradigms/05_concurrent/00_index.md`](../../02_programming_paradigms/05_concurrent/00_index.md)

## 导航

- 返回理论基础：[`../00_index.md`](../00_index.md)
- 编程范式：[`../../02_programming_paradigms/00_index.md`](../../02_programming_paradigms/00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
