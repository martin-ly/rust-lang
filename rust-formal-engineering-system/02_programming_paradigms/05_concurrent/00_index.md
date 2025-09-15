# 并发范式（Concurrent Paradigm）索引

## 目的

- 梳理 Rust 并发编程的核心概念与实现模式。
- 对比不同并发模型的适用场景与性能特征。

## 核心概念

- 并发 vs 并行：并发是同时处理多个任务，并行是同时执行多个任务
- 线程模型：OS 线程、绿色线程、异步任务
- 同步原语：互斥锁、读写锁、条件变量、信号量
- 消息传递：通道、Actor 模型、CSP 模型
- 内存模型：原子操作、内存序、数据竞争

## 与 Rust 的关联

- 所有权与借用：天然防止数据竞争
- `Send`/`Sync` 标记：跨线程安全保证
- 零成本抽象：并发原语的零成本抽象
- 结构化并发：任务生命周期管理

## 术语（Terminology）

- 并发（Concurrency）、并行（Parallelism）
- 数据竞争（Data Race）、竞态条件（Race Condition）
- 原子操作（Atomic Operation）、内存序（Memory Ordering）
- 结构化并发（Structured Concurrency）

## 实践与样例（Practice）

- 线程与同步：参见 [crates/c05_threads](../../../crates/c05_threads/)
- 异步编程：[crates/c06_async](../../../crates/c06_async/)
- 分布式系统：[crates/c20_distributed](../../../crates/c20_distributed/)

## 相关索引

- 理论基础（并发模型）：[`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- 同步范式：[`../01_synchronous/00_index.md`](../01_synchronous/00_index.md)
- 异步范式：[`../02_async/00_index.md`](../02_async/00_index.md)

## 导航

- 返回范式总览：[`../00_index.md`](../00_index.md)
- 同步范式：[`../01_synchronous/00_index.md`](../01_synchronous/00_index.md)
- 异步范式：[`../02_async/00_index.md`](../02_async/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
