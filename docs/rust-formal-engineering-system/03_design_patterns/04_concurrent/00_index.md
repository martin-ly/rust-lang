> ⚠️ **待完善** - 此文件为占位符，内容待完善
> **最后更新**: 2025-10-31
> **预期完成**: 待定

---

﻿# 并发模式（Concurrent Patterns）索引

## 📊 目录

- [并发模式（Concurrent Patterns）索引](#并发模式concurrent-patterns索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心模式](#核心模式)
  - [Rust 化要点](#rust-化要点)
  - [术语（Terminology）](#术语terminology)
  - [实践与样例（Practice）](#实践与样例practice)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)

## 目的

- 介绍并发编程中的设计模式在 Rust 中的实现与应用。
- 提供并发安全与性能优化的最佳实践。

## 核心模式

- 生产者-消费者模式（Producer-Consumer）：异步数据处理
- 读者-写者模式（Reader-Writer）：读写分离
- 工作窃取模式（Work Stealing）：负载均衡
- 无锁数据结构（Lock-Free Data Structures）：高性能并发
- 信号量模式（Semaphore）：资源访问控制
- 屏障模式（Barrier）：同步点协调
- 条件变量模式（Condition Variable）：等待-通知机制

## Rust 化要点

- 所有权与借用：通过所有权系统防止数据竞争
- `Send`/`Sync` 标记：跨线程安全保证
- 零成本抽象：并发原语的零成本抽象
- 结构化并发：任务生命周期管理

## 术语（Terminology）

- 并发模式（Concurrent Patterns）
- 生产者-消费者（Producer-Consumer）
- 读者-写者（Reader-Writer）
- 工作窃取（Work Stealing）
- 无锁（Lock-Free）、信号量（Semaphore）
- 屏障（Barrier）、条件变量（Condition Variable）

## 实践与样例（Practice）

- 并发编程：参见 [crates/c05_threads](../../../crates/c05_threads/)
- 异步编程：[crates/c06_async](../../../crates/c06_async/)
- 分布式系统：[crates/c20_distributed](../../../crates/c20_distributed/)

### 文件级清单（精选）

- `crates/c05_threads/src/concurrency/`：
  - `work_stealing.rs`：工作窃取模式实现
  - `producer_consumer.rs`：生产者-消费者模式
  - `reader_writer.rs`：读者-写者模式
- `crates/c05_threads/src/synchronization/`：
  - `semaphore.rs`：信号量模式
  - `barrier.rs`：屏障模式
  - `condition_variable.rs`：条件变量模式
- `crates/c05_threads/src/lockfree/`：
  - `lockfree_queue.rs`：无锁队列
  - `lockfree_stack.rs`：无锁栈

## 相关索引

- 理论基础（并发模型）：[`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- 编程范式（并发）：[`../../02_programming_paradigms/05_concurrent/00_index.md`](../../02_programming_paradigms/05_concurrent/00_index.md)
- 质量保障（并发测试）：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

## 导航

- 返回设计模式：[`../00_index.md`](../00_index.md)
- 并行模式：[`../05_parallel/00_index.md`](../05_parallel/00_index.md)
- 分布式模式：[`../06_distributed/00_index.md`](../06_distributed/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
