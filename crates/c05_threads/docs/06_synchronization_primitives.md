# 第 3 章：共享状态并发与同步原语

> **EN**: Threading / Concurrency Guide (crate example index)
> **Summary**: A stub page pointing to the canonical concept authority. General Rust explanations have been migrated to `concept/`; runnable examples remain in the crate.

> **权威来源**: 通用 Rust 概念解释已转移至 canonical authority page:
> [`concept/03_advanced/00_concurrency/01_concurrency.md`](../../../concept/03_advanced/00_concurrency/01_concurrency.md).

本文件原为对应 crate 的通用概念教程。遵循 AGENTS.md §6.4 治理规则，
通用 Rust 概念解释已转移至 `concept/`，此处仅保留索引与 canonical 链接。
具体可运行示例请参见本 crate 的 `examples/` 与 `src/bin/` 目录。

## 主题速览

- 🎯 同步原语核心知识图谱
  - 同步原语关系图
  - 同步原语决策树
- 📊 同步原语多维对比矩阵
  - 同步原语性能对比
  - 同步原语适用场景对比
  - 死锁风险对比
- 1. 共享状态并发模型
  - 1.1. 理念：通过共享内存来通信
  - 1.2. 核心挑战：数据竞争 (Data Races)
- 1. `Mutex<T>`：互斥锁
  - 2.1. 工作原理
  - 2.2. `MutexGuard` 与 RAII 模式
  - 🚀 Rust 1.92.0 Mutex 性能示例
  - 2.3. `Mutex` 的死锁风险
- 1. `Arc<T>`：原子引用计数
  - 3.1. 为何需要 `Arc`？
  - 3.2. `Arc<Mutex<T>>`：线程安全的内部可变性
- 1. `RwLock<T>`：读写锁
  - 4.1. 优化读多写少场景
  - 🚀 Rust 1.92.0 RwLock 性能示例
  - 📊 Mutex vs RwLock 性能对比
  - 4.2. 死锁与写者饥饿
- 1. `Send` 和 `Sync` Trait 的角色
  - 5.1. `Send`：所有权可以被安全地送到另一个线程
  - 5.2. `Sync`：引用可以被安全地在多线程间共享
- 1. 哲学批判性分析
  - 6.1. 复杂性的回归
  - 6.2. 性能与权衡
- 💡 思维导图：同步原语选择策略
- 📋 快速参考
  - 同步原语 API 速查
  - Rust 1.92.0 性能提升速查（自 Rust 1.90 引入）
  - Send/Sync 速查表
- 1. 总结
  - 核心优势
  - Rust 1.92.0 关键改进（自 Rust 1.90 引入）
  - 最佳实践建议
  - 性能权衡
  - 学习路径
