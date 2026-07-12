# Rust 2025 线程同步机制

> **EN**: Threading / Concurrency Guide (crate example index)
> **Summary**: A stub page pointing to the canonical concept authority. General Rust explanations have been migrated to `concept/`; runnable examples remain in the crate.

> **权威来源**: 通用 Rust 概念解释已迁移至 canonical authority page:
> [`concept/03_advanced/00_concurrency/01_concurrency.md`](../../../concept/03_advanced/00_concurrency/01_concurrency.md).

本文件原为对应 crate 的通用概念教程。根据 AGENTS.md §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/`，此处仅保留索引与 canonical 链接。
具体可运行示例请参见本 crate 的 `examples/` 与 `src/bin/` 目录。

## 主题速览

- 🎯 同步原语核心知识图谱
  - 同步原语关系图
  - 同步原语决策树
- 📊 同步原语多维对比矩阵
  - 同步原语性能对比
  - 同步原语适用场景对比
  - 死锁风险对比
- 1. 概述
  - 1.1 同步原语分类
  - 1.2 死锁预防
- 1. 互斥锁 (Mutex)
  - 2.1 基本Mutex使用
  - 2.2 递归Mutex
- 1. 读写锁 (RwLock)
  - 3.1 基本RwLock使用
- 1. 条件变量 (Condition Variable)
  - 4.1 基本条件变量
- 1. 信号量 (Semaphore)
  - 5.1 基本信号量
- 1. 屏障 (Barrier)
  - 6.1 基本屏障
- 1. 原子操作 (Atomic)
  - 7.1 基本原子类型
- 1. 最佳实践
  - 8.1 锁的粒度
  - 8.2 避免死锁
- 1. 总结
  - 9.1 关键要点
  - 9.2 最佳实践
