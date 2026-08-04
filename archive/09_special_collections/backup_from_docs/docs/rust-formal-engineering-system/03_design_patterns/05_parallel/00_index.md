# 并行模式（Parallel Patterns）索引

## 📊 目录

- [并行模式（Parallel Patterns）索引](#并行模式parallel-patterns索引)
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

- 介绍并行计算中的设计模式在 Rust 中的实现与应用。
- 提供并行算法设计与性能优化的最佳实践。

## 核心模式

- 数据并行模式（Data Parallel）：数据集并行处理
- 任务并行模式（Task Parallel）：任务并行执行
- 流水线模式（Pipeline）：数据流并行处理
- 分治模式（Divide and Conquer）：问题分解与合并
- 映射-归约模式（Map-Reduce）：分布式计算
- 扇出-扇入模式（Fan-out/Fan-in）：数据分发与聚合
- 并行扫描模式（Parallel Scan）：前缀和计算

## Rust 化要点

- 线程池：`rayon` 数据并行库
- 并行迭代器：`par_iter` 并行处理集合
- 原子操作：无锁并行数据结构
- SIMD：单指令多数据并行

## 术语（Terminology）

- 并行模式（Parallel Patterns）
- 数据并行（Data Parallel）、任务并行（Task Parallel）
- 流水线（Pipeline）、分治（Divide and Conquer）
- 映射-归约（Map-Reduce）、扇出-扇入（Fan-out/Fan-in）
- 并行扫描（Parallel Scan）

## 实践与样例（Practice）

- 并行算法：参见 [crates/c08_algorithms](../../../crates/c08_algorithms/)
- 线程与同步：[crates/c05_threads](../../../crates/c05_threads/)
- 异步编程：[crates/c06_async](../../../crates/c06_async/)

### 文件级清单（精选）

- `crates/c08_algorithms/src/performance_examples/`：
  - `concurrency_optimization.rs`：并行迭代与批处理
  - `memory_optimization.rs`：缓存友好布局
  - `compile_time_optimization.rs`：零成本抽象
- `crates/c05_threads/src/paralelism/`：
  - `numa_aware.rs`：NUMA 感知并行
  - `advanced_parallel_algorithms.rs`：高级并行算法

## 相关索引

- 理论基础（并发模型）：[`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- 编程范式（并行）：[`../../02_programming_paradigms/06_parallel/00_index.md`](../../02_programming_paradigms/06_parallel/00_index.md)
- 应用领域（高性能计算）：[`../../04_application_domains/00_index.md`](../../04_application_domains/00_index.md)

## 导航

- 返回设计模式：[`../00_index.md`](../00_index.md)
- 并发模式：[`../04_concurrent/00_index.md`](../04_concurrent/00_index.md)
- 分布式模式：[`../06_distributed/00_index.md`](../06_distributed/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
