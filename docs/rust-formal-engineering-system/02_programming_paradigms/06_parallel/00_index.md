# 并行范式（Parallel Paradigm）索引


## 📊 目录

- [目的](#目的)
- [核心概念](#核心概念)
- [与 Rust 的关联](#与-rust-的关联)
- [术语（Terminology）](#术语terminology)
- [实践与样例（Practice）](#实践与样例practice)
  - [文件级清单（精选）](#文件级清单精选)
  - [关联基准与指南](#关联基准与指南)
- [相关索引](#相关索引)
- [导航](#导航)


## 目的

- 介绍 Rust 并行计算的理论基础与实现技术。
- 提供并行算法设计与性能优化的指导。

## 核心概念

- 并行计算：同时执行多个计算任务
- 数据并行：对数据集的不同部分并行处理
- 任务并行：并行执行不同的任务
- 负载均衡：合理分配计算资源
- 同步与通信：并行任务间的协调机制

## 与 Rust 的关联

- 线程池：`rayon` 数据并行库
- 并行迭代器：`par_iter` 并行处理集合
- 原子操作：无锁并行数据结构
- SIMD：单指令多数据并行

## 术语（Terminology）

- 并行（Parallelism）、数据并行（Data Parallelism）
- 任务并行（Task Parallelism）、负载均衡（Load Balancing）
- 线程池（Thread Pool）、工作窃取（Work Stealing）
- SIMD（Single Instruction, Multiple Data）

## 实践与样例（Practice）

- 并行算法：参见 [crates/c08_algorithms](../../../crates/c08_algorithms/)
- 线程与同步：[crates/c05_threads](../../../crates/c05_threads/)
- 异步编程：[crates/c06_async](../../../crates/c06_async/)

### 文件级清单（精选）

- `crates/c08_algorithms/src/`：
  - `performance_examples/memory_optimization.rs`：布局/局部性与带宽
  - `performance_examples/concurrency_optimization.rs`：并行迭代与批处理
  - `performance_examples/compile_time_optimization.rs`：内联/泛型消除开销
  - `sorting/`、`graph/`：可并行化算法骨架
- `crates/c05_threads/src/`：
  - `paralelism/numa_aware.rs`、`paralelism/advanced_parallel_algorithms.rs`

### 关联基准与指南

- 最小基准指南：[`../11_benchmark_minimal_guide.md`](../11_benchmark_minimal_guide.md)
- 同步/并行基准：[`../../../crates/c05_threads/benches/`](../../../crates/c05_threads/benches/)
- 异步/管道基准：[`../../../crates/c06_async/benches/`](../../../crates/c06_async/benches/)

## 相关索引

- 并发范式：[`../05_concurrent/00_index.md`](../05_concurrent/00_index.md)
- 理论基础（并发模型）：[`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- 应用领域（高性能计算）：[`../../04_application_domains/00_index.md`](../../04_application_domains/00_index.md)

## 导航

- 返回范式总览：[`../00_index.md`](../00_index.md)
- 并发范式：[`../05_concurrent/00_index.md`](../05_concurrent/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
