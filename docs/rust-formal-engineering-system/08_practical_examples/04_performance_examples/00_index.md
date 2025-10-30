> ⚠️ **待完善** - 此文件为占位符，内容待完善
> **最后更新**: 2025-10-31
> **预期完成**: 待定

---

﻿# 性能示例（Performance Examples）索引

## 📊 目录

- [性能示例（Performance Examples）索引](#性能示例performance-examples索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心示例](#核心示例)
    - [算法优化](#算法优化)
    - [内存优化](#内存优化)
    - [并发优化](#并发优化)
    - [编译优化](#编译优化)
  - [实践与样例](#实践与样例)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)

## 目的

- 提供 Rust 性能优化和调优的实用示例。
- 展示如何编写高性能的 Rust 代码。

## 核心示例

### 算法优化

- 排序算法优化
- 搜索算法优化
- 图算法优化
- 数值计算优化

### 内存优化

- 内存布局优化
- 缓存友好代码
- 内存池实现
- 零拷贝技术

### 并发优化

- 并行算法实现
- 工作窃取优化
- 无锁数据结构
- 并发模式优化

### 编译优化

- 内联优化
- 循环优化
- 分支预测优化
- 指令级优化

## 实践与样例

- 性能示例：参见 [crates/c08_algorithms](../../../crates/c08_algorithms/)
- 并发编程：[crates/c05_threads](../../../crates/c05_threads/)
- 异步编程：[crates/c06_async](../../../crates/c06_async/)

### 文件级清单（精选）

- `crates/c08_algorithms/src/performance_examples/`：
  - `memory_optimization.rs`：内存优化示例
  - `concurrency_optimization.rs`：并发优化示例
  - `compile_time_optimization.rs`：编译时优化示例
  - `runtime_profiling.rs`：运行时剖析示例
- `crates/c05_threads/src/performance/`：
  - `high_performance_concurrency.rs`：高性能并发
  - `optimized_synchronization.rs`：优化同步原语
  - `performance_benchmarks.rs`：性能基准测试

## 相关索引

- 理论基础（并发模型）：[`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- 编程范式（数据导向）：[`../../02_programming_paradigms/10_data_oriented/00_index.md`](../../02_programming_paradigms/10_data_oriented/00_index.md)
- 工具链生态（性能分析）：[`../../06_toolchain_ecosystem/06_performance_analysis/00_index.md`](../../06_toolchain_ecosystem/06_performance_analysis/00_index.md)

## 导航

- 返回实用示例：[`../00_index.md`](../00_index.md)
- 真实案例：[`../03_real_world_cases/00_index.md`](../03_real_world_cases/00_index.md)
- 安全示例：[`../05_security_examples/00_index.md`](../05_security_examples/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
