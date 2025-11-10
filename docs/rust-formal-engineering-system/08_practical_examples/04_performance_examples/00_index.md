# 性能示例（Performance Examples）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [性能示例（Performance Examples）索引](#性能示例performance-examples索引)
  - [📊 目录](#-目录)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [📚 核心示例](#-核心示例)
    - [1. 算法优化（Algorithm Optimization）](#1-算法优化algorithm-optimization)
    - [2. 内存优化（Memory Optimization）](#2-内存优化memory-optimization)
    - [3. 并发优化（Concurrency Optimization）](#3-并发优化concurrency-optimization)
    - [4. 编译优化（Compilation Optimization）](#4-编译优化compilation-optimization)
  - [💻 实践与样例](#-实践与样例)
    - [代码示例位置](#代码示例位置)
    - [文件级清单（精选）](#文件级清单精选)
      - [`crates/c08_algorithms/src/performance_examples/`](#cratesc08_algorithmssrcperformance_examples)
      - [`crates/c05_threads/src/performance/`](#cratesc05_threadssrcperformance)
    - [性能优化工具](#性能优化工具)
      - [基准测试](#基准测试)
      - [性能分析](#性能分析)
      - [性能监控](#性能监控)
  - [🔗 相关索引](#-相关索引)
  - [🧭 导航](#-导航)

## 🎯 目的

本模块提供 Rust 性能优化和调优的实用示例，涵盖算法优化、内存优化、并发优化和编译优化等核心主题。所有示例均基于 Rust 1.91.0 和当前最佳实践。

### 核心价值

- **性能导向**: 专注于性能优化技巧
- **最佳实践**: 基于 Rust 社区最新实践
- **完整覆盖**: 涵盖多个优化维度
- **易于理解**: 提供详细的优化说明和基准测试

## 📚 核心示例

### 1. 算法优化（Algorithm Optimization）

**推荐库**: `rayon`, `crossbeam`, `dashmap`

- **排序算法优化**: 并行排序、优化排序算法
- **搜索算法优化**: 二分搜索、哈希表优化
- **图算法优化**: 图遍历、最短路径算法
- **数值计算优化**: SIMD 优化、数值计算库

**相关资源**:

- [rayon 文档](https://docs.rs/rayon/)
- [Rust Performance Book](https://nnethercote.github.io/perf-book/)
- [SIMD in Rust](https://doc.rust-lang.org/core/arch/)

### 2. 内存优化（Memory Optimization）

**推荐库**: `bumpalo`, `jemallocator`, `smallvec`

- **内存布局优化**: 结构体布局、对齐优化
- **缓存友好代码**: 数据局部性、缓存行优化
- **内存池实现**: 内存池、对象池实现
- **零拷贝技术**: 零拷贝、内存映射

**相关资源**:

- [Rust Performance Book - Memory](https://nnethercote.github.io/perf-book/memory.html)
- [bumpalo 文档](https://docs.rs/bumpalo/)
- [smallvec 文档](https://docs.rs/smallvec/)

### 3. 并发优化（Concurrency Optimization）

**推荐库**: `tokio`, `rayon`, `crossbeam`, `parking_lot`

- **并行算法实现**: 并行处理、数据并行
- **工作窃取优化**: 工作窃取队列、任务调度
- **无锁数据结构**: 无锁队列、无锁栈
- **并发模式优化**: Actor 模式、CSP 模式

**相关资源**:

- [Tokio 文档](https://tokio.rs/)
- [rayon 文档](https://docs.rs/rayon/)
- [crossbeam 文档](https://docs.rs/crossbeam/)

### 4. 编译优化（Compilation Optimization）

**推荐工具**: `cargo build --release`, `cargo-flamegraph`, `perf`

- **内联优化**: 函数内联、内联提示
- **循环优化**: 循环展开、向量化
- **分支预测优化**: 分支预测、条件优化
- **指令级优化**: 指令选择、寄存器分配

**相关资源**:

- [Cargo Book - Profiles](https://doc.rust-lang.org/cargo/reference/profiles.html)
- [cargo-flamegraph](https://github.com/flamegraph-rs/flamegraph)
- [Rust Performance Book - Compilation](https://nnethercote.github.io/perf-book/compilation.html)

## 💻 实践与样例

### 代码示例位置

- **性能示例**: [crates/c08_algorithms](../../../crates/c08_algorithms/)
- **并发编程**: [crates/c05_threads](../../../crates/c05_threads/)
- **异步编程**: [crates/c06_async](../../../crates/c06_async/)

### 文件级清单（精选）

#### `crates/c08_algorithms/src/performance_examples/`

- `memory_optimization.rs` - 内存优化示例
- `concurrency_optimization.rs` - 并发优化示例
- `compile_time_optimization.rs` - 编译时优化示例
- `runtime_profiling.rs` - 运行时剖析示例

#### `crates/c05_threads/src/performance/`

- `high_performance_concurrency.rs` - 高性能并发
- `optimized_synchronization.rs` - 优化同步原语
- `performance_benchmarks.rs` - 性能基准测试

### 性能优化工具

#### 基准测试

- **criterion**: Rust 基准测试框架
- **iai**: 指令级基准测试
- **divan**: 快速基准测试

#### 性能分析

- **cargo-flamegraph**: 火焰图生成
- **perf**: Linux 性能分析工具
- **valgrind**: 内存分析工具

#### 性能监控

- **dhat**: 堆分析工具
- **heaptrack**: 堆跟踪工具
- **massif**: 堆分析工具

---

## 🔗 相关索引

- **理论基础（并发模型）**: [`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- **编程范式（数据导向）**: [`../../02_programming_paradigms/10_data_oriented/00_index.md`](../../02_programming_paradigms/10_data_oriented/00_index.md)
- **工具链生态（性能分析）**: [`../../06_toolchain_ecosystem/06_performance_analysis/00_index.md`](../../06_toolchain_ecosystem/06_performance_analysis/00_index.md)

---

## 🧭 导航

- **返回实用示例**: [`../00_index.md`](../00_index.md)
- **真实案例**: [`../03_real_world_cases/00_index.md`](../03_real_world_cases/00_index.md)
- **安全示例**: [`../05_security_examples/00_index.md`](../05_security_examples/00_index.md)
- **返回项目根**: [`../../README.md`](../../README.md)

---

**最后更新**: 2025-11-10
**维护者**: 项目维护者
**状态**: 已完善 ✅
