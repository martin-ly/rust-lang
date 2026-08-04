# 数据导向范式（Data-Oriented Paradigm）索引

## 📊 目录

- [数据导向范式（Data-Oriented Paradigm）索引](#数据导向范式data-oriented-paradigm索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [术语](#术语)
  - [核心概念](#核心概念)
  - [实践与示例（仓库内）](#实践与示例仓库内)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [设计建议](#设计建议)
  - [与基准/观测的交叉链接](#与基准观测的交叉链接)
  - [导航](#导航)

## 目的

- 阐述以数据布局与访问模式为中心的设计方法在 Rust 中的落地方式。
- 给出与面向对象/函数式/并行计算的协作边界与选择建议。
- 汇总仓库内相关示例与可复用的实践清单。

## 术语

- 数据导向设计（Data-Oriented Design, DOD）：围绕数据布局、带宽与缓存友好性组织代码。
- SoA/ AoS：Structure of Arrays / Array of Structures 的存储布局权衡。
- 局部性（Locality）：时间/空间局部性；缓存命中率。
- 载体类型：`Vec<T>`、`SmallVec`、`VecDeque`、`Box<[T]>`、`Arc<[T]>`。
- ECS：实体-组件-系统（Entity-Component-System）架构。

## 核心概念

- 布局优先：以热路径的数据访问为中心选择 AoS/SoA/混合布局。
- 紧凑表示：偏移/索引替代指针；稠密集合（dense set）。
- 批处理与流水：批量处理、最小化分支、SIMD 友好。
- 借用与别名：以切片/索引表达只读/可变访问，减少别名复杂度。
- 错误与边界：越界/未对齐/未初始化内存的安全封装。

## 实践与示例（仓库内）

- 算法与数据结构：`crates/c08_algorithms/`（迭代器、并行迭代、SIMD 场景）。
- 并行与线程：`crates/c05_threads/`、`crates/c06_async/`（数据管线/流式处理）。
- 性能专题：`crates/c03_control_fn/`、`crates/c04_generic/` 中零成本抽象示例。

### 文件级清单（精选）

- `crates/c08_algorithms/src/performance_examples/`：
  - `memory_optimization.rs`：缓存友好布局与 SoA/AoS 对照
  - `concurrency_optimization.rs`：批处理与并行迭代的布局影响
  - `compile_time_optimization.rs`：零成本抽象与内联展开
  - `runtime_profiling.rs`：运行时剖析辅助定位数据热区
- `crates/c03_control_fn/src/performance_optimization_189.rs`：控制流与性能热点示例
- `crates/c04_generic/src/`：`polymorphism/generic_trait.rs`、`trait_bound/*` 展示零成本抽象对布局与内联的影响

## 相关索引

- 并行范式：[`../06_parallel/00_index.md`](../06_parallel/00_index.md)
- 并发范式：[`../05_concurrent/00_index.md`](../05_concurrent/00_index.md)
- 函数式范式：[`../03_functional/00_index.md`](../03_functional/00_index.md)
- 理论基础（内存与所有权）：[`../../01_theoretical_foundations/02_memory_safety/00_index.md`](../../01_theoretical_foundations/02_memory_safety/00_index.md)、[`../../01_theoretical_foundations/03_ownership_borrowing/00_index.md`](../../01_theoretical_foundations/03_ownership_borrowing/00_index.md)

## 设计建议

- 用基准驱动布局：以 p50/p95、带宽、缓存命中率作为主指标。
- 优先稠密结构：在热路径中减少指针追踪与小对象分配。
- 读写分离：只读切片与可变切片明确边界，批量变更。
- 先简后优：先得到正确的 AoS，再在热点引入 SoA 或 ECS。

## 与基准/观测的交叉链接

- 最小基准指南：[`../11_benchmark_minimal_guide.md`](../11_benchmark_minimal_guide.md)
- 并行/线程基准：[`../../../crates/c05_threads/benches/`](../../../crates/c05_threads/benches/)
- 异步基准：[`../../../crates/c06_async/benches/`](../../../crates/c06_async/benches/)

## 导航

- 返回范式总览：[`../00_index.md`](../00_index.md)
- 并行范式：[`../06_parallel/00_index.md`](../06_parallel/00_index.md)
- 并发范式：[`../05_concurrent/00_index.md`](../05_concurrent/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
