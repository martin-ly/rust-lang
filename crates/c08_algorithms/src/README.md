# C08 Algorithms - 源代码结构文档

> **版本**: 0.2.0
> **Rust版本**: 1.97.0+
> **最后更新**: 2025-12-25

## 📋 概述

本文档详细说明 `c08_algorithms` 库的源代码组织结构，帮助开发者理解代码架构和模块关系。

## 🗂️ 目录结构

```
src/
├── lib.rs                          # 库入口文件，导出所有公共模块
├── bin/                            # 二进制程序
│   ├── main.rs                     # 主程序入口
│   └── bench_report.rs             # 基准测试报告生成工具
│
├── algorithms/                     # 🎯 核心算法模块（主题化组织）
│   ├── mod.rs                      # 算法模块入口
│   ├── sorting/                    # 排序算法
│   │   ├── mod.rs
│   │   ├── sync.rs                 # 同步排序实现
│   │   ├── parallel.rs             # 并行排序实现
│   │   ├── async_exec.rs           # 异步排序实现
│   │   └── distributed.rs           # 分布式排序实现
│   ├── searching/                  # 搜索算法
│   │   └── mod.rs
│   ├── graph/                      # 图算法
│   │   └── mod.rs
│   ├── dynamic_programming/        # 动态规划
│   │   └── mod.rs
│   ├── divide_and_conquer/         # 分治算法
│   │   └── mod.rs
│   ├── greedy/                     # 贪心算法
│   │   └── mod.rs
│   ├── backtracking/               # 回溯算法
│   │   └── mod.rs
│   ├── string_algorithms/          # 字符串算法
│   │   └── mod.rs
│   ├── number_theory/              # 数论算法
│   │   └── mod.rs
│   ├── geometry/                   # 几何算法
│   │   └── mod.rs
│   ├── machine_learning/           # 机器学习算法
│   │   └── mod.rs
│   ├── optimization/               # 优化算法
│   │   └── mod.rs
│   ├── combinatorics/              # 组合数学
│   │   └── mod.rs
│   ├── execution_modes/             # 执行模式（同步/并行/异步/分布式）
│   │   ├── mod.rs
│   │   ├── sync.rs
│   │   ├── parallel.rs
│   │   ├── async_exec.rs
│   │   └── distributed.rs
│   ├── verification/                # 形式化验证
│   │   ├── mod.rs
│   │   ├── formal_proofs.rs        # 形式化证明
│   │   ├── correctness.rs          # 正确性验证
│   │   └── complexity_analysis.rs  # 复杂度分析
│   ├── performance/                # 性能分析
│   │   ├── mod.rs
│   │   ├── benchmarking.rs         # 基准测试
│   │   ├── profiling.rs            # 性能分析
│   │   └── optimization.rs         # 性能优化
│   ├── knowledge_base/             # 算法知识体系
│   │   ├── mod.rs
│   │   ├── theory.rs               # 理论知识
│   │   ├── applications.rs         # 应用场景
│   │   └── best_practices.rs       # 最佳实践
│   ├── formal_verification_examples.rs  # 形式化验证示例
│   ├── rust_2024_features.rs       # Rust 2024 特性应用
│   └── rust_2025_features.rs       # Rust 2025 特性应用
│
├── topics/                         # 🎨 主题化算法模块（高级抽象）
│   ├── mod.rs                      # 主题模块入口
│   ├── sorting/                    # 排序主题
│   │   └── mod.rs
│   ├── searching/                  # 搜索主题
│   │   └── mod.rs
│   └── formal_verification/        # 形式化验证主题
│       └── mod.rs
│
├── leetcode/                       # 📚 LeetCode 分类算法模块
│   ├── mod.rs                      # LeetCode 模块入口
│   ├── array.rs                    # 数组类算法（14个）
│   ├── string_algorithms.rs        # 字符串算法（11个）
│   ├── hash_table.rs               # 哈希表算法（13个）
│   ├── dynamic_programming.rs      # 动态规划（10个）
│   ├── two_pointers.rs             # 双指针（9个）
│   ├── binary_search.rs            # 二分查找（11个）
│   ├── sliding_window.rs           # 滑动窗口（10个）
│   ├── stack.rs                    # 栈算法（6个）
│   ├── heap.rs                     # 堆算法（7个）
│   ├── tree.rs                     # 树算法（15个）
│   ├── graph.rs                    # 图算法（8个）
│   ├── backtracking.rs            # 回溯算法（11个）
│   ├── trie.rs                     # 字典树（4个）
│   ├── bit_manipulation.rs         # 位操作（12个）
│   ├── matrix.rs                   # 矩阵算法（5个）
│   ├── math.rs                     # 数学算法（10个）
│   ├── greedy.rs                   # 贪心算法（5个）
│   ├── linked_list.rs              # 链表算法（8个）
│   ├── union_find.rs               # 并查集（5个）
│   ├── monotonic_stack.rs          # 单调栈（6个）
│   ├── queue.rs                    # 队列算法（4个）
│   ├── recursion.rs                # 递归算法（5个）
│   ├── sorting.rs                  # 排序算法（6个）
│   ├── design.rs                   # 设计题（6个）
│   ├── breadth_first_search.rs     # BFS（5个）
│   ├── depth_first_search.rs       # DFS（5个）
│   ├── segment_tree.rs             # 线段树（4个）
│   ├── binary_indexed_tree.rs      # 树状数组（3个）
│   └── ordered_map.rs              # 有序映射（3个）
│
├── data_structure/                 # 📦 数据结构模块
│   ├── mod.rs
│   ├── stack.rs                    # 栈
│   ├── priority_queue.rs           # 优先队列
│   ├── lru_cache.rs                # LRU缓存
│   ├── segtree.rs                  # 线段树
│   ├── fenwick.rs                  # 树状数组（Fenwick Tree）
│   ├── sparse_table.rs             # 稀疏表
│   └── dsu.rs                      # 并查集（Disjoint Set Union）
│
├── performance_examples/            # ⚡ 性能优化示例
│   ├── compile_time_optimization.rs    # 编译期优化
│   ├── concurrency_optimization.rs     # 并发优化
│   ├── memory_optimization.rs          # 内存优化
│   └── runtime_profiling.rs            # 运行时性能分析
│
├── performance_examples.rs         # 性能示例模块入口
├── performance_optimization.rs    # 性能优化工具
│
├── backtracking/                   # 🔄 回溯算法（兼容性模块）
│   └── mod.rs
├── divide_and_conquer/             # 🔀 分治算法（兼容性模块）
│   └── mod.rs
├── dynamic_programming/            # 💡 动态规划（兼容性模块）
│   └── mod.rs
├── graph/                          # 🕸️ 图算法（兼容性模块）
│   └── mod.rs
├── greedy/                         # 🎯 贪心算法（兼容性模块）
│   └── mod.rs
├── searching/                      # 🔍 搜索算法（兼容性模块）
│   └── mod.rs
├── sorting/                        # 📊 排序算法（兼容性模块）
│   └── mod.rs
├── string_algorithms/              # 📝 字符串算法（兼容性模块）
│   └── mod.rs
│
├── advanced_algorithms.rs          # 🚀 高级算法集合
├── geometry.rs                     # 📐 几何算法
├── number_theory.rs                # 🔢 数论算法
│
├── machine_learning/               # 🤖 机器学习模块
│   ├── mod.rs
│   ├── neural_network.rs           # 神经网络
│   ├── decision_tree.rs            # 决策树
│   ├── kmeans.rs                   # K-means聚类
│   ├── naive_bayes.rs              # 朴素贝叶斯
│   ├── svm.rs                      # 支持向量机
│   ├── regression.rs               # 回归算法
│   └── clustering.rs               # 聚类算法
│
├── rust_191_features.rs            # Rust 1.91 特性应用
└── rust_192_features.rs            # Rust 1.92.0 特性应用
```
## 📖 模块说明

### 1. lib.rs - 库入口

**作用**: 定义库的公共 API，导出所有公共模块和类型。

**主要导出**:

- `algorithms` - 核心算法模块
- `topics` - 主题化算法模块
- `leetcode` - LeetCode 分类算法
- `data_structure` - 数据结构
- `machine_learning` - 机器学习算法
- 兼容性模块（backtracking, sorting, searching 等）

### 2. algorithms/ - 核心算法模块

**组织方式**: 按算法类型分类，每个类型包含同步/并行/异步/分布式四种实现。

**主要子模块**:

- **sorting/** - 排序算法（快速排序、归并排序、堆排序等）
- **searching/** - 搜索算法（线性搜索、二分搜索等）
- **graph/** - 图算法（BFS、DFS、最短路径、最小生成树等）
- **dynamic_programming/** - 动态规划（LCS、背包问题等）
- **execution_modes/** - 执行模式抽象（同步/并行/异步/分布式）
- **verification/** - 形式化验证（正确性证明、复杂度分析）
- **performance/** - 性能分析工具
- **knowledge_base/** - 算法知识体系

### 3. topics/ - 主题化算法模块

**组织方式**: 提供高级抽象接口，统一不同实现方式的 API。

**特点**:

- 统一的 API 设计
- 自动选择最佳实现方式
- 完整的性能基准测试
- 形式化验证支持

### 4. leetcode/ - LeetCode 分类算法

**组织方式**: 按照 LeetCode 官方标签分类，每个文件对应一个分类。

**统计**:

- 29个模块
- 200+个算法实现
- 346+个测试用例
- 100%测试通过率

**主要分类**:

- Array（数组）
- String（字符串）
- Hash Table（哈希表）
- Dynamic Programming（动态规划）
- Tree（树）
- Graph（图）
- ... 等29个分类

### 5. data_structure/ - 数据结构

**包含的数据结构**:

- Stack（栈）
- Priority Queue（优先队列）
- LRU Cache（LRU缓存）
- Segment Tree（线段树）
- Fenwick Tree（树状数组）
- Sparse Table（稀疏表）
- Disjoint Set Union（并查集）

### 6. machine_learning/ - 机器学习

**包含的算法**:

- Neural Network（神经网络）
- Decision Tree（决策树）
- K-means（K-means聚类）
- Naive Bayes（朴素贝叶斯）
- SVM（支持向量机）
- Regression（回归算法）
- Clustering（聚类算法）

### 7. performance_examples/ - 性能优化示例

**包含的优化技术**:

- 编译期优化
- 并发优化
- 内存优化
- 运行时性能分析

## 🔗 模块关系

```
lib.rs
├── algorithms/          # 核心算法实现
│   ├── execution_modes/ # 执行模式（被其他算法模块使用）
│   ├── verification/     # 验证工具（被其他算法模块使用）
│   └── performance/      # 性能工具（被其他算法模块使用）
├── topics/              # 高级抽象（使用 algorithms/）
├── leetcode/            # LeetCode实现（使用 algorithms/ 和 data_structure/）
├── data_structure/      # 数据结构（被 leetcode/ 使用）
└── machine_learning/    # 机器学习（独立模块）
```
## 📝 代码组织原则

### 1. 分层架构

- **底层**: `algorithms/` - 核心算法实现
- **中层**: `topics/` - 高级抽象接口
- **应用层**: `leetcode/` - 实际应用场景

### 2. 多实现支持

每个算法类型都提供：

- **同步实现** (`sync.rs`) - 单线程执行
- **并行实现** (`parallel.rs`) - 使用 Rayon 多核并行
- **异步实现** (`async_exec.rs`) - 使用 Tokio 异步执行
- **分布式实现** (`distributed.rs`) - 分布式执行（如需要）

### 3. 向后兼容

保留原有模块结构（如 `sorting/`, `searching/` 等）以确保向后兼容。

### 4. 文档完整性

- 每个模块都有详细的文档注释
- 包含算法说明、复杂度分析、使用示例
- 提供形式化验证和证明

## 🚀 使用指南

### 导入模块

```rust
// 使用核心算法模块
use c08_algorithms::algorithms::sorting::*;

// 使用主题化模块（推荐）
use c08_algorithms::topics::sorting::{SortingEngine, SortingAlgorithm};

// 使用 LeetCode 模块
use c08_algorithms::leetcode::array::two_sum;

// 使用数据结构
use c08_algorithms::data_structure::stack::Stack;
```
### 添加新算法

1. 在 `algorithms/` 对应分类下添加实现
2. 在 `topics/` 中添加高级抽象（如需要）
3. 在 `leetcode/` 中添加对应分类的实现（如适用）
4. 添加测试用例
5. 更新文档

## 📚 相关文档

- [主 README](../README.md) - 项目概览
- [示例程序](../examples/README.md) - 使用示例
- [文档索引](../docs/00_master_index.md) - 完整文档导航

## 🔧 开发规范

### 代码风格

- 遵循 Rust 官方编码规范
- 使用 `rustfmt` 格式化代码
- 使用 `clippy` 检查代码质量

### 测试要求

- 每个公共函数都应该有测试用例
- 测试覆盖率应该达到 90%+
- 包含边界情况和错误处理测试

### 文档要求

- 所有公共 API 都应该有文档注释
- 包含算法说明、复杂度分析、使用示例
- 提供形式化验证和证明（如适用）

---

**最后更新**: 2025-12-25
**维护状态**: ✅ 活跃维护
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
