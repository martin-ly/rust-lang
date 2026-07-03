# C08 Algorithms - 示例程序

> **版本**: 0.2.0
> **Rust版本**: 1.96.0+
> **最后更新**: 2025-12-25

## 📋 概述

本目录包含 `c08_algorithms` 库的各种示例程序，展示如何使用不同的算法和数据结构。

## 🚀 运行示例

### 基础运行

```bash
# 运行所有示例
cargo run --example <example_name>

# 运行特定示例
cargo run --example algorithm_comprehensive_demo
```
### 示例列表

| 示例文件                                | 说明             | 主要功能                                   |
| :--- | :--- | :--- || **algorithm_comprehensive_demo.rs**     | 综合算法演示     | 展示排序、搜索、图算法、动态规划的综合使用 |
| **algorithm_comparison_demo.rs**        | 算法对比演示     | 对比不同算法的性能和复杂度                 |
| **algorithm_complexity_demo.rs**        | 复杂度分析演示   | 展示算法复杂度分析和性能测量               |
| **algorithm_optimization_demo.rs**      | 算法优化演示     | 展示算法优化技巧和性能提升                 |
| **backtracking_algorithms_demo.rs**     | 回溯算法演示     | N皇后、全排列、子集等回溯问题              |
| **comprehensive_network_async_demo.rs** | 异步网络算法演示 | 展示异步图算法和网络处理                   |
| **cross_module_integration_demo.rs**    | 跨模块集成演示   | 展示多个模块的协同使用                     |
| **data_structures_demo.rs**             | 数据结构演示     | 展示各种数据结构的用法                     |
| **divide_conquer_demo.rs**              | 分治算法演示     | 最大子段和、最近点对等分治问题             |
| **dynamic_programming_demo.rs**         | 动态规划演示     | LCS、背包问题等动态规划算法                |
| **graph_algorithms_demo.rs**            | 图算法演示       | BFS、DFS、最短路径、最小生成树             |
| **greedy_algorithms_demo.rs**           | 贪心算法演示     | 活动选择、霍夫曼编码等贪心问题             |
| **searching_algorithms_demo.rs**        | 搜索算法演示     | 线性搜索、二分搜索、并行搜索               |
| **sorting_algorithms_demo.rs**          | 排序算法演示     | 快速排序、归并排序、堆排序等               |
| **string_algorithms_demo.rs**           | 字符串算法演示   | KMP、Rabin-Karp、Aho-Corasick              |
| **core_range_demo.rs**                  | `core::range` 模块演示 | `RangeInclusive` 新模块            |
| **collections_mut_ref_demo.rs**         | 集合可变引用插入 | `VecDeque`/`LinkedList` `push_*_mut`       |

## 📖 详细说明

### 1. algorithm_comprehensive_demo.rs ⭐

**综合算法演示** - 最完整的示例，展示库的核心功能。

**运行**:

```bash
cargo run --example algorithm_comprehensive_demo
```
**主要内容**:

- 排序算法（同步/并行/异步）
- 搜索算法（线性/二分/并行）
- 图算法（BFS/DFS/最短路径）
- 动态规划（LCS/背包问题）
- 数据结构（栈/队列/堆）

### 2. algorithm_comparison_demo.rs

**算法对比演示** - 对比不同算法的性能。

**运行**:

```bash
cargo run --example algorithm_comparison_demo
```
**主要内容**:

- 排序算法性能对比
- 搜索算法性能对比
- 复杂度分析

### 3. algorithm_complexity_demo.rs

**复杂度分析演示** - 展示算法复杂度分析方法。

**运行**:

```bash
cargo run --example algorithm_complexity_demo
```
**主要内容**:

- 时间复杂度分析
- 空间复杂度分析
- 性能基准测试

### 4. algorithm_optimization_demo.rs

**算法优化演示** - 展示算法优化技巧。

**运行**:

```bash
cargo run --example algorithm_optimization_demo
```
**主要内容**:

- 编译期优化
- 运行时优化
- 并行化优化

### 5. backtracking_algorithms_demo.rs

**回溯算法演示** - 展示回溯算法的应用。

**运行**:

```bash
cargo run --example backtracking_algorithms_demo
```
**主要内容**:

- N皇后问题
- 全排列生成
- 子集生成

### 6. comprehensive_network_async_demo.rs

**异步网络算法演示** - 展示异步图算法和网络处理。

**运行**:

```bash
cargo run --example comprehensive_network_async_demo
```
**主要内容**:

- 异步图遍历
- 异步最短路径
- 异步网络处理

### 7. cross_module_integration_demo.rs

**跨模块集成演示** - 展示多个模块的协同使用。

**运行**:

```bash
cargo run --example cross_module_integration_demo
```
**主要内容**:

- 模块间数据传递
- 组合使用多个算法
- 复杂场景处理

### 8. data_structures_demo.rs

**数据结构演示** - 展示各种数据结构的用法。

**运行**:

```bash
cargo run --example data_structures_demo
```
**主要内容**:

- 栈和队列
- 堆和优先队列
- 树和图结构

### 9. divide_conquer_demo.rs

**分治算法演示** - 展示分治算法的应用。

**运行**:

```bash
cargo run --example divide_conquer_demo
```
**主要内容**:

- 最大子段和
- 最近点对问题
- 分治排序

### 10. dynamic_programming_demo.rs

**动态规划演示** - 展示动态规划算法的应用。

**运行**:

```bash
cargo run --example dynamic_programming_demo
```
**主要内容**:

- 最长公共子序列（LCS）
- 0-1背包问题
- 斐波那契数列

### 11. graph_algorithms_demo.rs

**图算法演示** - 展示图算法的应用。

**运行**:

```bash
cargo run --example graph_algorithms_demo
```
**主要内容**:

- 广度优先搜索（BFS）
- 深度优先搜索（DFS）
- 最短路径算法
- 最小生成树

### 12. greedy_algorithms_demo.rs

**贪心算法演示** - 展示贪心算法的应用。

**运行**:

```bash
cargo run --example greedy_algorithms_demo
```
**主要内容**:

- 活动选择问题
- 霍夫曼编码
- 最小生成树（Kruskal）

### 13. searching_algorithms_demo.rs

**搜索算法演示** - 展示搜索算法的应用。

**运行**:

```bash
cargo run --example searching_algorithms_demo
```
**主要内容**:

- 线性搜索
- 二分搜索
- 并行搜索

### 14. sorting_algorithms_demo.rs

**排序算法演示** - 展示排序算法的应用。

**运行**:

```bash
cargo run --example sorting_algorithms_demo
```
**主要内容**:

- 快速排序
- 归并排序
- 堆排序
- 并行排序

### 15. string_algorithms_demo.rs

**字符串算法演示** - 展示字符串算法的应用。

**运行**:

```bash
cargo run --example string_algorithms_demo
```
**主要内容**:

- KMP算法
- Rabin-Karp算法
- Aho-Corasick多模式匹配

## 🎯 学习路径

### 初学者路径

1. **data_structures_demo.rs** - 了解基础数据结构
2. **sorting_algorithms_demo.rs** - 学习排序算法
3. **searching_algorithms_demo.rs** - 学习搜索算法
4. **algorithm_comprehensive_demo.rs** - 综合应用

### 进阶路径

1. **graph_algorithms_demo.rs** - 图算法
2. **dynamic_programming_demo.rs** - 动态规划
3. **backtracking_algorithms_demo.rs** - 回溯算法
4. **comprehensive_network_async_demo.rs** - 异步编程

### 高级路径

1. **algorithm_optimization_demo.rs** - 性能优化
2. **algorithm_complexity_demo.rs** - 复杂度分析
3. **cross_module_integration_demo.rs** - 系统集成

## 📚 相关文档

- [主 README](../README.md) - 项目概览
- [文档索引](../docs/00_master_index.md) - 完整文档导航
- [快速入门指南](../docs/tier_02_guides/01_algorithms_quick_start.md) - 学习指南

## 🔧 开发说明

### 添加新示例

1. 在 `examples/` 目录创建新的 `.rs` 文件
2. 在 `Cargo.toml` 中添加示例配置（如需要）
3. 更新本 README 文档

### 示例代码规范

- 使用清晰的注释说明
- 包含错误处理
- 展示最佳实践
- 提供运行说明

## 📝 注意事项

- 所有示例都可以独立运行
- 部分示例需要异步运行时（使用 `tokio`）
- 性能测试示例可能需要较长时间运行
- 建议先阅读相关文档再运行示例

---

**最后更新**: 2025-12-25
**维护状态**: ✅ 活跃维护

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
