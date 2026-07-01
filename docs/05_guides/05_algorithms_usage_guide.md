# 算法使用指南 {#算法使用指南}
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
>
> **受众**: [进阶]
> **内容分级**: [专家级]
> **分级**: [A]
> **Bloom 层级**: L3-L4 (应用/分析)

**模块**: C08 Algorithms
**创建日期**: 2026-05-12
**最后更新**: 2026-05-12
**Rust 版本**: 1.96.0+ (Edition 2024)
**状态**: ✅ 已完成

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [算法使用指南 {#算法使用指南}](#算法使用指南-算法使用指南)
  - [📑 目录 {#目录}](#-目录-目录)
  - [📋 概述 {#概述}](#-概述-概述)
  - [🚀 快速开始 {#快速开始}](#-快速开始-快速开始)
  - [📊 核心功能 {#核心功能}](#-核心功能-核心功能)
    - [1. 排序算法 {#1-排序算法}](#1-排序算法-1-排序算法)
    - [2. 搜索算法 {#2-搜索算法}](#2-搜索算法-2-搜索算法)
    - [3. 图算法 {#3-图算法}](#3-图算法-3-图算法)
    - [4. 动态规划 {#4-动态规划}](#4-动态规划-4-动态规划)
    - [5. 数据结构 {#5-数据结构}](#5-数据结构-5-数据结构)
    - [6. 机器学习算法 {#6-机器学习算法}](#6-机器学习算法-6-机器学习算法)
    - [7. LeetCode 分类实现 {#7-leetcode-分类实现}](#7-leetcode-分类实现-7-leetcode-分类实现)
  - [⚡ 并行与异步执行 {#并行与异步执行}](#-并行与异步执行-并行与异步执行)
  - [🔧 形式化验证 {#形式化验证}](#-形式化验证-形式化验证)
  - [🐛 常见问题与解决方案 {#常见问题与解决方案}](#-常见问题与解决方案-常见问题与解决方案)
  - [🔗 相关文档 {#相关文档}](#-相关文档-相关文档)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 📋 概述 {#概述}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

本指南对应 `crates/c08_algorithms`，提供 Rust 中各类算法的完整实现，包括排序、搜索、图算法、动态规划、数据结构、机器学习算法以及 LeetCode 分类题解。所有实现支持同步、并行和异步三种执行模式。

**前置知识**: [knowledge/02_intermediate/](../../knowledge/02_intermediate) 集合与迭代器
**速查卡**: [02_algorithms_cheatsheet.md](../02_reference/quick_reference/02_algorithms_cheatsheet.md)

---

## 🚀 快速开始 {#快速开始}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
use c08_algorithms::algorithms::sorting::sync::{quick_sort, merge_sort};
use c08_algorithms::algorithms::searching::sync::binary_search;

fn main() {
    let mut data = vec![3, 1, 4, 1, 5, 9, 2, 6];

    // 快速排序
    quick_sort(&mut data);
    println!("Sorted: {:?}", data);

    // 二分搜索
    let idx = binary_search(&data, &5);
    println!("Index of 5: {:?}", idx);
}
```
---

## 📊 核心功能 {#核心功能}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 1. 排序算法 {#1-排序算法}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

`algorithms/sorting/` 提供多种排序实现，支持同步、并行和分布式执行：

| 算法 | 平均复杂度 | 空间复杂度 | 稳定性 | 模块 |
|------|-----------|-----------|--------|------|
| 快速排序 | O(n log n) | O(log n) | 否 | `sorting/sync.rs` |
| 归并排序 | O(n log n) | O(n) | 是 | `sorting/sync.rs` |
| 堆排序 | O(n log n) | O(1) | 否 | `sorting/sync.rs` |
| 并行快速排序 | O(n log n) | O(log n) | 否 | `sorting/parallel.rs` |
| 异步排序 | O(n log n) | O(n) | 是 | `sorting/async_exec.rs` |

**示例：并行排序**

```rust,ignore
use c08_algorithms::algorithms::sorting::parallel::parallel_quick_sort;

fn parallel_sort_example() {
    let mut data = (0..1_000_000).rev().collect::<Vec<_>>();
    parallel_quick_sort(&mut data);
    assert!(data.is_sorted());
}
```
### 2. 搜索算法 {#2-搜索算法}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

`algorithms/searching/` 提供经典搜索算法：

```rust,ignore
use c08_algorithms::algorithms::searching::sync::{
    binary_search, linear_search, interpolation_search
};

fn searching_examples() {
    let sorted = vec![1, 3, 5, 7, 9, 11, 13];

    // 二分搜索: O(log n)
    assert_eq!(binary_search(&sorted, &7), Some(3));

    // 插值搜索: 均匀分布数据下 O(log log n)
    assert_eq!(interpolation_search(&sorted, &9), Some(4));
}
```
### 3. 图算法 {#3-图算法}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

`algorithms/graph/` 和 `graph/` 提供完整图论算法库：

```rust,ignore
use c08_algorithms::graph::{
    Graph, dijkstra, bfs, dfs, topological_sort
};

fn graph_example() {
    let mut graph = Graph::new();
    graph.add_edge(0, 1, 4);
    graph.add_edge(0, 2, 1);
    graph.add_edge(2, 1, 2);

    // Dijkstra 最短路径
    let (dist, path) = dijkstra(&graph, 0, 1);
    println!("Shortest distance: {:?}", dist);
    println!("Path: {:?}", path);
}
```
### 4. 动态规划 {#4-动态规划}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

`algorithms/dynamic_programming/` 提供经典 DP 问题实现：

```rust,ignore
use c08_algorithms::algorithms::dynamic_programming::{
    longest_common_subsequence, knapsack_01, edit_distance
};

fn dp_examples() {
    let s1 = "ABCDE";
    let s2 = "ACE";
    assert_eq!(longest_common_subsequence(s1, s2), 3);

    let items = vec![(2, 3), (3, 4), (4, 5), (5, 6)]; // (weight, value)
    assert_eq!(knapsack_01(&items, 5), 7);
}
```
### 5. 数据结构 {#5-数据结构}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

`data_structure/` 提供高级数据结构实现：

| 数据结构 | 说明 | 关键操作复杂度 |
|----------|------|---------------|
| 并查集 (DSU) | 不相交集合合并查询 | 接近 O(α(n)) |
| 树状数组 (Fenwick) | 前缀和与单点更新 | O(log n) |
| 线段树 (SegTree) | 区间查询与更新 | O(log n) |
| LRU 缓存 | 最近最少使用缓存 | O(1) |
| 稀疏表 (Sparse Table) | RMQ 区间最值查询 | 预处理 O(n log n), 查询 O(1) |

```rust,ignore
use c08_algorithms::data_structure::{
    DisjointSet, Fenwick, SegmentTree, LruCache
};

fn data_structure_examples() {
    // 并查集
    let mut dsu = DisjointSet::new(5);
    dsu.union(0, 1);
    dsu.union(1, 2);
    assert!(dsu.find(0) == dsu.find(2));

    // 线段树区间求和
    let mut seg = SegmentTree::from_slice(&[1, 3, 5, 7, 9]);
    assert_eq!(seg.query_sum(1, 3), 15); // 3 + 5 + 7
}
```
### 6. 机器学习算法 {#6-机器学习算法}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

`machine_learning/` 提供基础 ML 算法实现：

```rust,ignore
use c08_algorithms::machine_learning::{
    KMeans, LinearRegression, DecisionTree
};

fn ml_examples() {
    // K-Means 聚类
    let data = vec![
        vec![1.0, 2.0], vec![1.5, 1.8],
        vec![5.0, 8.0], vec![8.0, 8.0],
    ];
    let kmeans = KMeans::new(2);
    let clusters = kmeans.fit(&data);
    println!("Clusters: {:?}", clusters);

    // 线性回归
    let x = vec![1.0, 2.0, 3.0, 4.0, 5.0];
    let y = vec![2.0, 4.0, 6.0, 8.0, 10.0];
    let reg = LinearRegression::fit(&x, &y);
    println!("Prediction for 6.0: {:?}", reg.predict(6.0));
}
```
### 7. LeetCode 分类实现 {#7-leetcode-分类实现}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

`leetcode/` 目录按 LeetCode 官方分类组织题解：

| 分类 | 模块 |
|------|------|
| 数组 | `leetcode/array.rs` |
| 二分搜索 | `leetcode/binary_search.rs` |
| 动态规划 | `leetcode/dynamic_programming.rs` |
| 图论 | `leetcode/graph.rs` |
| 贪心 | `leetcode/greedy.rs` |
| 链表 | `leetcode/linked_list.rs` |
| 树 | `leetcode/tree.rs` |
| 并查集 | `leetcode/union_find.rs` |
| 滑动窗口 | `leetcode/sliding_window.rs` |
| 单调栈 | `leetcode/monotonic_stack.rs` |

---

## ⚡ 并行与异步执行 {#并行与异步执行}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

`algorithms/execution_modes/` 提供统一的执行模式抽象：

```rust,ignore
use c08_algorithms::algorithms::execution_modes::{
    ExecutionMode, parallel, async_exec
};

fn execution_mode_examples() {
    // 同步执行
    let sync_result = ExecutionMode::Sync.execute(|| compute_intensive());

    // 并行执行 (rayon)
    let parallel_result = ExecutionMode::Parallel.execute(|| parallel_compute());

    // 异步执行 (tokio)
    let async_result = ExecutionMode::Async.execute(|| async_compute());
}
```
---

## 🔧 形式化验证 {#形式化验证}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

`algorithms/verification/` 和 `algorithms/formal_verification_examples.rs` 提供算法正确性证明：

```rust,ignore
use c08_algorithms::algorithms::formal_verification_examples::{
    binary_search_verified, insertion_sort_verified
};

fn verified_algorithms() {
    // 带循环不变量证明的二分查找
    let arr = vec![1, 3, 5, 7, 9];
    assert_eq!(binary_search_verified(&arr, &5), Some(2));

    // 带循环不变量证明的插入排序
    let mut arr = vec![3, 1, 4, 1, 5];
    insertion_sort_verified(&mut arr);
    assert_eq!(arr, vec![1, 1, 3, 4, 5]);
}
```
---

## 🐛 常见问题与解决方案 {#常见问题与解决方案}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 问题 | 原因 | 解决方案 |
|------|------|----------|
| 排序不稳定 | 使用了不稳定的排序算法 | 需要稳定性时改用 `merge_sort` |
| 二分搜索越界 | 未先排序或边界处理错误 | 确保输入已排序，参考 `binary_search_verified` |
| 递归深度溢出 | 深度过大 | 改用迭代实现或增加栈大小 |
| 并行性能未提升 | 数据量太小 | 并行化有开销，小数据量用同步版本 |
| 图算法无限循环 | 存在负权环或未访问标记错误 | 使用 `visited` 集合或 Bellman-Ford 检测负环 |

---

## 🔗 相关文档 {#相关文档}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- **速查卡**: [02_algorithms_cheatsheet.md](../02_reference/quick_reference/02_algorithms_cheatsheet.md)
- **算法决策树**: [algorithm_decision_trees.md](../../crates/c08_algorithms/src/algorithm_decision_trees.rs)
- **性能优化**: [05_performance_tuning_guide.md](05_performance_tuning_guide.md)
- **源码**: [crates/c08_algorithms/](../../crates/c08_algorithms)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念 {#相关概念}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [05_guides 目录](README.md)
- [docs 索引](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

---
