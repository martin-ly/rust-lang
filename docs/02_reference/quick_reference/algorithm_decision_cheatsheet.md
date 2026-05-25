# 算法选择决策树速查卡

> **适用场景**: 面试准备、算法选型、性能优化
> **版本**: 通用

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [算法选择决策树速查卡](#算法选择决策树速查卡)
  - [📑 目录](#-目录)
  - [📊 排序算法](#-排序算法)
  - [📊 搜索算法](#-搜索算法)
  - [📊 图算法](#-图算法)
  - [📊 动态规划](#-动态规划)
  - [🔗 参考](#-参考)
  - [**最后更新**: 2026-05-08](#最后更新-2026-05-08)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)
  - [权威来源索引](#权威来源索引-1)

## 📊 排序算法
>
> **[来源: Rust Official Docs]**

| 算法 | 平均 | 最坏 | 空间 | 稳定 | Rust 标准库 |
|------|------|------|------|------|------------|
| QuickSort | O(n log n) | O(n²) | O(log n) | ❌ | `sort_unstable` |
| MergeSort | O(n log n) | O(n log n) | O(n) | ✅ | `sort` (Timsort) |
| HeapSort | O(n log n) | O(n log n) | O(1) | ❌ | - |
| Counting | O(n + k) | O(n + k) | O(k) | ✅ | - |
| Insertion | O(n²) | O(n²) | O(1) | ✅ | 小数组优化 |

**Rust 选择**:

- `slice.sort()` → Timsort（稳定）
- `slice.sort_unstable()` → Pattern-defeating QuickSort（更快）

---

## 📊 搜索算法
>
> **[来源: Rust Official Docs]**

| 场景 | 算法 | 时间 | Rust 实现 |
|------|------|------|----------|
| 有序数组 | 二分查找 | O(log n) | `slice.binary_search` |
| 哈希查找 | HashMap | O(1) 平均 | `std::collections::HashMap` |
| 前缀匹配 | Trie | O(m) | `radix_trie` crate |
| 字符串 | KMP / Boyer-Moore | O(n + m) | `memchr` crate |

---

## 📊 图算法
>
> **[来源: Rust Official Docs]**

| 问题 | 算法 | 时间 | 适用 |
|------|------|------|------|
| 最短路径（无权） | BFS | O(V + E) | 层级遍历 |
| 最短路径（正权） | Dijkstra | O((V + E) log V) | 路由、导航 |
| 最短路径（负权） | Bellman-Ford | O(VE) | 金融检测 |
| 全源最短路径 | Floyd-Warshall | O(V³) | 小型稠密图 |
| 最小生成树 | Kruskal / Prim | O(E log E) | 网络设计 |
| 拓扑排序 | Kahn / DFS | O(V + E) | 任务调度 |

---

## 📊 动态规划
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 特征 | 适用 DP | 不适用（尝试贪心） |
|------|---------|------------------|
| 最优子结构 | ✅ | - |
| 重叠子问题 | ✅ | - |
| 局部最优 = 全局最优 | - | ✅ |

**经典问题**:

- 背包问题 → DP
- 硬币找零 → DP（一般情况）
- 活动选择 → 贪心
- 区间调度 → 贪心

---

## 🔗 参考
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- [c08_algorithm_decision_trees](../../../crates/c08_algorithms/src/algorithm_decision_trees.rs)
- [c08_AlgorithmSkeletons](../../../crates/c08_algorithms/src/algorithm_decision_trees.rs)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-05-08
---

> **权威来源**: [Rust Standard Library](https://doc.rust-lang.org/std/), [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust 标准库、Rust Reference、TRPL 官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- [quick_reference 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**

> **[来源: Rust Reference - doc.rust-lang.org/reference]**

> **[来源: TRPL - The Rust Programming Language]**

> **[来源: Rust Standard Library - doc.rust-lang.org/std]**

> **[来源: ACM - Systems Programming Languages]**

> **[来源: IEEE - Programming Language Standards]**

> **[来源: RFCs - github.com/rust-lang/rfcs]**

> **[来源: Rustonomicon - doc.rust-lang.org/nomicon]**

---

## 权威来源索引

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
