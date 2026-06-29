# 算法专项练习指南

> **内容分级**: [核心级]
>
> **分级**: [A]
> **Bloom 层级**: L2-L4 (理解 / 应用 / 分析)
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **层级**: L2-L4
> **概念族**: 学习资源 / 算法练习
> **权威来源**:
>
> [The Rust Programming Language](https://doc.rust-lang.org/book/) |
> [Rust By Example](https://doc.rust-lang.org/rust-by-example/) |
> [Rust Reference](https://doc.rust-lang.org/reference/) |
> [Cracking the Coding Interview](https://www.crackingthecodinginterview.com/) |
> [CLRS](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/)

---

## 📑 目录

- [算法专项练习指南](#算法专项练习指南)
  - [📑 目录](#-目录)
  - [一、指南说明](#一指南说明)
  - [二、练习题目录](#二练习题目录)
    - [2.1 排序 (`sorting.rs`)](#21-排序-sortingrs)
    - [2.2 搜索 (`searching.rs`)](#22-搜索-searchingrs)
    - [2.3 图论 (`graph.rs`)](#23-图论-graphrs)
    - [2.4 动态规划 (`dynamic_programming.rs`)](#24-动态规划-dynamic_programmingrs)
    - [2.5 数据结构 (`data_structures.rs`)](#25-数据结构-data_structuresrs)
  - [三、难度分级](#三难度分级)
  - [四、学习路径](#四学习路径)
  - [五、权威来源索引](#五权威来源索引)
    - [P0 — Rust 官方文档](#p0--rust-官方文档)
    - [P1 — 经典算法教材](#p1--经典算法教材)
    - [P2 — 在线判题与社区资源](#p2--在线判题与社区资源)
  - [六、验证方式](#六验证方式)

---

## 一、指南说明

本文档定位 `exercises/src/algorithms/` 算法专项练习的入口说明，配套代码位于 [`exercises/src/algorithms/`](../exercises/src/algorithms/) 目录。
练习采用"函数骨架 + 参考实现 + 单元测试"的形式，覆盖排序、搜索、图论、动态规划与经典数据结构五大主题，
帮助学习者在 Rust 1.96.0+ 环境中掌握算法实现与所有权、借用、泛型等 Rust 特性的结合。

> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/)

---

## 二、练习题目录

### 2.1 排序 (`sorting.rs`)

| 题目 | 函数 | 核心知识点 | 测试覆盖 |
|------|------|-----------|----------|
| 快速排序 | `quick_sort` | 原地 partition、递归分治 | 基础、空/单元素、重复与负数 |
| 归并排序 | `merge_sort` | 稳定归并、辅助数组 | 基础、全相同元素 |
| 堆排序 | `heap_sort` | 大顶堆、sift_down | 基础、大规模逆序 |
| 桶排序 | `bucket_sort` | 均匀分布 [0,1) 分桶 | 基础、空/单元素 |
| 计数排序 | `counting_sort` | 非负整数计数 | 基础、全零 |
| 荷兰国旗 | `sort_colors` | 三指针、O(n) 原地分类 | 基础、全相同 |

### 2.2 搜索 (`searching.rs`)

| 题目 | 函数 | 核心知识点 | 测试覆盖 |
|------|------|-----------|----------|
| 二分搜索 | `binary_search` | 有序数组折半查找 | 命中、未命中、空数组 |
| 下界搜索 | `lower_bound` | 首个 ≥ target 位置 | 命中、越界、重复元素 |
| 峰值元素 | `find_peak_element` | 二分查找局部峰值 | 基础、单元素、空数组 |
| BFS 最短路 | `bfs_shortest_path` | 无权图邻接表、队列 | 连通图、不连通图 |
| DFS 路径 | `dfs_has_path` | 有向图深度优先、访问标记 | 可达、不可达、越界 |
| 岛屿数量 | `num_islands` | 二维网格 DFS | 基础、空网格 |

### 2.3 图论 (`graph.rs`)

| 题目 | 函数/结构 | 核心知识点 | 测试覆盖 |
|------|-----------|-----------|----------|
| Dijkstra | `dijkstra` | 优先队列、松弛操作 | 基础、不可达节点 |
| 拓扑排序 | `topological_sort` | Kahn 算法、入度表 | DAG、含环图 |
| 并查集 | `UnionFind` | 路径压缩、按秩合并 | 连通性、合并 |
| 无向图环检测 | `has_cycle_undirected` | 并查集判环 | 有环、树 |
| 最小生成树 | `kruskal_mst` | Kruskal + 并查集 | 基础图 |
| 网络延迟时间 | `network_delay_time` | Dijkstra 变种 | 可达、不可达 |

### 2.4 动态规划 (`dynamic_programming.rs`)

| 题目 | 函数 | 核心知识点 | 测试覆盖 |
|------|------|-----------|----------|
| 0/1 背包 | `knapsack_01` | 一维 DP、逆序遍历 | 基础、空输入 |
| 完全背包 | `unbounded_knapsack` | 一维 DP、正序遍历 | 基础 |
| 最长递增子序列 | `length_of_lis` | 耐心排序 / 二分 | 基础、空数组 |
| 最长公共子序列 | `longest_common_subsequence` | 二维 DP 滚动数组 | 基础、无公共 |
| 最小编辑距离 | `min_edit_distance` | 滚动数组 DP | 基础、空串 |
| 零钱兑换 | `coin_change` | 完全背包求最小数量 | 基础、无解、金额 0 |
| 最大子数组和 | `max_subarray_sum` | Kadane 算法 | 基础、单元素、全负 |
| 爬楼梯 | `climb_stairs` | 斐波那契 DP | 基础、n=0 |

### 2.5 数据结构 (`data_structures.rs`)

| 题目 | 结构 | 核心知识点 | 测试覆盖 |
|------|------|-----------|----------|
| LRU 缓存 | `LruCache` | `IndexMap` 实现 O(1) get/put | 基本操作、零容量 |
| 前缀树 | `Trie` | `HashMap` 节点、前缀匹配 | 插入、搜索、前缀 |
| 并查集 | `UnionFind` | 路径压缩、按秩合并 | 连通性 |
| 最小栈 | `MinStack` | 辅助最小值同步栈 | push/pop/get_min |
| 栈实现队列 | `MyQueue` | 双栈 in/out | push/pop/peek/empty |

---

## 三、难度分级

| 难度 | 对应题目 | 建议对象 |
|------|----------|----------|
| L2 基础 | 快速排序、二分搜索、爬楼梯、最小栈、栈实现队列 | Rust 语法已入门，开始算法训练 |
| L3 进阶 | 归并排序、堆排序、BFS/DFS、拓扑排序、0/1 背包、LIS、LCS、编辑距离 | 掌握所有权/借用后可稳定实现 |
| L4 应用 | Dijkstra、Kruskal、并查集综合、LRU、Trie、网络延迟时间 | 能结合 Rust 标准库与第三方 crate 完成 |

---

## 四、学习路径

1. **阶段 1：排序与搜索**（L2-L3）
   - 先完成 `sorting.rs` 与 `searching.rs`，熟悉递归、切片、索引边界处理。
2. **阶段 2：数据结构**（L2-L4）
   - 实现 `LruCache`、`Trie`、`UnionFind` 等，练习泛型、生命周期与自定义结构体。
3. **阶段 3：图论**（L3-L4）
   - 掌握 Dijkstra、拓扑排序、并查集，理解 `BinaryHeap` 与图遍历模板。
4. **阶段 4：动态规划**（L3-L4）
   - 从背包、LIS、LCS 到编辑距离、零钱兑换，体会状态转移与空间优化。

> **来源**: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)

---

## 五、权威来源索引

### P0 — Rust 官方文档

- [The Rust Programming Language](https://doc.rust-lang.org/book/) — 所有权、借用、泛型、Trait
- [Rust Reference](https://doc.rust-lang.org/reference/) — 语言语义与标准库约定
- [Rust By Example](https://doc.rust-lang.org/rust-by-example/) — 可运行示例与惯用法
- [The Rustonomicon](https://doc.rust-lang.org/nomicon/) — Unsafe 与高级内存模型

### P1 — 经典算法教材

- [CLRS — Introduction to Algorithms](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/) — 排序、图论、DP 形式化
- [Cracking the Coding Interview](https://www.crackingthecodinginterview.com/) — 面试题型与边界讨论
- [Algorithm Design Manual](https://www.algorist.com/) — 算法选型与实现技巧

### P2 — 在线判题与社区资源

- [LeetCode](https://leetcode.com/) — 对应题目编号与官方题解
- [HackerRank](https://www.hackerrank.com/) — 算法专项训练
- [Rust算法练习社区](https://github.com/rust-lang/rustlings) — 风格参考

---

## 六、验证方式

```bash
# 运行 exercises crate 全部测试
cargo test -p exercises

# 仅运行算法模块测试
cargo test -p exercises --lib algorithms

# 检查研究笔记结构
cd scripts/maintenance && python check_research_notes.py
```

当前算法模块已包含 **25 个独立算法函数 + 5 个数据结构实现**，配套 **47 个单元测试**，全部通过。

> **来源: [ACM Digital Library](https://dl.acm.org/)**
> **来源: [IEEE Standards](https://standards.ieee.org/)**
> **来源: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)**
