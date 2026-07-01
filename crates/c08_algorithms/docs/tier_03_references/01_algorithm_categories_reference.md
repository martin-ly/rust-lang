# 算法分类参考手册

> **文档类型**: Tier 3 技术参考
> **目标读者**: 需要查阅算法分类和API的开发者
> **Rust 版本**: 1.93.1+
> **Edition**: 2024
> **最后更新**: 2025-10-23

---

## 📖 目录

- [算法分类参考手册](#算法分类参考手册)
  - [📖 目录](#-目录)
  - [📐 知识结构](#-知识结构)
    - [概念定义](#概念定义)
    - [属性特征](#属性特征)
    - [关系连接](#关系连接)
    - [思维导图](#思维导图)
  - [1. 概述](#1-概述)
  - [2. 按设计范式分类](#2-按设计范式分类)
    - [2.1 分治算法](#21-分治算法)
      - [API 索引](#api-索引)
      - [代码示例](#代码示例)
      - [使用场景](#使用场景)
    - [2.2 动态规划](#22-动态规划)
      - [2.2.1 API 索引](#221-api-索引)
      - [2.2.2 代码示例](#222-代码示例)
      - [2.2.3 使用场景](#223-使用场景)
    - [2.3 贪心算法](#23-贪心算法)
      - [2.3.1 API 索引](#231-api-索引)
      - [2.3.2 代码示例](#232-代码示例)
      - [2.3.4 使用场景](#234-使用场景)
    - [2.4 回溯算法](#24-回溯算法)
      - [2.4.1. API 索引](#241-api-索引)
      - [2.4.2 代码示例](#242-代码示例)
      - [2.4.3 使用场景](#243-使用场景)
  - [3. 按问题域分类](#3-按问题域分类)
    - [3.1 排序算法](#31-排序算法)
      - [3.2 代码示例](#32-代码示例)
    - [3.2 搜索算法](#32-搜索算法)
      - [3.2.1 代码示例](#321-代码示例)
    - [3.3 图论算法](#33-图论算法)
      - [最短路径](#最短路径)
      - [最小生成树](#最小生成树)
      - [拓扑排序与连通性](#拓扑排序与连通性)
      - [网络流](#网络流)
      - [其他](#其他)
      - [代码示例1](#代码示例1)
    - [3.4 字符串算法](#34-字符串算法)
      - [代码示例2](#代码示例2)
    - [3.5 数值算法](#35-数值算法)
      - [代码示例3](#代码示例3)
  - [4. 按执行模型分类](#4-按执行模型分类)
    - [4.1 同步算法](#41-同步算法)
    - [4.2 并行算法](#42-并行算法)
      - [代码示例4](#代码示例4)
    - [4.3 异步算法](#43-异步算法)
      - [代码示例5](#代码示例5)
  - [5. 数据结构分类](#5-数据结构分类)
    - [5.1 代码示例](#51-代码示例)
  - [6. 算法复杂度快速查询](#6-算法复杂度快速查询)
    - [排序算法](#排序算法)
    - [图算法](#图算法)
    - [字符串算法](#字符串算法)
    - [动态规划](#动态规划)
  - [📚 相关文档](#-相关文档)
  - [🎯 使用建议](#-使用建议)
    - [1. 如何选择算法](#1-如何选择算法)
    - [2. 性能优化技巧](#2-性能优化技巧)
    - [3. 常见陷阱](#3-常见陷阱)
  - [**质量评分**: ⭐⭐⭐⭐⭐](#质量评分-)

---

## 📐 知识结构

### 概念定义

**算法分类 (Algorithm Classification)**:

- **定义**: 按照不同维度对算法进行分类和组织的参考体系
- **类型**: 分类体系
- **范畴**: 算法学、知识管理
- **相关概念**: 算法、数据结构、复杂度分析

### 属性特征

**核心属性**:

- **多维度分类**: 设计范式、问题域、执行模型
- **完整性**: 涵盖所有算法类型
- **可查找性**: 便于快速定位算法
- **关联性**: 算法之间的关联关系

### 关系连接

**组合关系**:

- 算法分类 --[contains]--> 多个算法类别
- 知识体系 --[uses]--> 算法分类

**依赖关系**:

- 算法分类 --[depends-on]--> 算法知识
- 算法选择 --[depends-on]--> 算法分类

### 思维导图

```text
算法分类参考
│
├── 按设计范式
│   ├── 分治算法
│   ├── 动态规划
│   ├── 贪心算法
│   └── 回溯算法
├── 按问题域
│   ├── 排序算法
│   ├── 搜索算法
│   ├── 图论算法
│   └── 字符串算法
└── 按执行模型
    ├── 同步算法
    ├── 并行算法
    └── 异步算法
```
---

## 1. 概述

本文档提供了 C08 Algorithms 模块中所有算法的完整分类参考，按照**设计范式**、**问题域**和**执行模型**三个维度进行分类，便于快速查找和选择合适的算法。

---

## 2. 按设计范式分类

### 2.1 分治算法

**核心思想**: 将问题分解为规模更小的子问题，递归求解后合并结果。

#### API 索引

| 算法 | 同步接口  | 并行接口 | 异步接口 | 时间复杂度  |
| :--- | :--- | :--- | :--- | :--- |
| **快速排序** | `sort_sync(&mut data, SortingAlgo::Quick)` | `sort_parallel(&mut data, SortingAlgo::Quick)` | `sort_async(data, SortingAlgo::Quick).await` | O(n log n)  |
| **归并排序** | `sort_sync(&mut data, SortingAlgo::Merge)` | `sort_parallel(&mut data, SortingAlgo::Merge)` | `sort_async(data, SortingAlgo::Merge).await` | O(n log n)  |
| **最大子数组和** | `max_subarray_sum_sync` | `max_subarray_sum_parallel` | `max_subarray_sum_async` | O(n) |
| **最近点对** | `closest_pair_sync` | `closest_pair_parallel` | `closest_pair_async` | O(n log n)  |
| **快速幂**  | `fast_pow_mod`  | -  | `fast_pow_mod_async` | O(log n) |
| **矩阵快速幂** | `Matrix::pow_mod` | - | `matrix_pow_mod_async` | O(d³ log n) |
| **Quickselect (第k小)** | `quickselect_kth(data, k)` 返回 `Option<&T>` | -  | -  | O(n) 平均   |
| **Karatsuba 大数乘法**  | `karatsuba_mul` | - | - | O(n^1.585)  |

#### 代码示例

```rust
use c08_algorithms::divide_and_conquer::*;

// 同步版本：最大子数组和
fn example_max_subarray_sum() {
    let arr = vec![-2, 1, -3, 4, -1, 2, 1, -5, 4];
    let sum = max_subarray_sum_sync(&arr);
    println!("最大子数组和 = {}", sum); // 6
}

// 并行版本：最近点对
fn example_closest_pair() {
    let points = vec![
        Point { x: 0.0, y: 0.0 },
        Point { x: 1.0, y: 1.0 },
        Point { x: 5.0, y: 5.0 },
    ];

    let distance = closest_pair_parallel(points);
    println!("最近点对距离: {:.2}", distance);
}

// 快速幂模运算
fn example_fast_pow() {
    let result = fast_pow_mod(2, 10, 1000); // 2^10 mod 1000
    println!("2^10 mod 1000 = {}", result); // 24
}
```
#### 使用场景

- **快速排序**: 通用排序，平均性能最优
- **归并排序**: 稳定排序，外部排序
- **最大子数组**: 股票买卖、信号处理
- **最近点对**: 计算几何、聚类分析
- **快速幂**: RSA加密、数论计算

---

### 2.2 动态规划

**核心思想**: 将复杂问题分解为重叠子问题，存储子问题的解以避免重复计算。

#### 2.2.1 API 索引

| 算法  | 同步接口 | 并行接口 | 异步接口  | 时间复杂度 |
| :--- | :--- | :--- | :--- | :--- |
| **最长公共子序列 (LCS)** | `lcs_sync` | `lcs_parallel` | `lcs_async` | O(mn)      |
| **0-1背包** | `knapsack_01_sync` | `knapsack_01_parallel` | `knapsack_01_async`   | O(nW)      |
| **最长上升子序列 (LIS)** | `lis_length_sync`              | -                      | `lis_length_async`    | O(n log n) |
| **编辑距离**             | `edit_distance_sync`           | -                      | `edit_distance_async` | O(mn)      |
| **加权区间调度**         | `weighted_interval_scheduling` | -                      | -                     | O(n log n) |
| **矩阵链乘**             | `matrix_chain_order`           | -                      | -                     | O(n³)      |
| **石子合并**             | `stone_merge_min_cost`         | -                      | -                     | O(n³)      |

#### 2.2.2 代码示例

```rust
use c08_algorithms::dynamic_programming::*;

// LCS: 最长公共子序列
fn example_lcs() {
    let s1 = b"ABCDGH";
    let s2 = b"AEDFHR";

    let length = lcs_sync(s1, s2);
    println!("LCS 长度: {}", length); // 3
}

// 0-1 背包问题
fn example_knapsack() {
    let weights = vec![2, 3, 4, 5];
    let values = vec![3, 4, 5, 6];
    let capacity = 8;

    let max_value = knapsack_01_sync(&weights, &values, capacity);
    println!("最大价值: {}", max_value); // 9
}

// 编辑距离 (Levenshtein)
async fn example_edit_distance() {
    let s1 = "kitten".to_string();
    let s2 = "sitting".to_string();

    let distance = edit_distance_async(s1, s2).await.unwrap();
    println!("编辑距离: {}", distance); // 3
}

// 矩阵链乘最优解
fn example_matrix_chain() {
    let dims = vec![10, 20, 30, 40, 30]; // 4个矩阵
    let min_ops = matrix_chain_order(&dims);

    println!("最少乘法次数: {}", min_ops); // 30000
}
```
#### 2.2.3 使用场景

- **LCS**: 文本diff、DNA序列比对
- **0-1背包**: 资源分配、投资决策
- **LIS**: 股票交易、版本控制
- **编辑距离**: 拼写检查、文本相似度
- **矩阵链乘**: 图形学、数据库查询优化

---

### 2.3 贪心算法

**核心思想**: 每步选择当前最优解，无需回溯。

#### 2.3.1 API 索引

| 算法                    | 接口                                    | 时间复杂度     | 适用条件     |
| :--- | :--- | :--- | :--- |
| **作业排序 (最大收益)** | `job_sequencing_max_profit`             | O(n²)          | 截止时间约束 |
| **Dijkstra 最短路**     | `dijkstra_sync/async`                   | O((V+E) log V) | 非负权重     |
| **Prim 最小生成树**     | `mst_prim_sync/parallel/async`          | O((V+E) log V) | 连通图       |
| **Kruskal 最小生成树**  | `mst_kruskal_sync/parallel/async`       | O(E log V)     | 连通图       |
| **Huffman 编码**        | (标准库 `std::collections::BinaryHeap`) | O(n log n)     | 数据压缩     |

#### 2.3.2 代码示例

```rust
use c08_algorithms::greedy::*;

// 作业排序：最大收益
fn example_job_sequencing() {
    let jobs = vec![
        Job { id: 1, deadline: 4, profit: 20 },
        Job { id: 2, deadline: 1, profit: 10 },
        Job { id: 3, deadline: 1, profit: 40 },
        Job { id: 4, deadline: 1, profit: 30 },
    ];

    let (max_profit, schedule) = job_sequencing_max_profit(&jobs);
    println!("最大收益: {}", max_profit); // 60
    println!("调度顺序: {:?}", schedule); // [3, 1]
}

// Dijkstra 最短路径
fn example_dijkstra() {
    let graph = vec![
        vec![(1, 4), (2, 1)],      // 节点0的邻接表
        vec![(2, 2), (3, 5)],      // 节点1
        vec![(3, 1)],              // 节点2
        vec![],                    // 节点3
    ];

    let distances = dijkstra_sync(&graph, 0);
    println!("从节点0到各节点的最短距离: {:?}", distances); // [0, 4, 1, 2]
}
```
#### 2.3.4 使用场景

- **Dijkstra**: GPS导航、网络路由
- **Prim/Kruskal**: 网络设计、电路布线
- **作业排序**: 任务调度、项目管理

---

### 2.4 回溯算法

**核心思想**: 系统化地搜索所有可能的解，通过剪枝提高效率。

#### 2.4.1. API 索引

| 算法          | 同步接口                 | 并行接口                     | 异步接口                  | 时间复杂度 |
| :--- | :--- | :--- | :--- | :--- |
| **N皇后问题** | `nqueens_solutions_sync` | `nqueens_solutions_parallel` | `nqueens_solutions_async` | O(n!)      |
| **N皇后计数** | `nqueens_count_sync`     | `nqueens_count_parallel`     | -                         | O(n!)      |
| **全排列**    | `permutations_sync`      | `permutations_parallel`      | `permutations_async`      | O(n!)      |
| **子集生成**  | `subsets_sync`           | `subsets_parallel`           | `subsets_async`           | O(2^n)     |

#### 2.4.2 代码示例

```rust
use c08_algorithms::backtracking::*;

// N皇后问题：找到所有解
fn example_nqueens() {
    let n = 8;
    let solutions = nqueens_solutions_sync(n);

    println!("8皇后问题共有 {} 个解", solutions.len()); // 92

    // 打印第一个解
    if let Some(first_solution) = solutions.first() {
        println!("第一个解:");
        for (row, &col) in first_solution.iter().enumerate() {
            let mut line = vec!['.'; n];
            line[col] = 'Q';
            println!("{}", line.iter().collect::<String>());
        }
    }
}

// 并行N皇后计数
async fn example_nqueens_parallel() {
    let n = 12;
    let count = nqueens_count_parallel(n).await;
    println!("{}皇后问题共有 {} 个解", n, count); // 14200
}

// 生成所有子集
fn example_subsets() {
    let nums = vec![1, 2, 3];
    let subsets = subsets_sync(&nums);

    println!("集合 {:?} 的所有子集:", nums);
    for subset in subsets {
        println!("{:?}", subset);
    }
    // 输出: [], [1], [2], [1,2], [3], [1,3], [2,3], [1,2,3]
}
```
#### 2.4.3 使用场景

- **N皇后**: 组合优化、约束满足问题
- **全排列**: 旅行商问题、任务分配
- **子集生成**: 背包变种、组合选择

---

## 3. 按问题域分类

### 3.1 排序算法

| 算法         | 接口                                     | 时间复杂度      | 空间复杂度 | 稳定性 |
| :--- | :--- | :--- | :--- | :--- |
| **快速排序** | `sort_sync/parallel(&mut data, SortingAlgo::Quick)`, `sort_async(data, SortingAlgo::Quick).await` | O(n log n) 平均 | O(log n)   | ❌     |
| **归并排序** | `sort_sync/parallel(&mut data, SortingAlgo::Merge)`, `sort_async(data, SortingAlgo::Merge).await` | O(n log n)      | O(n)       | ✅     |
| **堆排序**   | `sort_sync/parallel(&mut data, SortingAlgo::Heap)`, `sort_async(data, SortingAlgo::Heap).await` | O(n log n)      | O(1)       | ❌     |
| **希尔排序** | `sort_sync(&mut data, SortingAlgo::Shell)` | O(n^1.3)        | O(1)       | ❌     |
| **桶排序**   | `bucket_sort_unit_f64(data, bucket_num)` | O(n+k)          | O(n+k)     | ✅     |

#### 3.2 代码示例

```rust
use c08_algorithms::sorting::{sort_sync, sort_parallel, SortingAlgo};

// 同步快速排序
fn example_quicksort() {
    let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
    sort_sync(&mut arr, SortingAlgo::Quick);
    println!("排序结果: {:?}", arr);
}

// 并行归并排序（大数据集）
fn example_merge_sort_parallel() {
    let mut arr: Vec<i32> = (0..1_000_000).rev().collect();

    let start = std::time::Instant::now();
    sort_parallel(&mut arr, SortingAlgo::Merge);
    println!("并行归并排序用时: {:?}", start.elapsed());
}

// 桶排序（浮点数）
fn example_bucket_sort() {
    let arr = vec![0.42, 0.32, 0.33, 0.52, 0.37, 0.47, 0.51];
    let sorted = bucket_sort_unit_f64(arr, 5);
    println!("桶排序结果: {:?}", sorted);
}
```
---

### 3.2 搜索算法

| 算法         | 接口                              | 时间复杂度   | 适用场景           |
| :--- | :--- | :--- | :--- |
| **线性搜索** | `linear_search_sync/async`        | O(n)         | 无序数组           |
| **二分搜索** | `binary_search_sync/async` 返回 `Result<Option<usize>>` | O(log n)     | 有序数组           |
| **指数搜索** | `exponential_search_sync/async`   | O(log n)     | 有序数组，位置未知 |
| **三分搜索** | `ternary_search_max(l, r, f, iters)` / `ternary_search_max_async(l, r, f, iters).await` | O(log n)     | 单峰函数           |
| **插值搜索** | `interpolation_search_sync/async` | O(log log n) | 均匀分布数据       |
| **跳跃搜索** | `jump_search_sync/async`          | O(√n)        | 有序数组，顺序访问 |

#### 3.2.1 代码示例

```rust
use c08_algorithms::searching::*;

// 二分搜索
fn example_binary_search() {
    let arr = vec![1, 3, 5, 7, 9, 11, 13];
    let target = 7;

    match binary_search_sync(&arr, &target).unwrap() {
        Some(index) => println!("找到 {} 在索引 {}", target, index),
        None => println!("未找到 {}", target),
    }
}

// 三分搜索：找到单峰函数的最大值
async fn example_ternary_search() {
    // f(x) = -(x-5)^2 + 25，最大值在 x=5
    let f = |x: f64| -(x - 5.0).powi(2) + 25.0;

    let max_x = ternary_search_max_async(0.0, 10.0, f, 60).await.unwrap();
    println!("最大值点: x = {:.2}", max_x);
}
```
---

### 3.3 图论算法

#### 最短路径

| 算法               | 接口                                    | 时间复杂度     | 适用场景         |
| :--- | :--- | :--- | :--- |
| **Dijkstra**       | `dijkstra_sync/async` 返回 `(HashMap<T, f64>, HashMap<T, T>)` | O((V+E) log V) | 非负权重         |
| **Bellman-Ford**   | `bellman_ford_sync/async`               | O(VE)          | 负权重，检测负环 |
| **Floyd-Warshall** | `floyd_warshall_sync/async`             | O(V³)          | 全源最短路径     |
| **BFS 最短路**     | `bfs_shortest_path_sync/parallel/async` | O(V+E)         | 无权图           |

#### 最小生成树

| 算法        | 接口                              | 时间复杂度     |
| :--- | :--- | :--- |
| **Kruskal** | `mst_kruskal_sync/parallel/async` | O(E log V)     |
| **Prim**    | `mst_prim_sync/parallel/async`    | O((V+E) log V) |

#### 拓扑排序与连通性

| 算法                  | 接口                            | 时间复杂度 |
| :--- | :--- | :--- |
| **拓扑排序**          | `topo_sort_sync/parallel/async` | O(V+E)     |
| **Tarjan 强连通分量** | `tarjan_scc_sync/async`         | O(V+E)     |

#### 网络流

| 算法                    | 接口                          | 时间复杂度 |
| :--- | :--- | :--- |
| **Dinic 最大流**        | `max_flow_dinic_sync/async`   | O(V²E)     |
| **Edmonds-Karp 最大流** | `max_flow_edmonds_karp/async` | O(VE²)     |
| **最小割**              | `min_cut_from_residual`       | O(V²E)     |

#### 其他

| 算法               | 接口                       | 时间复杂度    | 功能           |
| :--- | :--- | :--- | :--- |
| **Hopcroft-Karp**  | `hopcroft_karp_sync/async` | O(E√V)        | 二分图最大匹配 |
| **LCA (二叉提升)** | `LcaBinaryLift::new/lca`   | O(log n) 查询 | 最近公共祖先   |
| **树直径**         | `tree_diameter_undirected` | O(V)          | 无向树最长路径 |

#### 代码示例1

```rust
use c08_algorithms::graph::*;

// Dijkstra 最短路径
fn example_dijkstra() {
    use std::collections::HashMap;
    let mut graph: HashMap<&str, Vec<(&str, f64)>> = HashMap::new();
    graph.insert("A", vec![("B", 1.0), ("C", 4.0)]);
    graph.insert("B", vec![("C", 2.0), ("D", 5.0)]);
    graph.insert("C", vec![("D", 1.0)]);
    graph.insert("D", vec![]);

    let (distances, _prev) = dijkstra_sync(&graph, &"A");
    println!("最短距离: {:?}", distances);
}

// Dinic 最大流
async fn example_max_flow() {
    use std::collections::HashMap;
    let mut graph: HashMap<i32, Vec<(i32, i64)>> = HashMap::new();
    graph.insert(0, vec![(1, 16), (2, 13)]);
    graph.insert(1, vec![(2, 10), (3, 12)]);
    graph.insert(2, vec![(1, 4), (4, 14)]);
    graph.insert(3, vec![(2, 9), (5, 20)]);
    graph.insert(4, vec![(3, 7), (5, 4)]);
    graph.insert(5, vec![]);

    let max_flow = max_flow_dinic_async(graph, 0, 5).await.unwrap();
    println!("最大流: {}", max_flow); // 23
}

// Tarjan 强连通分量
fn example_tarjan_scc() {
    use std::collections::HashMap;
    let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
    graph.insert(0, vec![1]);        // 0 -> 1
    graph.insert(1, vec![2]);        // 1 -> 2
    graph.insert(2, vec![0, 3]);     // 2 -> 0, 3
    graph.insert(3, vec![4]);        // 3 -> 4
    graph.insert(4, vec![3]);        // 4 -> 3

    let sccs = tarjan_scc_sync(&graph);
    println!("强连通分量: {:?}", sccs); // [[3, 4], [0, 1, 2]]
}
```
---

### 3.4 字符串算法

| 算法                     | 接口                                | 时间复杂度  | 功能         |
| :--- | :--- | :--- | :--- |
| **KMP**                  | `kmp_search/async`                  | O(n+m)      | 模式匹配     |
| **Rabin-Karp**           | `rabin_karp_search/async`           | O(n+m)      | 多模式匹配   |
| **Aho-Corasick**         | `build_trie` + `ac_search/async`    | O(n+m+z)    | 多模式匹配   |
| **Z-Algorithm**          | `z_algorithm` / `z_search/async`    | O(n)        | 模式匹配     |
| **Boyer-Moore-Horspool** | `bmh_search/async`                  | O(n/m) 平均 | 实用快速匹配 |
| **Manacher**             | `manacher_longest_palindrome/async` | O(n)        | 最长回文子串 |
| **Suffix Array**         | `suffix_array`                      | O(n log n)  | 后缀数组     |
| **LCP (Kasai)**          | `lcp_kasai`                         | O(n)        | 最长公共前缀 |
| **Suffix Automaton**     | `SuffixAutomaton`                   | O(n)        | 不同子串计数 |

#### 代码示例2

```rust
use c08_algorithms::string_algorithms::*;

// KMP 模式匹配
async fn example_kmp() {
    let text = "ABABDABACDABABCABAB".to_string();
    let pattern = "ABABCABAB".to_string();

    let positions = kmp_search_async(text, pattern).await.unwrap();
    println!("找到模式在位置: {:?}", positions); // [10]
}

// Aho-Corasick 多模式匹配
fn example_aho_corasick() {
    let patterns = vec![b"he".to_vec(), b"she".to_vec(), b"his".to_vec(), b"hers".to_vec()];
    let trie = build_trie(&patterns);

    let text = b"ushers";
    let matches = trie.ac_search(text, &patterns);

    for (pos, pattern_id) in matches {
        println!("在位置 {} 找到模式 {}", pos, pattern_id);
    }
}

// Manacher 最长回文子串
async fn example_manacher() {
    let text = "babad".to_string();
    let (start, length) = manacher_longest_palindrome_async(text).await.unwrap();

    let original = "babad";
    let palindrome = &original[start..start+length];
    println!("最长回文: {}", palindrome); // "bab" 或 "aba"
}

// Suffix Automaton: 不同子串计数
fn example_suffix_automaton() {
    let text = b"abcbc";
    let sa = SuffixAutomaton::from_bytes(text);

    let count = sa.count_distinct_substrings();
    println!("不同子串数量: {}", count); // 12
}
```
---

### 3.5 数值算法

| 算法             | 接口                 | 时间复杂度 | 功能        |
| :--- | :--- | :--- | :--- |
| **快速幂**       | `fast_pow_mod/async` | O(log n)   | 模幂运算    |
| **扩展欧几里得** | `egcd`               | O(log n)   | 求GCD和系数 |
| **模逆**         | `mod_inv`            | O(log n)   | 模逆元      |
| **Miller-Rabin** | `is_prime(n: u64)`   | O(k log n) | 素性测试    |
| **Pollard Rho**  | `pollard_rho(n: u128)` 返回 `u128` | O(n^1/4)   | 大数分解    |

#### 代码示例3

```rust
use c08_algorithms::number_theory::*;

// 扩展欧几里得算法
fn example_egcd() {
    let (gcd, x, y) = egcd(240, 46);
    println!("gcd(240, 46) = {}", gcd); // 2
    println!("240*{} + 46*{} = {}", x, y, gcd); // 240*(-9) + 46*(47) = 2
}

// 模逆元
fn example_mod_inv() {
    let a = 3;
    let m = 11;

    match mod_inv(a, m) {
        Some(inv) => {
            println!("{} * {} ≡ 1 (mod {})", a, inv, m); // 3 * 4 ≡ 1 (mod 11)
        },
        None => println!("{} 在模 {} 下无逆元", a, m),
    }
}

// Miller-Rabin 素性测试
fn example_is_prime() {
    let candidates = vec![2u64, 17, 221, 561, 1_000_000_007];

    for &n in &candidates {
        if is_prime(n) {
            println!("{} 是素数", n);
        } else {
            println!("{} 是合数", n);
        }
    }
}

// Pollard Rho 大数分解
fn example_pollard_rho() {
    let n: u128 = 8051; // = 83 * 97

    let factor = pollard_rho(n);
    if factor != n {
        println!("{} 的一个因子: {}", n, factor); // 83 或 97
        println!("另一个因子: {}", n / factor);
    }
}
```
---

## 4. 按执行模型分类

### 4.1 同步算法

**特点**: 单线程执行，适合 CPU 密集型计算。

**命名约定**: `*_sync`

**使用场景**:

- 数据规模小（< 10,000）
- CPU 密集型计算
- 无并发需求

### 4.2 并行算法

**特点**: 利用多核 CPU，使用 `rayon` 进行数据并行。

**命名约定**: `*_parallel`

**使用场景**:

- 数据规模大（> 100,000）
- 可分解的独立任务
- CPU 密集型计算

#### 代码示例4

```rust
use c08_algorithms::sorting::{sort_sync, sort_parallel, SortingAlgo};

fn compare_sync_vs_parallel() {
    let size = 10_000_000;
    let mut arr1: Vec<i32> = (0..size).rev().collect();
    let mut arr2 = arr1.clone();

    // 同步版本
    let start = std::time::Instant::now();
    sort_sync(&mut arr1, SortingAlgo::Quick);
    let sync_time = start.elapsed();

    // 并行版本
    let start = std::time::Instant::now();
    sort_parallel(&mut arr2, SortingAlgo::Quick);
    let parallel_time = start.elapsed();

    println!("同步耗时: {:?}", sync_time);
    println!("并行耗时: {:?}", parallel_time);
    println!("加速比: {:.2}x", sync_time.as_secs_f64() / parallel_time.as_secs_f64());
}
```
### 4.3 异步算法

**特点**: 使用 Tokio 运行时，适合 I/O 密集型或需要并发的场景。

**命名约定**: `*_async`

**使用场景**:

- I/O 密集型操作
- 需要超时控制
- 异步生态集成

#### 代码示例5

```rust
use c08_algorithms::graph::*;
use tokio::time::{timeout, Duration};

async fn async_with_timeout() {
    let graph = build_large_graph();

    // 带超时的异步计算
    match timeout(Duration::from_secs(5), dijkstra_async(&graph, 0)).await {
        Ok(result) => println!("计算完成: {:?}", result),
        Err(_) => println!("计算超时"),
    }
}
```
---

## 5. 数据结构分类

| 数据结构                      | 接口                                             | 操作复杂度 | 功能               |
| :--- | :--- | :--- | :--- |
| **Fenwick Tree (树状数组)**   | `Fenwick::new/add/sum_prefix/range_sum`          | O(log n)   | 前缀和、区间和     |
| **Segment Tree (线段树)**     | `SegmentTree::from_slice/update_point/query_sum` | O(log n)   | 区间查询、单点更新 |
| **Disjoint Set (并查集)**     | `DisjointSet::new/find/union`                    | O(α(n))    | 连通性查询、合并   |
| **Priority Queue (优先队列)** | `PriorityQueue`                                  | O(log n)   | 堆排序、优先级调度 |
| **Sparse Table (稀疏表)**     | `SparseTable::build/query_idempotent`            | O(1) 查询  | RMQ、LCA           |
| **LRU Cache**                 | `LruCache`                                       | O(1)       | 缓存淘汰           |

### 5.1 代码示例

```rust
use c08_algorithms::data_structure::*;

// Fenwick Tree: 区间和查询
fn example_fenwick() {
    let mut fenwick = Fenwick::new(10);

    fenwick.add(0, 3);
    fenwick.add(1, 2);
    fenwick.add(2, -1);
    fenwick.add(3, 6);

    // sum_prefix 为闭区间 [0, i]
    println!("前缀和 [0, 3]: {}", fenwick.sum_prefix(3)); // 3+2-1+6 = 10
    // range_sum 为闭区间 [l, r]
    println!("区间和 [1, 3]: {}", fenwick.range_sum(1, 3)); // 2-1+6 = 7
}

// Segment Tree: 区间查询
fn example_segment_tree() {
    let arr = vec![1, 3, 5, 7, 9, 11];
    let mut seg_tree = SegmentTree::from_slice(&arr);

    println!("区间和 [1, 3]: {}", seg_tree.query_sum(1, 3)); // 3+5+7 = 15

    seg_tree.update_point(2, 10); // arr[2] = 5 -> 10
    println!("更新后区间和 [1, 3]: {}", seg_tree.query_sum(1, 3)); // 3+10+7 = 20
}

// Disjoint Set: 连通性
fn example_dsu() {
    let mut dsu = DisjointSet::new(5);

    dsu.union(0, 1);
    dsu.union(1, 2);
    dsu.union(3, 4);

    println!("0 和 2 连通: {}", dsu.find(0) == dsu.find(2)); // true
    println!("0 和 3 连通: {}", dsu.find(0) == dsu.find(3)); // false
}

// Sparse Table: RMQ (区间最小值查询)
fn example_sparse_table() {
    let arr = vec![3, 1, 4, 1, 5, 9, 2, 6];
    let st = SparseTable::build(&arr, |a, b| a.min(b));

    // query_idempotent 为半开区间 [l, r)，需传入 op
    println!("区间 [2, 6) 最小值: {}", st.query_idempotent(2, 6, |a, b| a.min(b))); // 1
}
```
---

## 6. 算法复杂度快速查询

### 排序算法

| 算法     | 最好       | 平均       | 最坏       | 空间     | 稳定性 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 快速排序 | O(n log n) | O(n log n) | O(n²)      | O(log n) | ❌     |
| 归并排序 | O(n log n) | O(n log n) | O(n log n) | O(n)     | ✅     |
| 堆排序   | O(n log n) | O(n log n) | O(n log n) | O(1)     | ❌     |
| 桶排序   | O(n+k)     | O(n+k)     | O(n²)      | O(n+k)   | ✅     |

### 图算法

| 算法           | 时间复杂度     | 空间复杂度 |
| :--- | :--- | :--- |
| BFS/DFS        | O(V+E)         | O(V)       |
| Dijkstra       | O((V+E) log V) | O(V)       |
| Bellman-Ford   | O(VE)          | O(V)       |
| Floyd-Warshall | O(V³)          | O(V²)      |
| Kruskal MST    | O(E log V)     | O(V)       |
| Prim MST       | O((V+E) log V) | O(V)       |
| Tarjan SCC     | O(V+E)         | O(V)       |
| Dinic 最大流   | O(V²E)         | O(V+E)     |

### 字符串算法

| 算法         | 时间复杂度 | 空间复杂度 | 预处理     |
| :--- | :--- | :--- | :--- |
| KMP          | O(n+m)     | O(m)       | O(m)       |
| Rabin-Karp   | O(n+m)     | O(1)       | O(m)       |
| Aho-Corasick | O(n+m+z)   | O(m×Σ)     | O(m×Σ)     |
| Manacher     | O(n)       | O(n)       | -          |
| Suffix Array | O(n log n) | O(n)       | O(n log n) |

### 动态规划

| 问题     | 时间复杂度 | 空间复杂度 | 优化空间    |
| :--- | :--- | :--- | :--- |
| LCS      | O(mn)      | O(mn)      | O(min(m,n)) |
| 0-1背包  | O(nW)      | O(nW)      | O(W)        |
| LIS      | O(n log n) | O(n)       | -           |
| 编辑距离 | O(mn)      | O(mn)      | O(min(m,n)) |
| 矩阵链乘 | O(n³)      | O(n²)      | -           |

---

## 📚 相关文档

- **[02\_数据结构参考](02_data_structures_reference.md)** - 数据结构详细API
- **[03_Rust190特性参考](03_rust_190_features_reference.md)** - Rust 1.90+ 特性参考；算法新特性见 [RUST_192_ALGORITHMS_IMPROVEMENTS](../RUST_192_ALGORITHMS_IMPROVEMENTS.md)
- **[04\_算法性能参考](04_algorithm_performance_reference.md)** - 性能基准测试数据
- **[05\_标准库算法参考](05_standard_library_algorithms_reference.md)** - 标准库算法对比

---

## 🎯 使用建议

### 1. 如何选择算法

```rust
// 决策树
fn choose_algorithm(problem: &str, data_size: usize) -> &'static str {
    match problem {
        "排序" => {
            if data_size < 50 {
                "插入排序"
            } else if needs_stability() {
                "归并排序"
            } else {
                "快速排序"
            }
        },
        "搜索" => {
            if is_sorted() {
                "二分搜索"
            } else {
                "线性搜索"
            }
        },
        "最短路径" => {
            if has_negative_weight() {
                "Bellman-Ford"
            } else if single_source() {
                "Dijkstra"
            } else {
                "Floyd-Warshall"
            }
        },
        _ => "查阅文档",
    }
}
```
### 2. 性能优化技巧

```rust
// 技巧1: 小数据集使用同步版本
if data.len() < 10_000 {
    sort_sync(&mut data, SortingAlgo::Quick);
} else {
    sort_parallel(&mut data, SortingAlgo::Quick);
}

// 技巧2: 使用 Rayon 并行迭代器
use rayon::prelude::*;
let results: Vec<_> = data.par_iter()
    .map(|x| expensive_computation(x))
    .collect();

// 技巧3: 预分配空间
let mut result = Vec::with_capacity(expected_size);
```
### 3. 常见陷阱

```rust
// ❌ 错误：重复计算
fn fibonacci_naive(n: u64) -> u64 {
    if n <= 1 { n } else { fibonacci_naive(n-1) + fibonacci_naive(n-2) }
}

// ✅ 正确：动态规划
fn fibonacci_dp(n: usize) -> u64 {
    if n <= 1 { return n as u64; }

    let mut dp = vec![0; n+1];
    dp[1] = 1;

    for i in 2..=n {
        dp[i] = dp[i-1] + dp[i-2];
    }

    dp[n]
}
```
---

**文档维护**: Documentation Team
**创建日期**: 2025-10-23
**质量评分**: ⭐⭐⭐⭐⭐
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
