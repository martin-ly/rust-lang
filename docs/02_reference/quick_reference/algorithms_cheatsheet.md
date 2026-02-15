# 算法与数据结构快速参考卡片

**模块**: C08 Algorithms
**Rust 版本**: 1.93.0+
**最后更新**: 2026-01-26

---

## 📋 目录

- [算法与数据结构快速参考卡片](#算法与数据结构快速参考卡片)
  - [📋 目录](#-目录)
  - [🚀 快速开始](#-快速开始)
    - [排序算法](#排序算法)
    - [搜索算法](#搜索算法)
  - [📋 常用算法](#-常用算法)
    - [排序算法](#排序算法-1)
    - [搜索算法](#搜索算法-1)
    - [图算法](#图算法)
    - [动态规划](#动态规划)
  - [📊 数据结构](#-数据结构)
    - [栈和队列](#栈和队列)
    - [树结构](#树结构)
    - [哈希表](#哈希表)
    - [BTreeMap/BTreeSet 与 append（Rust 1.93）](#btreemapbtreeset-与-appendrust-193)
  - [⚡ 并行算法](#-并行算法)
    - [并行排序](#并行排序)
    - [并行搜索](#并行搜索)
  - [🔧 算法选择指南](#-算法选择指南)
    - [排序选择](#排序选择)
    - [搜索选择](#搜索选择)
  - [📈 性能优化技巧](#-性能优化技巧)
    - [使用迭代器](#使用迭代器)
    - [避免不必要的分配](#避免不必要的分配)
  - [🐛 常见错误](#-常见错误)
    - [越界访问](#越界访问)
    - [整数溢出](#整数溢出)
  - [🚫 反例速查](#-反例速查)
    - [反例 1: 对未排序切片 binary\_search](#反例-1-对未排序切片-binary_search)
    - [反例 2: sort 与 sort\_by 混用导致不稳定](#反例-2-sort-与-sort_by-混用导致不稳定)
  - [📚 相关文档](#-相关文档)
  - [🧩 相关示例代码](#-相关示例代码)
  - [📚 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [相关速查卡](#相关速查卡)

---

## 🚀 快速开始

### 排序算法

```rust
use c08_algorithms::algorithms::sorting::*;

let mut data = vec![64, 34, 25, 12, 22, 11, 90];

// 快速排序
quicksort(&mut data);
println!("Sorted: {:?}", data);

// 归并排序
let sorted = mergesort(&data);
println!("Sorted: {:?}", sorted);

// 堆排序
heapsort(&mut data);
println!("Sorted: {:?}", data);
```

### 搜索算法

```rust
use c08_algorithms::algorithms::searching::*;

let data = vec![1, 3, 5, 7, 9, 11, 13, 15];

// 二分搜索
if let Some(index) = binary_search(&data, 7) {
    println!("Found at index: {}", index);
}

// 线性搜索
if let Some(index) = linear_search(&data, 7) {
    println!("Found at index: {}", index);
}
```

---

## 📋 常用算法

### 排序算法

| 算法     | 时间复杂度 | 空间复杂度 | 稳定性 | 使用场景   |
| -------- | ---------- | ---------- | ------ | ---------- |
| 快速排序 | O(n log n) | O(log n)   | 不稳定 | 通用排序   |
| 归并排序 | O(n log n) | O(n)       | 稳定   | 需要稳定性 |
| 堆排序   | O(n log n) | O(1)       | 不稳定 | 内存受限   |
| 插入排序 | O(n²)      | O(1)       | 稳定   | 小数据集   |
| 选择排序 | O(n²)      | O(1)       | 不稳定 | 简单场景   |

### 搜索算法

| 算法     | 时间复杂度   | 空间复杂度 | 前提条件       |
| -------- | ------------ | ---------- | -------------- |
| 二分搜索 | O(log n)     | O(1)       | 已排序         |
| 线性搜索 | O(n)         | O(1)       | 无             |
| 插值搜索 | O(log log n) | O(1)       | 均匀分布已排序 |

### 图算法

```rust
use c08_algorithms::algorithms::graph::*;

// BFS (广度优先搜索)
let graph = Graph::new(vertices, edges);
let path = bfs(&graph, start, end)?;

// DFS (深度优先搜索)
let path = dfs(&graph, start, end)?;

// 最短路径 (Dijkstra)
let distances = dijkstra(&graph, start)?;
```

### 动态规划

```rust
use c08_algorithms::algorithms::dynamic_programming::*;

// 斐波那契数列
let fib_n = fibonacci(10);

// 最长公共子序列
let lcs = longest_common_subsequence("ABCDGH", "AEDFHR");

// 0-1 背包问题
let max_value = knapsack_01(weights, values, capacity);
```

---

## 📊 数据结构

### 栈和队列

```rust
use c08_algorithms::data_structures::*;

// 栈
let mut stack = Stack::new();
stack.push(1);
stack.push(2);
if let Some(value) = stack.pop() {
    println!("Popped: {}", value);
}

// 队列
let mut queue = Queue::new();
queue.enqueue(1);
queue.enqueue(2);
if let Some(value) = queue.dequeue() {
    println!("Dequeued: {}", value);
}
```

### 树结构

```rust
use c08_algorithms::data_structures::tree::*;

// 二叉搜索树
let mut bst = BinarySearchTree::new();
bst.insert(5);
bst.insert(3);
bst.insert(7);

if let Some(value) = bst.search(3) {
    println!("Found: {}", value);
}

// 遍历
let inorder = bst.inorder_traversal();
println!("Inorder: {:?}", inorder);
```

### 哈希表

```rust
use std::collections::HashMap;

let mut map = HashMap::new();
map.insert("key1", "value1");
map.insert("key2", "value2");

if let Some(value) = map.get("key1") {
    println!("Value: {}", value);
}
```

### BTreeMap/BTreeSet 与 append（Rust 1.93）

**Rust 1.93 行为变更**：`BTreeMap::append` 和 `BTreeSet` 相关 append 操作不再更新目标中已存在的 key。若源与目标有相同 key，保留目标原有条目。需覆盖时使用 `insert` 或 `entry` API。

---

## ⚡ 并行算法

### 并行排序

```rust
use c08_algorithms::algorithms::execution_modes::parallel::*;

let mut data = vec![64, 34, 25, 12, 22, 11, 90];

// 并行快速排序
parallel_quicksort(&mut data);
println!("Sorted: {:?}", data);
```

### 并行搜索

```rust
use c08_algorithms::algorithms::execution_modes::parallel::*;

let data = vec![1, 3, 5, 7, 9, 11, 13, 15];

// 并行线性搜索
if let Some(index) = parallel_linear_search(&data, 7) {
    println!("Found at index: {}", index);
}
```

---

## 🔧 算法选择指南

### 排序选择

- **小数据集 (< 50)**: 插入排序
- **中等数据集 (50-1000)**: 快速排序
- **大数据集 (> 1000)**: 归并排序或堆排序
- **需要稳定性**: 归并排序
- **内存受限**: 堆排序

### 搜索选择

- **已排序数组**: 二分搜索
- **未排序数组**: 线性搜索
- **均匀分布已排序**: 插值搜索
- **频繁搜索**: 使用哈希表

---

## 📈 性能优化技巧

### 使用迭代器

```rust
// 高效的数据处理
let sum: i32 = data.iter()
    .filter(|&x| x > 0)
    .map(|x| x * 2)
    .sum();
```

### 避免不必要的分配

```rust
// 使用切片而非 Vec
fn process_slice(slice: &[i32]) {
    // 处理逻辑
}

// 复用缓冲区
let mut buffer = Vec::with_capacity(1024);
// 复用 buffer
```

---

## 🐛 常见错误

### 越界访问

```rust
// ❌ 错误
let value = data[index];  // 可能 panic

// ✅ 正确
if let Some(value) = data.get(index) {
    // 安全访问
}
```

### 整数溢出

```rust
// ❌ 错误
let result = a + b;  // 可能溢出

// ✅ 正确
let result = a.checked_add(b)?;
```

---

## 🚫 反例速查

### 反例 1: 对未排序切片 binary_search

**错误示例**:

```rust
let v = vec![3, 1, 2];
let _ = v.binary_search(&2);  // ❌ 结果未定义：未排序
```

**原因**: `binary_search` 要求切片已排序。

**修正**:

```rust
let mut v = vec![3, 1, 2];
v.sort();
let _ = v.binary_search(&2);
```

---

### 反例 2: sort 与 sort_by 混用导致不稳定

**错误示例**:

```rust
// 需稳定排序时
v.sort_by(|a, b| a.0.cmp(&b.0));
v.sort_by(|a, b| a.1.cmp(&b.1));  // 可能破坏第一键顺序
```

**原因**: 多次排序时需用 `sort_by_key` 组合键，或 `sort_by` 一次性比较。

**修正**: 使用 `sort_by_key(|x| (x.0, x.1))` 或单次 `sort_by` 组合比较。

---

## 📚 相关文档

- [完整文档](../../../crates/c08_algorithms/README.md)

## 🧩 相关示例代码

这些示例都在 `crates/c08_algorithms/examples/` 下，可直接运行（例如：`cargo run -p c08_algorithms --example sorting_algorithms_demo`）。

- [排序算法演示](../../../crates/c08_algorithms/examples/sorting_algorithms_demo.rs)
- [搜索算法演示](../../../crates/c08_algorithms/examples/searching_algorithms_demo.rs)
- [图算法演示](../../../crates/c08_algorithms/examples/graph_algorithms_demo.rs)
- [动态规划演示](../../../crates/c08_algorithms/examples/dynamic_programming_demo.rs)
- [算法复杂度演示](../../../crates/c08_algorithms/examples/algorithm_complexity_demo.rs)
- [算法优化演示](../../../crates/c08_algorithms/examples/algorithm_optimization_demo.rs)

## 📚 相关资源

### 官方文档

- [Rust 算法文档](https://doc.rust-lang.org/std/collections/)
- [Iterator 文档](https://doc.rust-lang.org/std/iter/trait.Iterator.html)

### 项目内部文档

- [算法指南](../../../crates/c08_algorithms/docs/tier_02_guides/01_算法快速入门.md)
- [数据结构指南](../../../crates/c08_algorithms/docs/tier_02_guides/02_数据结构实践.md)
- [性能优化](../../../crates/c08_algorithms/docs/tier_02_guides/04_性能优化实践.md)

### 相关速查卡

- [集合与迭代器速查卡](./collections_iterators_cheatsheet.md) - 数据结构基础
- [控制流与函数速查卡](./control_flow_functions_cheatsheet.md) - 算法控制流
- [类型系统速查卡](./type_system.md) - 算法中的类型

---

**最后更新**: 2026-01-27
**Rust 版本**: 1.93.0+ (Edition 2024)
**提示**: 使用 `cargo doc --open` 查看完整 API 文档
