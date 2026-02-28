# 算法与数据结构快速参考卡片

> **快速参考** | [完整文档](../../../crates/c08_algorithms/docs/README.md) | [代码示例](../../../crates/c08_algorithms/examples/)
> **创建日期**: 2026-01-26
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📋 目录 {#-目录}

- [算法与数据结构快速参考卡片](#算法与数据结构快速参考卡片)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [🚀 快速开始 {#-快速开始}](#-快速开始--快速开始)
    - [排序算法](#排序算法)
    - [搜索算法](#搜索算法)
  - [📋 常用算法 {#-常用算法}](#-常用算法--常用算法)
    - [排序算法 {#排序算法-1}](#排序算法-排序算法-1)
    - [搜索算法 {#搜索算法-1}](#搜索算法-搜索算法-1)
    - [图算法](#图算法)
    - [动态规划](#动态规划)
  - [📊 数据结构 {#-数据结构}](#-数据结构--数据结构)
    - [栈和队列](#栈和队列)
    - [树结构](#树结构)
    - [哈希表](#哈希表)
    - [BTreeMap/BTreeSet 与 append（Rust 1.93）](#btreemapbtreeset-与-appendrust-193)
  - [💡 代码示例 {#-代码示例}](#-代码示例--代码示例)
    - [示例 1: 快速排序实现](#示例-1-快速排序实现)
    - [示例 2: 二分搜索实现](#示例-2-二分搜索实现)
    - [示例 3: 动态规划 - 最长公共子序列](#示例-3-动态规划---最长公共子序列)
    - [示例 4: 图的 BFS 和 DFS](#示例-4-图的-bfs-和-dfs)
    - [示例 5: 滑动窗口最大值](#示例-5-滑动窗口最大值)
  - [🎯 使用场景 {#-使用场景}](#-使用场景--使用场景)
    - [场景: 日志分析系统](#场景-日志分析系统)
  - [⚡ 并行算法 {#-并行算法}](#-并行算法--并行算法)
    - [并行排序](#并行排序)
    - [并行搜索](#并行搜索)
  - [🔧 算法选择指南 {#-算法选择指南}](#-算法选择指南--算法选择指南)
    - [排序选择](#排序选择)
    - [搜索选择](#搜索选择)
  - [📈 性能优化技巧 {#-性能优化技巧}](#-性能优化技巧--性能优化技巧)
    - [使用迭代器](#使用迭代器)
    - [避免不必要的分配](#避免不必要的分配)
  - [🐛 常见错误 {#-常见错误}](#-常见错误--常见错误)
    - [越界访问](#越界访问)
    - [整数溢出](#整数溢出)
  - [🚫 反例速查 {#-反例速查}](#-反例速查--反例速查)
    - [反例 1: 对未排序切片 binary\_search](#反例-1-对未排序切片-binary_search)
    - [反例 2: sort 与 sort\_by 混用导致不稳定](#反例-2-sort-与-sort_by-混用导致不稳定)
    - [反例 3: 递归深度过大导致栈溢出](#反例-3-递归深度过大导致栈溢出)
    - [反例 4: 整数溢出](#反例-4-整数溢出)
    - [反例 5: 不当使用递归导致重复计算](#反例-5-不当使用递归导致重复计算)
  - [📚 相关文档 {#-相关文档}](#-相关文档--相关文档)
  - [🧩 相关示例代码 {#-相关示例代码}](#-相关示例代码--相关示例代码)
  - [📚 相关资源 {#-相关资源}](#-相关资源--相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [形式化理论与类型系统](#形式化理论与类型系统)
    - [相关速查卡](#相关速查卡)

---

## 🚀 快速开始 {#-快速开始}

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

## 📋 常用算法 {#-常用算法}

### 排序算法 {#排序算法-1}

| 算法     | 时间复杂度 | 空间复杂度 | 稳定性 | 使用场景   |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 归并排序 | O(n log n) | O(n)       | 稳定   | 需要稳定性 |
| 堆排序   | O(n log n) | O(1)       | 不稳定 | 内存受限   |
| 插入排序 | O(n²)      | O(1)       | 稳定   | 小数据集   |
| 选择排序 | O(n²)      | O(1)       | 不稳定 | 简单场景   |

### 搜索算法 {#搜索算法-1}

| 算法     | 时间复杂度   | 空间复杂度 | 前提条件       |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
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

## 📊 数据结构 {#-数据结构}

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

**Rust 1.93 行为变更**：`BTreeMap::append` 和 `BTreeSet` 相关 append 操作不再更新目标中已存在的 key。
若源与目标有相同 key，保留目标原有条目。需覆盖时使用 `insert` 或 `entry` API。

---

## 💡 代码示例 {#-代码示例}

### 示例 1: 快速排序实现

```rust
fn quicksort<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    let pivot = partition(arr);
    let (left, right) = arr.split_at_mut(pivot);
    quicksort(left);
    quicksort(&mut right[1..]);
}

fn partition<T: Ord>(arr: &mut [T]) -> usize {
    let len = arr.len();
    let pivot_index = len / 2;
    arr.swap(pivot_index, len - 1);

    let mut store_index = 0;
    for i in 0..len - 1 {
        if arr[i] < arr[len - 1] {
            arr.swap(i, store_index);
            store_index += 1;
        }
    }
    arr.swap(store_index, len - 1);
    store_index
}

// 使用
let mut data = vec![64, 34, 25, 12, 22, 11, 90];
quicksort(&mut data);
assert_eq!(data, vec![11, 12, 22, 25, 34, 64, 90]);
```

### 示例 2: 二分搜索实现

```rust
fn binary_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();

    while left < right {
        let mid = left + (right - left) / 2;
        match arr[mid].cmp(target) {
            std::cmp::Ordering::Equal => return Some(mid),
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid,
        }
    }
    None
}

// 使用
let arr = vec![1, 3, 5, 7, 9, 11, 13];
assert_eq!(binary_search(&arr, &7), Some(3));
assert_eq!(binary_search(&arr, &4), None);
```

### 示例 3: 动态规划 - 最长公共子序列

```rust
fn lcs(s1: &str, s2: &str) -> String {
    let chars1: Vec<char> = s1.chars().collect();
    let chars2: Vec<char> = s2.chars().collect();
    let m = chars1.len();
    let n = chars2.len();

    // dp[i][j] 表示 s1[0..i] 和 s2[0..j] 的 LCS 长度
    let mut dp = vec![vec![0; n + 1]; m + 1];

    for i in 1..=m {
        for j in 1..=n {
            if chars1[i - 1] == chars2[j - 1] {
                dp[i][j] = dp[i - 1][j - 1] + 1;
            } else {
                dp[i][j] = dp[i - 1][j].max(dp[i][j - 1]);
            }
        }
    }

    // 回溯构建结果
    let mut result = String::new();
    let (mut i, mut j) = (m, n);
    while i > 0 && j > 0 {
        if chars1[i - 1] == chars2[j - 1] {
            result.push(chars1[i - 1]);
            i -= 1;
            j -= 1;
        } else if dp[i - 1][j] > dp[i][j - 1] {
            i -= 1;
        } else {
            j -= 1;
        }
    }
    result.chars().rev().collect()
}

// 使用
assert_eq!(lcs("ABCDGH", "AEDFHR"), "ADH");
```

### 示例 4: 图的 BFS 和 DFS

```rust
use std::collections::{HashMap, HashSet, VecDeque};

struct Graph {
    adj: HashMap<i32, Vec<i32>>,
}

impl Graph {
    fn new() -> Self {
        Self { adj: HashMap::new() }
    }

    fn add_edge(&mut self, u: i32, v: i32) {
        self.adj.entry(u).or_insert_with(Vec::new).push(v);
    }

    fn bfs(&self, start: i32) -> Vec<i32> {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        let mut result = vec![];

        queue.push_back(start);
        visited.insert(start);

        while let Some(node) = queue.pop_front() {
            result.push(node);
            if let Some(neighbors) = self.adj.get(&node) {
                for &neighbor in neighbors {
                    if visited.insert(neighbor) {
                        queue.push_back(neighbor);
                    }
                }
            }
        }
        result
    }

    fn dfs(&self, start: i32) -> Vec<i32> {
        let mut visited = HashSet::new();
        let mut result = vec![];
        self.dfs_helper(start, &mut visited, &mut result);
        result
    }

    fn dfs_helper(&self, node: i32, visited: &mut HashSet<i32>, result: &mut Vec<i32>) {
        visited.insert(node);
        result.push(node);
        if let Some(neighbors) = self.adj.get(&node) {
            for &neighbor in neighbors {
                if !visited.contains(&neighbor) {
                    self.dfs_helper(neighbor, visited, result);
                }
            }
        }
    }
}

// 使用
let mut g = Graph::new();
g.add_edge(0, 1);
g.add_edge(0, 2);
g.add_edge(1, 2);
println!("BFS: {:?}", g.bfs(0));
println!("DFS: {:?}", g.dfs(0));
```

### 示例 5: 滑动窗口最大值

```rust
use std::collections::VecDeque;

fn max_sliding_window(nums: &[i32], k: usize) -> Vec<i32> {
    let mut result = vec![];
    let mut deque: VecDeque<usize> = VecDeque::new();

    for i in 0..nums.len() {
        // 移除窗口外的元素
        while let Some(&front) = deque.front() {
            if front + k <= i {
                deque.pop_front();
            } else {
                break;
            }
        }

        // 移除较小的元素
        while let Some(&back) = deque.back() {
            if nums[back] < nums[i] {
                deque.pop_back();
            } else {
                break;
            }
        }

        deque.push_back(i);

        // 记录窗口最大值
        if i >= k - 1 {
            result.push(nums[deque.front().unwrap()]);
        }
    }

    result
}

// 使用
let nums = vec![1, 3, -1, -3, 5, 3, 6, 7];
assert_eq!(max_sliding_window(&nums, 3), vec![3, 3, 5, 5, 6, 7]);
```

---

## 🎯 使用场景 {#-使用场景}

### 场景: 日志分析系统

在实际项目中，算法常用于数据处理和分析。以下是一个简化的日志分析系统：

```rust
use std::collections::HashMap;

struct LogAnalyzer;

impl LogAnalyzer {
    // 统计 IP 出现频率（哈希表）
    fn ip_frequency(logs: &[&str]) -> HashMap<&str, usize> {
        let mut freq = HashMap::new();
        for log in logs {
            let ip = log.split_whitespace().next().unwrap_or("");
            *freq.entry(ip).or_insert(0) += 1;
        }
        freq
    }

    // 查找最频繁的 IP（堆/优先级队列）
    fn top_k_ips(logs: &[&str], k: usize) -> Vec<(&str, usize)> {
        let freq = Self::ip_frequency(logs);
        let mut pairs: Vec<_> = freq.into_iter().collect();

        // 按频率排序（快速选择可用于 O(n) 复杂度）
        pairs.sort_by(|a, b| b.1.cmp(&a.1));
        pairs.into_iter().take(k).collect()
    }

    // 检测异常访问模式（滑动窗口）
    fn detect_burst(logs: &[(u64, &str)], window_secs: u64, threshold: usize) -> Vec<(u64, usize)> {
        let mut result = vec![];
        let mut window = std::collections::VecDeque::new();

        for &(timestamp, _) in logs {
            window.push_back(timestamp);

            // 移除窗口外的记录
            while let Some(&front) = window.front() {
                if front + window_secs < timestamp {
                    window.pop_front();
                } else {
                    break;
                }
            }

            if window.len() >= threshold {
                result.push((timestamp, window.len()));
            }
        }
        result
    }
}
```

---

## ⚡ 并行算法 {#-并行算法}

### 并行排序

```rust
use rayon::prelude::*;

let mut data = vec![64, 34, 25, 12, 22, 11, 90];

// 使用 rayon 进行并行排序
data.par_sort();
println!("Sorted: {:?}", data);
```

### 并行搜索

```rust
use rayon::prelude::*;

let data = vec![1, 3, 5, 7, 9, 11, 13, 15];

// 并行查找
let found = data.par_iter().find_any(|&&x| x == 7);
if let Some(&value) = found {
    println!("Found: {}", value);
}
```

---

## 🔧 算法选择指南 {#-算法选择指南}

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

## 📈 性能优化技巧 {#-性能优化技巧}

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

## 🐛 常见错误 {#-常见错误}

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

## 🚫 反例速查 {#-反例速查}

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

### 反例 3: 递归深度过大导致栈溢出

**错误示例**:

```rust
fn factorial(n: u64) -> u64 {
    if n == 0 { 1 } else { n * factorial(n - 1) }  // ❌ 大数会栈溢出
}

factorial(100_000);  // thread 'main' has overflowed its stack
```

**原因**: 递归调用会消耗栈空间，深度过大时溢出。

**修正**: 使用迭代或尾递归优化：

```rust
fn factorial(n: u64) -> u64 {
    let mut result = 1;
    for i in 1..=n {
        result = result.checked_mul(i).expect("overflow");
    }
    result
}
```

---

### 反例 4: 整数溢出

**错误示例**:

```rust
let a: i32 = 2_000_000_000;
let b: i32 = 2_000_000_000;
let sum = a + b;  // ❌ 溢出：结果为 -294967296
```

**原因**: Rust 中整数溢出在 release 模式下是未定义行为（debug 模式会 panic）。

**修正**: 使用检查溢出方法：

```rust
let sum = a.checked_add(b).expect("overflow");
// 或使用 wrapping_add、saturating_add
```

---

### 反例 5: 不当使用递归导致重复计算

**错误示例**:

```rust
fn fib(n: u32) -> u32 {
    if n <= 1 { n } else { fib(n - 1) + fib(n - 2) }  // ❌ 指数级复杂度
}

fib(50);  // 极慢！
```

**原因**: 朴素递归存在大量重复计算。

**修正**: 使用记忆化或迭代：

```rust
fn fib(n: usize) -> usize {
    let mut dp = vec![0; n + 1];
    dp[1] = 1;
    for i in 2..=n {
        dp[i] = dp[i - 1] + dp[i - 2];
    }
    dp[n]
}
```

---

## 📚 相关文档 {#-相关文档}

- [完整文档](../../../crates/c08_algorithms/README.md)

## 🧩 相关示例代码 {#-相关示例代码}

这些示例都在 `crates/c08_algorithms/examples/` 下，可直接运行（例如：`cargo run -p c08_algorithms --example sorting_algorithms_demo`）。

- [排序算法演示](../../../crates/c08_algorithms/examples/sorting_algorithms_demo.rs)
- [搜索算法演示](../../../crates/c08_algorithms/examples/searching_algorithms_demo.rs)
- [图算法演示](../../../crates/c08_algorithms/examples/graph_algorithms_demo.rs)
- [动态规划演示](../../../crates/c08_algorithms/examples/dynamic_programming_demo.rs)
- [算法复杂度演示](../../../crates/c08_algorithms/examples/algorithm_complexity_demo.rs)
- [算法优化演示](../../../crates/c08_algorithms/examples/algorithm_optimization_demo.rs)

## 📚 相关资源 {#-相关资源}

### 官方文档

- [Rust 算法文档](https://doc.rust-lang.org/std/collections/)
- [Iterator 文档](https://doc.rust-lang.org/std/iter/trait.Iterator.html)

### 项目内部文档

- [算法指南](../../../crates/c08_algorithms/docs/tier_02_guides/01_算法快速入门.md)
- [数据结构指南](../../../crates/c08_algorithms/docs/tier_02_guides/02_数据结构实践.md)
- [性能优化](../../../crates/c08_algorithms/docs/tier_02_guides/04_性能优化实践.md)

### 形式化理论与类型系统

- [类型系统基础](../../research_notes/type_theory/type_system_foundations.md) — 算法与类型的关系
- [构造能力理论](../../research_notes/type_theory/construction_capability.md) — 算法表达能力边界
- [执行模型边界分析](../../research_notes/software_design_theory/03_execution_models/06_boundary_analysis.md) — 算法复杂度与执行模型
- [工作流安全完整模型](../../research_notes/software_design_theory/02_workflow_safe_complete_models/) — 算法正确性验证

### 相关速查卡

- [集合与迭代器速查卡](./collections_iterators_cheatsheet.md) - 数据结构基础
- [控制流与函数速查卡](./control_flow_functions_cheatsheet.md) - 算法控制流
- [类型系统速查卡](./type_system.md) - 算法中的类型

---

**最后更新**: 2026-01-27
**Rust 版本**: 1.93.1+ (Edition 2024)
**提示**: 使用 `cargo doc --open` 查看完整 API 文档
