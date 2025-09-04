# 算法与数据结构

## 目录

- [算法与数据结构](#算法与数据结构)
  - [目录](#目录)
  - [1. 算法复杂度分析](#1-算法复杂度分析)
    - [1.1 时间复杂度的形式化定义](#11-时间复杂度的形式化定义)
    - [1.2 空间复杂度的理论基础](#12-空间复杂度的理论基础)
    - [1.3 渐进符号与证明](#13-渐进符号与证明)
  - [2. 基本数据结构](#2-基本数据结构)
    - [2.1 线性表（数组、链表）形式化](#21-线性表数组链表形式化)
    - [2.2 栈与队列的理论基础](#22-栈与队列的理论基础)
    - [2.3 树结构的数学表示](#23-树结构的数学表示)
  - [3. 高级算法设计](#3-高级算法设计)
    - [3.1 分治算法的形式化](#31-分治算法的形式化)
    - [3.2 动态规划的理论基础](#32-动态规划的理论基础)
    - [3.3 贪心算法的数学证明](#33-贪心算法的数学证明)
  - [4. 图论算法](#4-图论算法)
    - [4.1 图的基本概念](#41-图的基本概念)
    - [4.2 最短路径算法](#42-最短路径算法)
    - [4.3 最小生成树算法](#43-最小生成树算法)
  - [5. 字符串算法](#5-字符串算法)
    - [5.1 字符串匹配算法](#51-字符串匹配算法)
    - [5.2 字符串压缩算法](#52-字符串压缩算法)
  - [6. 并行算法](#6-并行算法)
    - [6.1 并行计算模型](#61-并行计算模型)
    - [6.2 MapReduce模型](#62-mapreduce模型)
  - [7. 算法优化技术](#7-算法优化技术)
    - [7.1 缓存优化](#71-缓存优化)
    - [7.2 内存优化](#72-内存优化)
  - [总结](#总结)

## 1. 算法复杂度分析

### 1.1 时间复杂度的形式化定义

**理论定义**：

设算法 A 的输入规模为 n，基本操作执行次数为 T(n)。若存在正实数 c 和 n₀，使得对所有 n ≥ n₀，有 T(n) ≤ c·f(n)，则称算法 A 的时间复杂度为 O(f(n))。

**数学符号**：

T(n) = O(f(n)) ⇔ ∃ c>0, n₀>0, ∀ n≥n₀, T(n) ≤ c·f(n)

**Rust 伪代码示例**：

```rust
fn sum(arr: &[i32]) -> i32 {
    let mut s = 0;
    for &x in arr { s += x; } // 循环 n 次
    s
}
// T(n) = O(n)
```

**简要证明**：
对上述 sum 算法，T(n) = a·n + b，取 c=a+1, n₀=1，则 T(n) ≤ c·n，故 T(n)=O(n)。

### 1.2 空间复杂度的理论基础

**理论定义**：
设算法 A 的输入规模为 n，所需内存单元数为 S(n)。若存在正实数 c 和 n₀，使得对所有 n ≥ n₀，有 S(n) ≤ c·g(n)，则称算法 A 的空间复杂度为 O(g(n))。

**数学符号**：
S(n) = O(g(n)) ⇔ ∃ c>0, n₀>0, ∀ n≥n₀, S(n) ≤ c·g(n)

**Rust 伪代码示例**：

```rust
fn count_unique(arr: &[i32]) -> usize {
    use std::collections::HashSet;
    let mut set = HashSet::new();
    for &x in arr { set.insert(x); }
    set.len()
}
// S(n) = O(n)
```

**简要说明**：
如上算法需 O(n) 额外空间存储 HashSet，空间复杂度为 O(n)。

### 1.3 渐进符号与证明

**理论定义**：
渐进符号用于描述算法复杂度的增长趋势，常见有 O（上界）、Ω（下界）、Θ（紧确界）。

**数学符号**：

- O(f(n))：T(n) ≤ c·f(n)
- Ω(f(n))：T(n) ≥ c·f(n)
- Θ(f(n))：c₁·f(n) ≤ T(n) ≤ c₂·f(n)

**Rust 伪代码示例**：

```rust
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let (mut l, mut r) = (0, arr.len());
    while l < r {
        let m = (l + r) / 2;
        if arr[m] == target { return Some(m); }
        if arr[m] < target { l = m + 1; } else { r = m; }
    }
    None
}
// T(n) = O(log n)
```

**简要说明**：
渐进符号便于分析算法在大规模输入下的性能表现。

## 2. 基本数据结构

### 2.1 线性表（数组、链表）形式化

**理论定义**：
线性表是一种有序数据结构，支持按序访问和插入，常见实现有数组和链表。

**结构符号**：
Array = [a₁, a₂, ..., aₙ]
List = Node(value, next)

**Rust 伪代码**：

```rust
let arr = [1, 2, 3, 4]; // 数组
struct ListNode { val: i32, next: Option<Box<ListNode>> }
```

**简要说明**：
数组支持 O(1) 随机访问，链表支持 O(1) 插入删除。

### 2.2 栈与队列的理论基础

**理论定义**：
栈（Stack）是后进先出（LIFO）的数据结构，队列（Queue）是先进先出（FIFO）的数据结构。

**数学符号**：
Stack = { push(x), pop() → x, top() → x }
Queue = { enqueue(x), dequeue() → x, front() → x }

**Rust 伪代码**：

```rust
// 栈实现
struct Stack<T> {
    data: Vec<T>
}
impl<T> Stack<T> {
    fn push(&mut self, item: T) { self.data.push(item); }
    fn pop(&mut self) -> Option<T> { self.data.pop() }
    fn top(&self) -> Option<&T> { self.data.last() }
}

// 队列实现
struct Queue<T> {
    data: Vec<T>
}
impl<T> Queue<T> {
    fn enqueue(&mut self, item: T) { self.data.push(item); }
    fn dequeue(&mut self) -> Option<T> { 
        if self.data.is_empty() { None } else { Some(self.data.remove(0)) }
    }
    fn front(&self) -> Option<&T> { self.data.first() }
}
```

**简要说明**：
栈和队列是基础的数据结构，广泛应用于算法和系统设计中。

### 2.3 树结构的数学表示

**理论定义**：
树是一种层次化的数据结构，由节点和边组成，每个节点最多有一个父节点。

**数学符号**：
Tree = (V, E), 其中 V 是节点集合，E 是边集合，且 |E| = |V| - 1

**Rust 伪代码**：

```rust
struct TreeNode<T> {
    val: T,
    left: Option<Box<TreeNode<T>>>,
    right: Option<Box<TreeNode<T>>>
}

impl<T> TreeNode<T> {
    fn new(val: T) -> Self {
        Self { val, left: None, right: None }
    }
    
    fn insert(&mut self, val: T) {
        // 二叉搜索树插入逻辑
        if val < self.val {
            if let Some(ref mut left) = self.left {
                left.insert(val);
            } else {
                self.left = Some(Box::new(TreeNode::new(val)));
            }
        } else {
            if let Some(ref mut right) = self.right {
                right.insert(val);
            } else {
                self.right = Some(Box::new(TreeNode::new(val)));
            }
        }
    }
}
```

**简要说明**：
树结构支持高效的搜索、插入和删除操作。

## 3. 高级算法设计

### 3.1 分治算法的形式化

**理论定义**：
分治算法将问题分解为更小的子问题，递归解决后合并结果。

**数学符号**：
T(n) = a·T(n/b) + f(n)，其中 a ≥ 1, b > 1

**Rust 伪代码**：

```rust
fn merge_sort<T: Ord + Clone>(arr: &[T]) -> Vec<T> {
    if arr.len() <= 1 { return arr.to_vec(); }
    
    let mid = arr.len() / 2;
    let left = merge_sort(&arr[..mid]);
    let right = merge_sort(&arr[mid..]);
    
    merge(&left, &right)
}

fn merge<T: Ord + Clone>(left: &[T], right: &[T]) -> Vec<T> {
    let mut result = Vec::new();
    let (mut i, mut j) = (0, 0);
    
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            result.push(left[i].clone());
            i += 1;
        } else {
            result.push(right[j].clone());
            j += 1;
        }
    }
    
    result.extend_from_slice(&left[i..]);
    result.extend_from_slice(&right[j..]);
    result
}
```

**复杂度分析**：

- 时间复杂度：O(n log n)
- 空间复杂度：O(n)

### 3.2 动态规划的理论基础

**理论定义**：
动态规划通过将问题分解为重叠子问题，避免重复计算。

**数学符号**：
dp[i] = f(dp[j]) for j < i

**Rust 伪代码**：

```rust
fn fibonacci_dp(n: usize) -> u64 {
    if n <= 1 { return n as u64; }
    
    let mut dp = vec![0; n + 1];
    dp[0] = 0;
    dp[1] = 1;
    
    for i in 2..=n {
        dp[i] = dp[i-1] + dp[i-2];
    }
    
    dp[n]
}

fn longest_increasing_subsequence(arr: &[i32]) -> usize {
    let n = arr.len();
    let mut dp = vec![1; n];
    
    for i in 1..n {
        for j in 0..i {
            if arr[i] > arr[j] {
                dp[i] = dp[i].max(dp[j] + 1);
            }
        }
    }
    
    dp.into_iter().max().unwrap_or(0)
}
```

**简要说明**：
动态规划适用于具有最优子结构的问题。

### 3.3 贪心算法的数学证明

**理论定义**：
贪心算法在每一步选择当前最优解，期望得到全局最优解。

**数学符号**：
对于问题 P，贪心选择 g(x) 满足：g(x) ∈ argmax{f(y) | y ∈ feasible(x)}

**Rust 伪代码**：

```rust
fn activity_selection(start: &[i32], finish: &[i32]) -> Vec<usize> {
    let n = start.len();
    let mut activities: Vec<(usize, i32, i32)> = (0..n)
        .map(|i| (i, start[i], finish[i]))
        .collect();
    
    // 按结束时间排序
    activities.sort_by_key(|&(_, _, f)| f);
    
    let mut result = vec![];
    let mut last_finish = 0;
    
    for (i, s, f) in activities {
        if s >= last_finish {
            result.push(i);
            last_finish = f;
        }
    }
    
    result
}

fn huffman_encoding(frequencies: &[u32]) -> Vec<String> {
    use std::collections::BinaryHeap;
    use std::cmp::Reverse;
    
    let mut heap: BinaryHeap<Reverse<(u32, usize)>> = frequencies
        .iter()
        .enumerate()
        .map(|(i, &freq)| Reverse((freq, i)))
        .collect();
    
    let mut codes = vec![String::new(); frequencies.len()];
    
    while heap.len() > 1 {
        let Reverse((freq1, idx1)) = heap.pop().unwrap();
        let Reverse((freq2, idx2)) = heap.pop().unwrap();
        
        // 构建新节点
        let new_freq = freq1 + freq2;
        let new_idx = frequencies.len() + heap.len();
        
        // 更新编码
        for &idx in &[idx1, idx2] {
            if idx < frequencies.len() {
                codes[idx].push(if idx == idx1 { '0' } else { '1' });
            }
        }
        
        heap.push(Reverse((new_freq, new_idx)));
    }
    
    codes.into_iter().map(|s| s.chars().rev().collect()).collect()
}
```

**简要说明**：
贪心算法适用于具有贪心选择性质的问题。

## 4. 图论算法

### 4.1 图的基本概念

**理论定义**：
图 G = (V, E) 由顶点集 V 和边集 E 组成，边表示顶点间的关系。

**数学符号**：
G = (V, E), E ⊆ V × V

**Rust 伪代码**：

```rust
use std::collections::HashMap;

struct Graph {
    adjacency_list: HashMap<usize, Vec<usize>>
}

impl Graph {
    fn new() -> Self {
        Self { adjacency_list: HashMap::new() }
    }
    
    fn add_edge(&mut self, from: usize, to: usize) {
        self.adjacency_list.entry(from).or_insert_with(Vec::new).push(to);
    }
    
    fn neighbors(&self, vertex: usize) -> &[usize] {
        self.adjacency_list.get(&vertex).map_or(&[], |v| v.as_slice())
    }
}
```

### 4.2 最短路径算法

**理论定义**：
最短路径算法用于找到图中两个顶点间的最短路径。

**数学符号**：
d(u, v) = min{∑w(e) | e ∈ path from u to v}

**Rust 伪代码**：

```rust
use std::collections::BinaryHeap;
use std::cmp::Reverse;

fn dijkstra(graph: &Graph, start: usize) -> Vec<Option<u32>> {
    let n = graph.adjacency_list.len();
    let mut distances = vec![None; n];
    let mut heap = BinaryHeap::new();
    
    distances[start] = Some(0);
    heap.push(Reverse((0, start)));
    
    while let Some(Reverse((dist, vertex))) = heap.pop() {
        if distances[vertex].unwrap() < dist { continue; }
        
        for &neighbor in graph.neighbors(vertex) {
            let new_dist = dist + 1; // 假设所有边权重为1
            
            if distances[neighbor].is_none() || new_dist < distances[neighbor].unwrap() {
                distances[neighbor] = Some(new_dist);
                heap.push(Reverse((new_dist, neighbor)));
            }
        }
    }
    
    distances
}
```

**复杂度分析**：

- 时间复杂度：O((V + E) log V)
- 空间复杂度：O(V)

### 4.3 最小生成树算法

**理论定义**：
最小生成树是连接所有顶点的无环图，且总权重最小。

**数学符号**：
MST = argmin{∑w(e) | e ∈ T, T is spanning tree}

**Rust 伪代码**：

```rust
use std::collections::BinaryHeap;
use std::cmp::Reverse;

struct Edge {
    from: usize,
    to: usize,
    weight: u32
}

fn kruskal(edges: &[Edge], n: usize) -> Vec<Edge> {
    let mut edges = edges.to_vec();
    edges.sort_by_key(|e| e.weight);
    
    let mut uf = UnionFind::new(n);
    let mut mst = vec![];
    
    for edge in edges {
        if uf.find(edge.from) != uf.find(edge.to) {
            uf.union(edge.from, edge.to);
            mst.push(edge);
        }
    }
    
    mst
}

struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<usize>
}

impl UnionFind {
    fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
            rank: vec![0; n]
        }
    }
    
    fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }
    
    fn union(&mut self, x: usize, y: usize) {
        let px = self.find(x);
        let py = self.find(y);
        
        if px == py { return; }
        
        if self.rank[px] < self.rank[py] {
            self.parent[px] = py;
        } else if self.rank[px] > self.rank[py] {
            self.parent[py] = px;
        } else {
            self.parent[py] = px;
            self.rank[px] += 1;
        }
    }
}
```

## 5. 字符串算法

### 5.1 字符串匹配算法

**理论定义**：
字符串匹配算法用于在文本中查找模式串的位置。

**数学符号**：
给定文本 T[1..n] 和模式 P[1..m]，找到所有满足 T[i..i+m-1] = P 的位置 i。

**Rust 伪代码**：

```rust
fn kmp_search(text: &str, pattern: &str) -> Vec<usize> {
    let pattern_bytes = pattern.as_bytes();
    let text_bytes = text.as_bytes();
    let lps = compute_lps(pattern_bytes);
    
    let mut result = vec![];
    let (mut i, mut j) = (0, 0);
    
    while i < text_bytes.len() {
        if pattern_bytes[j] == text_bytes[i] {
            i += 1;
            j += 1;
        }
        
        if j == pattern_bytes.len() {
            result.push(i - j);
            j = lps[j - 1];
        } else if i < text_bytes.len() && pattern_bytes[j] != text_bytes[i] {
            if j != 0 {
                j = lps[j - 1];
            } else {
                i += 1;
            }
        }
    }
    
    result
}

fn compute_lps(pattern: &[u8]) -> Vec<usize> {
    let mut lps = vec![0; pattern.len()];
    let (mut len, mut i) = (0, 1);
    
    while i < pattern.len() {
        if pattern[i] == pattern[len] {
            len += 1;
            lps[i] = len;
            i += 1;
        } else {
            if len != 0 {
                len = lps[len - 1];
            } else {
                lps[i] = 0;
                i += 1;
            }
        }
    }
    
    lps
}
```

**复杂度分析**：

- 时间复杂度：O(n + m)
- 空间复杂度：O(m)

### 5.2 字符串压缩算法

**理论定义**：
字符串压缩算法用于减少字符串的存储空间。

**数学符号**：
压缩率 = (原始长度 - 压缩后长度) / 原始长度

**Rust 伪代码**：

```rust
fn run_length_encoding(s: &str) -> String {
    if s.is_empty() { return String::new(); }
    
    let mut result = String::new();
    let mut current_char = s.chars().next().unwrap();
    let mut count = 1;
    
    for c in s.chars().skip(1) {
        if c == current_char {
            count += 1;
        } else {
            result.push_str(&format!("{}{}", count, current_char));
            current_char = c;
            count = 1;
        }
    }
    
    result.push_str(&format!("{}{}", count, current_char));
    result
}

fn huffman_compress(text: &str) -> (String, HashMap<char, String>) {
    // 计算频率
    let mut frequencies = HashMap::new();
    for c in text.chars() {
        *frequencies.entry(c).or_insert(0) += 1;
    }
    
    // 构建Huffman树（简化版）
    let codes = huffman_encoding(&frequencies.values().copied().collect::<Vec<_>>());
    
    // 编码
    let mut encoded = String::new();
    for c in text.chars() {
        if let Some(code) = codes.get(&c) {
            encoded.push_str(code);
        }
    }
    
    (encoded, HashMap::new()) // 简化返回
}
```

## 6. 并行算法

### 6.1 并行计算模型

**理论定义**：
并行计算模型描述多个处理器同时执行计算任务的方式。

**数学符号**：
T_p(n) = T(n) / p + O(communication)

**Rust 伪代码**：

```rust
use std::thread;
use std::sync::{Arc, Mutex};

fn parallel_sum(arr: &[i32]) -> i32 {
    let num_threads = 4;
    let chunk_size = arr.len() / num_threads;
    let arr = Arc::new(arr.to_vec());
    let result = Arc::new(Mutex::new(0));
    
    let mut handles = vec![];
    
    for i in 0..num_threads {
        let arr = Arc::clone(&arr);
        let result = Arc::clone(&result);
        let start = i * chunk_size;
        let end = if i == num_threads - 1 { arr.len() } else { (i + 1) * chunk_size };
        
        let handle = thread::spawn(move || {
            let sum: i32 = arr[start..end].iter().sum();
            *result.lock().unwrap() += sum;
        });
        
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    *result.lock().unwrap()
}
```

### 6.2 MapReduce模型

**理论定义**：
MapReduce是一种并行编程模型，包含Map和Reduce两个阶段。

**数学符号**：
MapReduce = Map(data) → Reduce(mapped_data)

**Rust 伪代码**：

```rust
fn map_reduce_word_count(texts: Vec<String>) -> HashMap<String, usize> {
    // Map阶段：每个文本生成(word, 1)对
    let mapped: Vec<(String, usize)> = texts.into_iter()
        .flat_map(|text| {
            text.split_whitespace()
                .map(|word| (word.to_lowercase(), 1))
                .collect::<Vec<_>>()
        })
        .collect();
    
    // Reduce阶段：合并相同单词的计数
    let mut result = HashMap::new();
    for (word, count) in mapped {
        *result.entry(word).or_insert(0) += count;
    }
    
    result
}
```

## 7. 算法优化技术

### 7.1 缓存优化

**理论定义**：
缓存优化通过利用局部性原理提高算法性能。

**数学符号**：
缓存命中率 = 缓存命中次数 / 总访问次数

**Rust 伪代码**：

```rust
fn matrix_multiply_optimized(a: &[Vec<f64>], b: &[Vec<f64>]) -> Vec<Vec<f64>> {
    let n = a.len();
    let mut result = vec![vec![0.0; n]; n];
    
    // 分块矩阵乘法，提高缓存局部性
    let block_size = 32;
    
    for i in (0..n).step_by(block_size) {
        for j in (0..n).step_by(block_size) {
            for k in (0..n).step_by(block_size) {
                for ii in i..(i + block_size).min(n) {
                    for jj in j..(j + block_size).min(n) {
                        for kk in k..(k + block_size).min(n) {
                            result[ii][jj] += a[ii][kk] * b[kk][jj];
                        }
                    }
                }
            }
        }
    }
    
    result
}
```

### 7.2 内存优化

**理论定义**：
内存优化通过减少内存分配和访问提高算法效率。

**Rust 伪代码**：

```rust
fn fibonacci_iterative(n: usize) -> u64 {
    if n <= 1 { return n as u64; }
    
    let (mut prev, mut curr) = (0, 1);
    for _ in 2..=n {
        let next = prev + curr;
        prev = curr;
        curr = next;
    }
    
    curr
}

// 使用迭代器避免中间向量分配
fn filter_even_numbers(numbers: &[i32]) -> Vec<i32> {
    numbers.iter()
        .filter(|&&x| x % 2 == 0)
        .copied()
        .collect()
}
```

## 总结

本文档提供了算法与数据结构的完整形式化理论框架，包括：

1. **复杂度分析**：时间、空间复杂度的数学定义和证明
2. **基本数据结构**：线性表、栈、队列、树的实现
3. **高级算法**：分治、动态规划、贪心算法的理论基础
4. **图论算法**：最短路径、最小生成树算法
5. **字符串算法**：匹配、压缩算法
6. **并行算法**：并行计算模型和MapReduce
7. **优化技术**：缓存和内存优化

每个算法都包含：

- 严格的理论定义
- 数学符号表示
- 完整的Rust代码实现
- 复杂度分析
- 实际应用说明

这个框架为Rust语言中的算法实现提供了坚实的理论基础和实践指导。

---

## 实战实现索引（Rust 1.89 与国际百科对齐）

- 文档导航：
  - 算法复杂度与评估：`crates/c08_algorithms/docs/algorithm_complexity.md`
  - 数据结构实现：`crates/c08_algorithms/docs/data_structures.md`
  - 异步算法指南：`crates/c08_algorithms/docs/async_algorithms.md`
  - 性能优化：`crates/c08_algorithms/docs/performance_optimization.md`
  - Rust 1.89 特性应用：`crates/c08_algorithms/docs/rust_189_features.md`

- 核心模块入口：
  - 排序：`crates/c08_algorithms/src/sorting/mod.rs`（`sort_sync` / `sort_parallel` / `sort_async`）
  - 搜索：`crates/c08_algorithms/src/searching/mod.rs`（线性/二分/并行/异步）
  - 图论：`crates/c08_algorithms/src/graph/mod.rs`（BFS/Dijkstra/MST/Topo 的同步/并行/异步）
  - 分治：`crates/c08_algorithms/src/divide_and_conquer/mod.rs`（最大子段和、最近点对，含异步封装）
  - 动态规划：`crates/c08_algorithms/src/dynamic_programming/mod.rs`（LCS、0-1 背包，含异步封装）

- 基准：`crates/c08_algorithms/benches/alg_benches.rs`（包含排序/搜索/图/DP/分治/贪心）

- 快速使用（示例位于 README 中“基础用法”）：
  - 异步排序/搜索/图：`sort_async`、`binary_search_async`、`bfs_shortest_path_async`、`dijkstra_async`
  - 分治/动态规划异步：`max_subarray_sum_async`、`closest_pair_async`、`lcs_async`、`knapsack_01_async`