# 知识图谱

本页展示算法与数据结构的概念关系。

---

## 📊 核心概念关系图

```text
                   [算法与数据结构]
                         |
         +---------------+---------------+
         |               |               |
    [数据结构]       [算法设计]       [复杂度分析]
         |               |               |
    +----+----+     +----+----+     +----+----+
    |    |    |     |    |    |     |    |    |
  线性  树形  图    分治  动态  贪心  时间  空间  渐进
  结构  结构  结构        规划              分析
```

---

## 🎯 概念层次

### 1. 数据结构 (Data Structures)

**核心类别**:

- **线性结构**: 数组、链表、栈、队列、双端队列
- **树形结构**: 二叉树、BST、AVL树、红黑树、B树、堆
- **图结构**: 有向图、无向图、加权图、DAG
- **散列结构**: 哈希表、布隆过滤器

**Rust 特性**:

- **Vec**: 动态数组
- **VecDeque**: 双端队列
- **BinaryHeap**: 二叉堆
- **HashMap/BTreeMap**: 关联容器

---

### 2. 算法设计范式 (Algorithm Paradigms)

**核心范式**:

- **分治法** (Divide and Conquer): 快速排序、归并排序
- **动态规划** (Dynamic Programming): 背包问题、最长子序列
- **贪心算法** (Greedy): 最小生成树、哈夫曼编码
- **回溯算法** (Backtracking): N皇后、迷宫问题
- **分支限界** (Branch and Bound): 旅行商问题

**Rust 实现特点**:

- 零成本抽象
- 迭代器组合
- 所有权优化
- 并发安全

---

### 3. 复杂度分析 (Complexity Analysis)

**时间复杂度**:

- O(1) - 常数时间
- O(log n) - 对数时间
- O(n) - 线性时间
- O(n log n) - 线性对数时间
- O(n²) - 平方时间

**空间复杂度**:

- 原地算法 O(1)
- 递归深度
- 缓存空间

---

## 🔗 概念关联

### 数据结构 ←→ 算法设计

```rust
// 数据结构选择影响算法效率
use std::collections::BinaryHeap;

// 优先队列 + 贪心算法 = Dijkstra最短路径
fn dijkstra(graph: &[(Vec<(usize, i32)>)], start: usize) -> Vec<i32> {
    let mut distances = vec![i32::MAX; graph.len()];
    let mut heap = BinaryHeap::new();
    
    distances[start] = 0;
    heap.push((0, start));
    
    while let Some((dist, node)) = heap.pop() {
        // 贪心选择当前最短路径
        if -dist > distances[node] { continue; }
        
        for &(neighbor, weight) in &graph[node] {
            let new_dist = distances[node] + weight;
            if new_dist < distances[neighbor] {
                distances[neighbor] = new_dist;
                heap.push((-new_dist, neighbor));
            }
        }
    }
    
    distances
}
```

### 算法范式 ←→ 复杂度

```rust
// 动态规划: 空间换时间
fn fibonacci_dp(n: usize) -> u64 {
    let mut dp = vec![0; n + 1];
    dp[1] = 1;
    
    for i in 2..=n {
        dp[i] = dp[i-1] + dp[i-2];
    }
    
    dp[n]  // O(n) 时间, O(n) 空间
}

// 优化: 降低空间复杂度
fn fibonacci_optimized(n: usize) -> u64 {
    let (mut prev, mut curr) = (0, 1);
    
    for _ in 2..=n {
        let next = prev + curr;
        prev = curr;
        curr = next;
    }
    
    curr  // O(n) 时间, O(1) 空间
}
```

### 并发 ←→ 算法

```rust
use rayon::prelude::*;

// 并行快速排序
fn parallel_quicksort<T: Ord + Send>(arr: &mut [T]) {
    if arr.len() <= 1 { return; }
    
    let mid = partition(arr);
    let (left, right) = arr.split_at_mut(mid);
    
    rayon::join(
        || parallel_quicksort(left),
        || parallel_quicksort(right),
    );
}
```

---

## 📚 学习路径图

```text
第一步: 掌握基本数据结构
    ↓
第二步: 学习排序和搜索算法
    ↓
第三步: 理解算法设计范式
    ↓
第四步: 掌握图算法
    ↓
第五步: 并发与异步算法
```

---

## 🎓 算法分类体系

### 排序算法

| 算法 | 时间复杂度 | 空间复杂度 | 稳定性 |
|------|-----------|-----------|--------|
| 快速排序 | O(n log n) | O(log n) | 不稳定 |
| 归并排序 | O(n log n) | O(n) | 稳定 |
| 堆排序 | O(n log n) | O(1) | 不稳定 |
| 插入排序 | O(n²) | O(1) | 稳定 |

### 搜索算法

| 算法 | 时间复杂度 | 适用场景 |
|------|-----------|---------|
| 二分搜索 | O(log n) | 有序数组 |
| 哈希查找 | O(1) | 键值对 |
| DFS | O(V+E) | 图遍历 |
| BFS | O(V+E) | 最短路径 |

### 图算法

| 算法 | 时间复杂度 | 用途 |
|------|-----------|------|
| Dijkstra | O((V+E) log V) | 单源最短路径 |
| Floyd-Warshall | O(V³) | 全源最短路径 |
| Kruskal | O(E log E) | 最小生成树 |
| Prim | O((V+E) log V) | 最小生成树 |

---

## 💡 核心原则

### 1. 选择合适的数据结构

```text
数据结构 → 算法效率 → 系统性能
```

### 2. 权衡时间与空间

```text
时间换空间 ← 动态规划 → 空间换时间
```

### 3. 利用 Rust 特性

```text
所有权 → 零成本抽象 → 高效实现
```

---

## 🔍 Rust 1.90 增强特性

### 1. 高级类型推断

```rust
// 复杂类型自动推断
let graph: Vec<Vec<_>> = (0..n)
    .map(|_| Vec::new())
    .collect();
```

### 2. 并发算法

```rust
use tokio::task;

// 异步并行计算
async fn parallel_map<F, T, R>(data: Vec<T>, f: F) -> Vec<R>
where
    F: Fn(T) -> R + Send + Sync + 'static,
    T: Send + 'static,
    R: Send + 'static,
{
    let handles: Vec<_> = data
        .into_iter()
        .map(|item| task::spawn_blocking(move || f(item)))
        .collect();
    
    let mut results = Vec::new();
    for handle in handles {
        results.push(handle.await.unwrap());
    }
    results
}
```

### 3. 泛型优化

```rust
// 使用 const 泛型优化数组算法
fn array_sum<T, const N: usize>(arr: [T; N]) -> T
where
    T: std::ops::Add<Output = T> + Default + Copy,
{
    arr.into_iter().fold(T::default(), |acc, x| acc + x)
}
```

---

## 📖 相关章节

- **[基础概念](./foundations.md)** - 理论详解
- **[实践指南](./guides.md)** - 实现技巧
- **[代码示例](./examples.md)** - 算法实现 ⭐
- **[返回模块首页](./README.md)**

---

## 🔗 扩展学习

### 深入阅读

- [完整知识图谱](../../crates/c08_algorithms/docs/KNOWLEDGE_GRAPH.md)
- [算法理论](../../crates/c08_algorithms/docs/theory/README.md)
- [形式化分析](../../crates/c08_algorithms/docs/theory_enhanced/README.md)

### 相关模块

- **[C05: 多线程](../c05/README.md)** - 并行算法
- **[C06: 异步编程](../c06/README.md)** - 异步算法
- **[C09: 设计模式](../c09/README.md)** - 算法模式

---

## 🎯 实践项目建议

### 入门级

- 实现基本排序算法
- 二叉树遍历
- 简单图算法

### 进阶级

- LRU 缓存
- 并发数据结构
- 高性能哈希表

### 高级

- 分布式算法
- 无锁数据结构
- 实时系统算法

---

**理解算法与数据结构的关系是高效编程的基础！** 🚀
