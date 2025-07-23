# 算法与数据结构（形式化推进目录）

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

- 1.2 空间复杂度的理论基础

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

- 1.3 渐进符号与证明

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

- 2.1 线性表（数组、链表）形式化

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

- 2.2 栈与队列的数学模型

**理论定义**：
栈（Stack）是后进先出（LIFO）结构，队列（Queue）是先进先出（FIFO）结构。

**结构符号**：
Stack = [a₁, a₂, ..., aₙ]，push(x), pop() -> x
Queue = [a₁, a₂, ..., aₙ]，enqueue(x), dequeue() -> x

**Rust 伪代码**：

```rust
let mut stack = Vec::new();
stack.push(1); stack.pop();
let mut queue = std::collections::VecDeque::new();
queue.push_back(1); queue.pop_front();
```

**简要说明**：
栈适合递归、回溯，队列适合广度优先等场景。

- 2.3 树与图的结构定义

**理论定义**：
树（Tree）是无环连通图，图（Graph）是由顶点和边组成的结构。

**结构符号**：
Tree = (V, E), |E| = |V|-1
Graph = (V, E)

**Rust 伪代码**：

```rust
struct TreeNode { val: i32, children: Vec<TreeNode> }
struct Graph { adj: Vec<Vec<usize>> }
```

**简要说明**：
树适合层次结构建模，图适合复杂关系建模。

## 3. 排序算法

- 3.1 比较排序的理论分析

**理论定义**：
比较排序通过元素间的比较确定顺序，常见有冒泡、插入、归并、快速排序等。

**数学符号**：
最优比较排序下界：Ω(n log n)

**Rust 伪代码**：

```rust
fn merge_sort(arr: &mut [i32]) {
    if arr.len() <= 1 { return; }
    let mid = arr.len() / 2;
    merge_sort(&mut arr[..mid]);
    merge_sort(&mut arr[mid..]);
    let mut merged = arr.to_vec();
    let (mut i, mut j, mut k) = (0, mid, 0);
    while i < mid && j < arr.len() {
        if arr[i] < arr[j] { merged[k] = arr[i]; i += 1; }
        else { merged[k] = arr[j]; j += 1; }
        k += 1;
    }
    while i < mid { merged[k] = arr[i]; i += 1; k += 1; }
    while j < arr.len() { merged[k] = arr[j]; j += 1; k += 1; }
    arr.copy_from_slice(&merged);
}
```

**简要说明**：
比较排序的时间复杂度下界为 Ω(n log n)。

- 3.2 非比较排序的形式化

**理论定义**：
非比较排序不依赖元素间比较，常见有计数排序、基数排序、桶排序等。

**数学符号**：
计数排序时间复杂度 O(n+k)，k 为数据范围

**Rust 伪代码**：

```rust
fn counting_sort(arr: &mut [usize], max: usize) {
    let mut count = vec![0; max+1];
    for &x in arr.iter() { count[x] += 1; }
    let mut i = 0;
    for (num, &c) in count.iter().enumerate() {
        for _ in 0..c { arr[i] = num; i += 1; }
    }
}
```

**简要说明**：
非比较排序适用于数据范围有限的场景。

- 3.3 稳定性与最优性证明

**理论定义**：
排序算法的稳定性指相等元素排序后相对顺序不变，最优性指达到理论复杂度下界。

**数学符号**：
设 S 是排序算法，若 ∀i<j, arr[i]=arr[j]，排序后 i'<j'，则 S 稳定。

**Rust 伪代码**：

```rust
fn stable_sort(arr: &mut [(i32, usize)]) {
    arr.sort_by(|a, b| a.0.cmp(&b.0));
}
// Rust 标准库 sort_by 是稳定排序
```

**简要说明**：
归并排序等为稳定排序，快速排序通常不稳定。

## 4. 图算法

- 4.1 图的数学基础与表示

**理论定义**：
图由顶点集合和边集合组成，可分为有向图和无向图。

**数学符号**：
Graph = (V, E)
有向图：E ⊆ V × V
无向图：E ⊆ {{u, v} | u, v ∈ V}

**Rust 伪代码**：

```rust
struct Graph { adj: Vec<Vec<usize>> }
```

**简要说明**：
图结构广泛用于建模网络、关系和路径。

- 4.2 最短路径算法的形式化

**理论定义**：
最短路径算法用于在加权图中寻找两点间权重和最小的路径。

**数学符号**：
设 G=(V,E,w)，d(u,v) = min_{path} Σw(e)

**Rust 伪代码**：

```rust
use std::collections::BinaryHeap;
fn dijkstra(adj: &Vec<Vec<(usize, u32)>>, start: usize) -> Vec<u32> {
    let n = adj.len();
    let mut dist = vec![u32::MAX; n];
    let mut heap = BinaryHeap::new();
    dist[start] = 0;
    heap.push((0, start));
    while let Some((cost, u)) = heap.pop() {
        for &(v, w) in &adj[u] {
            let next = cost + w as i32;
            if (next as u32) < dist[v] {
                dist[v] = next as u32;
                heap.push((-(next as i32), v));
            }
        }
    }
    dist
}
```

**简要说明**：
Dijkstra 算法适用于无负权边的最短路径问题。

- 4.3 最小生成树的理论证明

**理论定义**：
最小生成树（MST）是连接图中所有顶点且权重和最小的无环子图。

**数学符号**：
设 G=(V,E,w)，MST T ⊆ E，|T|=|V|-1，Σ_{e∈T}w(e) 最小

**Rust 伪代码**：

```rust
fn kruskal(n: usize, mut edges: Vec<(u32, usize, usize)>) -> u32 {
    edges.sort();
    let mut parent = (0..n).collect::<Vec<_>>();
    fn find(p: &mut Vec<usize>, x: usize) -> usize {
        if p[x] != x { p[x] = find(p, p[x]); } p[x]
    }
    let mut total = 0;
    for (w, u, v) in edges {
        let (pu, pv) = (find(&mut parent, u), find(&mut parent, v));
        if pu != pv { parent[pu] = pv; total += w; }
    }
    total
}
```

**简要说明**：
Kruskal 算法基于贪心策略，能正确求解无向连通图的 MST。

## 5. 动态规划

- 5.1 状态转移方程的形式化

**理论定义**：
动态规划通过状态转移方程递归求解最优子结构问题。

**数学符号**：
设 f(i) = min/max { f(j) + cost(j, i) | j < i }

**Rust 伪代码**：

```rust
fn fib(n: usize) -> usize {
    let mut dp = vec![0; n+1];
    dp[0] = 0; dp[1] = 1;
    for i in 2..=n { dp[i] = dp[i-1] + dp[i-2]; }
    dp[n]
}
```

**简要说明**：
状态转移方程是动态规划的核心。

- 5.2 最优子结构与重叠子问题

**理论定义**：
最优子结构：问题的最优解包含其子问题的最优解。
重叠子问题：同一子问题被多次求解。

**数学符号**：
f(i) = min/max { f(j) + cost(j, i) | j < i }

**Rust 伪代码**：

```rust
fn coin_change(coins: &[usize], amount: usize) -> usize {
    let mut dp = vec![amount+1; amount+1];
    dp[0] = 0;
    for i in 1..=amount {
        for &c in coins {
            if i >= c { dp[i] = dp[i].min(dp[i-c]+1); }
        }
    }
    if dp[amount] > amount { 0 } else { dp[amount] }
}
```

**简要说明**：
动态规划适用于具有最优子结构和重叠子问题的问题。

## 6. 并行与分布式算法

- 6.1 并行模型与复杂度

**理论定义**：
并行算法利用多处理器同时计算以加速问题求解。

**数学符号**：
T_p(n)：p 个处理器下的运行时间
Speedup S_p(n) = T_1(n) / T_p(n)

**Rust 伪代码**：

```rust
use rayon::prelude::*;
fn parallel_sum(arr: &[i32]) -> i32 {
    arr.par_iter().sum()
}
```

**简要说明**：
并行模型分析加速比、效率和可扩展性。

- 6.2 分布式一致性算法  [TODO]

## 7. 工程案例与代码示例

- 7.1 Rust 算法库设计  [TODO]
- 7.2 典型数据结构实现  [TODO]

## 8. 理论贡献与方法论总结  [TODO]

---

### 推进计划与断点快照

- [x] 目录骨架搭建
- [ ] 复杂度分析小节补全
- [ ] 数据结构小节补全
- [ ] 算法与证明小节补全
- [ ] 工程案例与代码补全
- [ ] 理论贡献总结
