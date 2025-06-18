# Rust 算法与数据结构形式化理论

## 目录

1. [理论基础](#理论基础)
   1.1. [算法复杂度分析](#算法复杂度分析)
   1.2. [数据结构形式化定义](#数据结构形式化定义)
   1.3. [算法正确性证明](#算法正确性证明)
   1.4. [Rust 算法特性](#rust-算法特性)

2. [基础数据结构](#基础数据结构)
   2.1. [线性结构](#线性结构)
   2.2. [树结构](#树结构)
   2.3. [图结构](#图结构)
   2.4. [散列结构](#散列结构)

3. [排序算法](#排序算法)
   3.1. [比较排序](#比较排序)
   3.2. [非比较排序](#非比较排序)
   3.3. [排序算法分析](#排序算法分析)

4. [搜索算法](#搜索算法)
   4.1. [线性搜索](#线性搜索)
   4.2. [二分搜索](#二分搜索)
   4.3. [高级搜索](#高级搜索)

5. [图论算法](#图论算法)
   5.1. [图遍历](#图遍历)
   5.2. [最短路径](#最短路径)
   5.3. [最小生成树](#最小生成树)

6. [动态规划](#动态规划)
   6.1. [动态规划原理](#动态规划原理)
   6.2. [经典问题](#经典问题)
   6.3. [优化技巧](#优化技巧)

7. [分治算法](#分治算法)
   7.1. [分治原理](#分治原理)
   7.2. [经典算法](#经典算法)
   7.3. [并行分治](#并行分治)

8. [贪心算法](#贪心算法)
   8.1. [贪心原理](#贪心原理)
   8.2. [贪心选择](#贪心选择)
   8.3. [最优性证明](#最优性证明)

9. [回溯算法](#回溯算法)
   9.1. [回溯原理](#回溯原理)
   9.2. [状态空间搜索](#状态空间搜索)
   9.3. [剪枝优化](#剪枝优化)

10. [并行算法](#并行算法)
    10.1. [并行模型](#并行模型)
    10.2. [并行排序](#并行排序)
    10.3. [并行搜索](#并行搜索)

---

## 1. 理论基础

### 1.1 算法复杂度分析

**定义 1.1.1 (算法)**
算法是解决特定问题的明确定义的计算过程：
$$\text{Algorithm} = \langle \text{Input}, \text{Output}, \text{Steps}, \text{Termination} \rangle$$

**定义 1.1.2 (时间复杂度)**
算法的时间复杂度是输入规模 $n$ 的函数：
$$T(n) = O(f(n)) \iff \exists c, n_0 > 0, \forall n \geq n_0, T(n) \leq c \cdot f(n)$$

**定义 1.1.3 (空间复杂度)**
算法的空间复杂度是额外空间使用量：
$$S(n) = O(f(n)) \iff \exists c, n_0 > 0, \forall n \geq n_0, S(n) \leq c \cdot f(n)$$

**定理 1.1.1 (主定理)**
对于递归算法 $T(n) = aT(n/b) + f(n)$：
$$\text{Master Theorem} = \begin{cases}
O(n^{\log_b a}) & \text{if } f(n) = O(n^{\log_b a - \epsilon}) \\
O(f(n) \log n) & \text{if } f(n) = \Theta(n^{\log_b a}) \\
O(f(n)) & \text{if } f(n) = \Omega(n^{\log_b a + \epsilon})
\end{cases}$$

### 1.2 数据结构形式化定义

**定义 1.2.1 (数据结构)**
数据结构是数据的组织、管理和存储格式：
$$\text{DataStructure} = \langle \text{Elements}, \text{Operations}, \text{Constraints} \rangle$$

**定义 1.2.2 (抽象数据类型)**
抽象数据类型是数据结构的数学抽象：
$$\text{ADT} = \langle \text{Signature}, \text{Axioms}, \text{Implementation} \rangle$$

### 1.3 算法正确性证明

**定义 1.3.1 (算法正确性)**
算法 $A$ 对问题 $P$ 是正确的，当且仅当：
$$\forall x \in \text{Input}, A(x) \in \text{Output} \land P(x, A(x))$$

**定义 1.3.2 (循环不变量)**
循环不变量是在循环执行过程中保持为真的性质：
$$\text{Invariant}(i) = \text{Precondition} \land \text{LoopCondition}(i) \implies \text{Invariant}(i+1)$$

### 1.4 Rust 算法特性

**特征 1.4.1 (零成本抽象)**
Rust 的零成本抽象确保算法实现的高效性：
$$\text{ZeroCost}(abstraction) = \text{Performance}(abstraction) = \text{Performance}(manual)$$

**特征 1.4.2 (内存安全)**
Rust 的所有权系统确保算法实现的安全性：
$$\text{MemorySafety}(algorithm) = \text{NoDataRaces}(algorithm) \land \text{NoUseAfterFree}(algorithm)$$

---

## 2. 基础数据结构

### 2.1 线性结构

**定义 2.1.1 (动态数组)**
动态数组是具有自动扩容能力的数组：
$$\text{DynamicArray}[T] = \langle \text{capacity}, \text{size}, \text{data}: \text{Vec}[T] \rangle$$

**定理 2.1.1 (动态数组摊销复杂度)**
具有倍增扩容策略的动态数组，插入操作的摊销时间复杂度为 $O(1)$。

**证明：**
假设初始容量为 1，每次扩容为原来的 2 倍。经过 $n$ 次插入操作后，总共的元素搬移次数为：
$$\sum_{i=0}^{\lfloor \log_2 n \rfloor} 2^i = 2^{\lfloor \log_2 n \rfloor + 1} - 1 < 2n$$
因此 $n$ 次操作的摊销代价为 $O(1)$。

**Rust 实现：**
```rust
pub struct DynamicArray<T> {
    data: Vec<T>,
}

impl<T> DynamicArray<T> {
    pub fn new() -> Self {
        Self { data: Vec::new() }
    }
    
    pub fn push(&mut self, item: T) {
        self.data.push(item); // Vec 已实现动态扩容
    }
    
    pub fn pop(&mut self) -> Option<T> {
        self.data.pop()
    }
    
    pub fn get(&self, index: usize) -> Option<&T> {
        self.data.get(index)
    }
}
```

**定义 2.1.2 (链表)**
链表是由节点组成的线性结构：
$$\text{LinkedList}[T] = \langle \text{head}: \text{Option}[\text{Node}[T]] \rangle$$
$$\text{Node}[T] = \langle \text{value}: T, \text{next}: \text{Option}[\text{Box}[\text{Node}[T]]] \rangle$$

**Rust 实现：**
```rust
pub struct List<T> {
    head: Option<Box<Node<T>>>,
}

struct Node<T> {
    value: T,
    next: Option<Box<Node<T>>>,
}

impl<T> List<T> {
    pub fn new() -> Self {
        Self { head: None }
    }
    
    pub fn push_front(&mut self, value: T) {
        let new_node = Box::new(Node {
            value,
            next: self.head.take(),
        });
        self.head = Some(new_node);
    }
    
    pub fn pop_front(&mut self) -> Option<T> {
        self.head.take().map(|node| {
            self.head = node.next;
            node.value
        })
    }
}
```

### 2.2 树结构

**定义 2.2.1 (二叉树)**
二叉树是每个节点最多有两个子节点的树：
$$\text{BinaryTree}[T] = \langle \text{value}: T, \text{left}: \text{Option}[\text{Box}[\text{BinaryTree}[T]]], \text{right}: \text{Option}[\text{Box}[\text{BinaryTree}[T]]] \rangle$$

**定义 2.2.2 (二叉搜索树)**
二叉搜索树是满足搜索性质的二叉树：
$$\text{BSTProperty}(node) = \begin{cases}
\text{true} & \text{if } node = \text{null} \\
\text{left}(node).\text{value} < node.\text{value} < \text{right}(node).\text{value} \land \\
\text{BSTProperty}(\text{left}(node)) \land \text{BSTProperty}(\text{right}(node)) & \text{otherwise}
\end{cases}$$

**定理 2.2.1 (BST 操作复杂度)**
在平衡的二叉搜索树中，查找、插入、删除操作的时间复杂度为 $O(\log n)$。

**Rust 实现：**
```rust
pub struct BinarySearchTree<T: Ord> {
    root: Option<Box<Node<T>>>,
}

struct Node<T: Ord> {
    value: T,
    left: Option<Box<Node<T>>>,
    right: Option<Box<Node<T>>>,
}

impl<T: Ord> BinarySearchTree<T> {
    pub fn new() -> Self {
        Self { root: None }
    }
    
    pub fn insert(&mut self, value: T) {
        self.root = Some(Box::new(self.insert_recursive(self.root.take(), value)));
    }
    
    fn insert_recursive(&self, node: Option<Box<Node<T>>>, value: T) -> Node<T> {
        match node {
            None => Node { value, left: None, right: None },
            Some(mut node) => {
                if value < node.value {
                    node.left = Some(Box::new(self.insert_recursive(node.left.take(), value)));
                } else {
                    node.right = Some(Box::new(self.insert_recursive(node.right.take(), value)));
                }
                *node
            }
        }
    }
}
```

### 2.3 图结构

**定义 2.3.1 (图)**
图是顶点和边的集合：
$$\text{Graph} = \langle V, E \rangle$$
其中 $V$ 是顶点集合，$E \subseteq V \times V$ 是边集合。

**定义 2.3.2 (邻接矩阵)**
邻接矩阵是图的矩阵表示：
$$A[i][j] = \begin{cases}
1 & \text{if } (i, j) \in E \\
0 & \text{otherwise}
\end{cases}$$

**定义 2.3.3 (邻接表)**
邻接表是图的链表表示：
$$\text{AdjacencyList}[V] = \text{Map}[V, \text{List}[V]]$$

**Rust 实现：**
```rust
use std::collections::HashMap;

pub struct Graph {
    adjacency_list: HashMap<usize, Vec<usize>>,
}

impl Graph {
    pub fn new() -> Self {
        Self {
            adjacency_list: HashMap::new(),
        }
    }
    
    pub fn add_edge(&mut self, from: usize, to: usize) {
        self.adjacency_list.entry(from).or_insert_with(Vec::new).push(to);
    }
    
    pub fn get_neighbors(&self, vertex: usize) -> Option<&Vec<usize>> {
        self.adjacency_list.get(&vertex)
    }
}
```

### 2.4 散列结构

**定义 2.4.1 (散列表)**
散列表是通过散列函数组织数据的结构：
$$\text{HashTable}[K, V] = \langle \text{buckets}: \text{Array}[\text{List}[\langle K, V \rangle]], \text{hash}: K \rightarrow \text{usize} \rangle$$

**定义 2.4.2 (散列函数)**
散列函数将键映射到桶索引：
$$\text{hash}: K \rightarrow \{0, 1, ..., m-1\}$$

**定理 2.4.1 (散列表平均复杂度)**
在均匀散列的假设下，散列表的平均查找、插入、删除时间复杂度为 $O(1)$。

---

## 3. 排序算法

### 3.1 比较排序

**定义 3.1.1 (比较排序)**
比较排序是通过比较元素确定相对顺序的排序算法。

**定理 3.1.1 (比较排序下界)**
任何基于比较的排序算法的最坏情况时间复杂度为 $\Omega(n \log n)$。

**证明：**
比较排序的决策树有 $n!$ 个叶子节点，树的高度至少为 $\log_2(n!)$。根据斯特林公式，$\log_2(n!) = \Theta(n \log n)$。

#### 3.1.1 快速排序

**算法 3.1.1 (快速排序)**
```rust
pub fn quicksort<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let pivot_index = partition(arr);
    quicksort(&mut arr[..pivot_index]);
    quicksort(&mut arr[pivot_index + 1..]);
}

fn partition<T: Ord>(arr: &mut [T]) -> usize {
    let pivot_index = arr.len() - 1;
    let mut i = 0;
    
    for j in 0..pivot_index {
        if arr[j] <= arr[pivot_index] {
            arr.swap(i, j);
            i += 1;
        }
    }
    
    arr.swap(i, pivot_index);
    i
}
```

**定理 3.1.2 (快速排序复杂度)**
快速排序的平均时间复杂度为 $O(n \log n)$，最坏情况为 $O(n^2)$。

#### 3.1.2 归并排序

**算法 3.1.2 (归并排序)**
```rust
pub fn mergesort<T: Ord + Clone>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let mid = arr.len() / 2;
    mergesort(&mut arr[..mid]);
    mergesort(&mut arr[mid..]);
    merge(arr, mid);
}

fn merge<T: Ord + Clone>(arr: &mut [T], mid: usize) {
    let left = arr[..mid].to_vec();
    let right = arr[mid..].to_vec();
    
    let mut i = 0;
    let mut j = 0;
    let mut k = 0;
    
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            arr[k] = left[i].clone();
            i += 1;
        } else {
            arr[k] = right[j].clone();
            j += 1;
        }
        k += 1;
    }
    
    while i < left.len() {
        arr[k] = left[i].clone();
        i += 1;
        k += 1;
    }
    
    while j < right.len() {
        arr[k] = right[j].clone();
        j += 1;
        k += 1;
    }
}
```

**定理 3.1.3 (归并排序复杂度)**
归并排序的时间复杂度为 $O(n \log n)$，空间复杂度为 $O(n)$。

### 3.2 非比较排序

#### 3.2.1 计数排序

**算法 3.2.1 (计数排序)**
```rust
pub fn counting_sort(arr: &[usize], max_value: usize) -> Vec<usize> {
    let mut count = vec![0; max_value + 1];
    let mut output = vec![0; arr.len()];
    
    // 计数
    for &x in arr {
        count[x] += 1;
    }
    
    // 累加
    for i in 1..=max_value {
        count[i] += count[i - 1];
    }
    
    // 输出
    for &x in arr.iter().rev() {
        output[count[x] - 1] = x;
        count[x] -= 1;
    }
    
    output
}
```

**定理 3.2.1 (计数排序复杂度)**
计数排序的时间复杂度为 $O(n + k)$，其中 $k$ 是数据范围。

### 3.3 排序算法分析

**排序算法比较表：**

| 算法 | 平均时间 | 最坏时间 | 空间 | 稳定性 |
|------|----------|----------|------|--------|
| 快速排序 | $O(n \log n)$ | $O(n^2)$ | $O(\log n)$ | 不稳定 |
| 归并排序 | $O(n \log n)$ | $O(n \log n)$ | $O(n)$ | 稳定 |
| 堆排序 | $O(n \log n)$ | $O(n \log n)$ | $O(1)$ | 不稳定 |
| 计数排序 | $O(n + k)$ | $O(n + k)$ | $O(k)$ | 稳定 |

---

## 4. 搜索算法

### 4.1 线性搜索

**算法 4.1.1 (线性搜索)**
```rust
pub fn linear_search<T: PartialEq>(arr: &[T], target: &T) -> Option<usize> {
    for (i, item) in arr.iter().enumerate() {
        if item == target {
            return Some(i);
        }
    }
    None
}
```

**定理 4.1.1 (线性搜索复杂度)**
线性搜索的时间复杂度为 $O(n)$。

### 4.2 二分搜索

**算法 4.2.1 (二分搜索)**
```rust
pub fn binary_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
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
```

**定理 4.2.1 (二分搜索复杂度)**
二分搜索的时间复杂度为 $O(\log n)$。

**循环不变量：**
- 如果目标元素存在，它一定在 $[left, right)$ 范围内
- 每次迭代后，搜索范围至少减少一半

### 4.3 高级搜索

#### 4.3.1 深度优先搜索

**算法 4.3.1 (DFS)**
```rust
pub fn dfs(graph: &Graph, start: usize, visited: &mut Vec<bool>) {
    visited[start] = true;
    println!("Visited: {}", start);
    
    if let Some(neighbors) = graph.get_neighbors(start) {
        for &neighbor in neighbors {
            if !visited[neighbor] {
                dfs(graph, neighbor, visited);
            }
        }
    }
}
```

#### 4.3.2 广度优先搜索

**算法 4.3.2 (BFS)**
```rust
use std::collections::VecDeque;

pub fn bfs(graph: &Graph, start: usize) {
    let mut visited = vec![false; graph.adjacency_list.len()];
    let mut queue = VecDeque::new();
    
    visited[start] = true;
    queue.push_back(start);
    
    while let Some(vertex) = queue.pop_front() {
        println!("Visited: {}", vertex);
        
        if let Some(neighbors) = graph.get_neighbors(vertex) {
            for &neighbor in neighbors {
                if !visited[neighbor] {
                    visited[neighbor] = true;
                    queue.push_back(neighbor);
                }
            }
        }
    }
}
```

---

## 5. 图论算法

### 5.1 图遍历

**定理 5.1.1 (DFS 复杂度)**
深度优先搜索的时间复杂度为 $O(|V| + |E|)$。

**定理 5.1.2 (BFS 复杂度)**
广度优先搜索的时间复杂度为 $O(|V| + |E|)$。

### 5.2 最短路径

#### 5.2.1 Dijkstra 算法

**算法 5.2.1 (Dijkstra)**
```rust
use std::collections::BinaryHeap;
use std::cmp::Reverse;

pub fn dijkstra(graph: &Graph, start: usize) -> Vec<usize> {
    let mut distances = vec![usize::MAX; graph.adjacency_list.len()];
    let mut heap = BinaryHeap::new();
    
    distances[start] = 0;
    heap.push(Reverse((0, start)));
    
    while let Some(Reverse((dist, vertex))) = heap.pop() {
        if dist > distances[vertex] {
            continue;
        }
        
        if let Some(neighbors) = graph.get_neighbors(vertex) {
            for &neighbor in neighbors {
                let new_dist = dist + 1; // 假设所有边权重为 1
                if new_dist < distances[neighbor] {
                    distances[neighbor] = new_dist;
                    heap.push(Reverse((new_dist, neighbor)));
                }
            }
        }
    }
    
    distances
}
```

**定理 5.2.1 (Dijkstra 复杂度)**
Dijkstra 算法的时间复杂度为 $O((|V| + |E|) \log |V|)$。

### 5.3 最小生成树

#### 5.3.1 Kruskal 算法

**算法 5.3.1 (Kruskal)**
```rust
pub struct Edge {
    from: usize,
    to: usize,
    weight: usize,
}

pub fn kruskal(edges: &mut [Edge], num_vertices: usize) -> Vec<Edge> {
    edges.sort_by_key(|e| e.weight);
    
    let mut union_find = UnionFind::new(num_vertices);
    let mut mst = Vec::new();
    
    for edge in edges {
        if union_find.find(edge.from) != union_find.find(edge.to) {
            union_find.union(edge.from, edge.to);
            mst.push(*edge);
        }
    }
    
    mst
}
```

---

## 6. 动态规划

### 6.1 动态规划原理

**定义 6.1.1 (动态规划)**
动态规划是通过将问题分解为子问题来解决复杂问题的算法设计方法。

**动态规划特征：**
1. **最优子结构**：问题的最优解包含子问题的最优解
2. **重叠子问题**：子问题被重复计算
3. **状态转移方程**：问题解与子问题解的关系

**定理 6.1.1 (动态规划正确性)**
如果问题具有最优子结构性质，则动态规划算法能正确求解。

### 6.2 经典问题

#### 6.2.1 斐波那契数列

**算法 6.2.1 (动态规划斐波那契)**
```rust
pub fn fibonacci_dp(n: usize) -> usize {
    if n <= 1 {
        return n;
    }
    
    let mut dp = vec![0; n + 1];
    dp[0] = 0;
    dp[1] = 1;
    
    for i in 2..=n {
        dp[i] = dp[i - 1] + dp[i - 2];
    }
    
    dp[n]
}
```

**状态转移方程：**
$$F(n) = \begin{cases}
n & \text{if } n \leq 1 \\
F(n-1) + F(n-2) & \text{otherwise}
\end{cases}$$

#### 6.2.2 最长公共子序列

**算法 6.2.2 (LCS)**
```rust
pub fn longest_common_subsequence(text1: &str, text2: &str) -> usize {
    let m = text1.len();
    let n = text2.len();
    let mut dp = vec![vec![0; n + 1]; m + 1];
    
    for i in 1..=m {
        for j in 1..=n {
            if text1.chars().nth(i - 1) == text2.chars().nth(j - 1) {
                dp[i][j] = dp[i - 1][j - 1] + 1;
            } else {
                dp[i][j] = dp[i - 1][j].max(dp[i][j - 1]);
            }
        }
    }
    
    dp[m][n]
}
```

**状态转移方程：**
$$LCS(i, j) = \begin{cases}
0 & \text{if } i = 0 \text{ or } j = 0 \\
LCS(i-1, j-1) + 1 & \text{if } s1[i-1] = s2[j-1] \\
\max(LCS(i-1, j), LCS(i, j-1)) & \text{otherwise}
\end{cases}$$

### 6.3 优化技巧

**空间优化：**
- 滚动数组：只保存必要的状态
- 状态压缩：使用位运算表示状态

**时间优化：**
- 记忆化搜索：避免重复计算
- 状态剪枝：提前终止无效分支

---

## 7. 分治算法

### 7.1 分治原理

**定义 7.1.1 (分治算法)**
分治算法将问题分解为更小的子问题，递归求解，然后合并结果。

**分治步骤：**
1. **分解**：将问题分解为子问题
2. **解决**：递归求解子问题
3. **合并**：将子问题的解合并为原问题的解

**定理 7.1.1 (分治复杂度)**
分治算法的时间复杂度满足：
$$T(n) = aT(n/b) + f(n)$$
其中 $a$ 是子问题数量，$b$ 是问题规模缩小因子，$f(n)$ 是合并复杂度。

### 7.2 经典算法

#### 7.2.1 归并排序

**算法 7.2.1 (分治归并排序)**
```rust
pub fn merge_sort_divide_conquer<T: Ord + Clone>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let mid = arr.len() / 2;
    merge_sort_divide_conquer(&mut arr[..mid]);
    merge_sort_divide_conquer(&mut arr[mid..]);
    merge(arr, mid);
}
```

#### 7.2.2 快速排序

**算法 7.2.2 (分治快速排序)**
```rust
pub fn quick_sort_divide_conquer<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let pivot_index = partition(arr);
    quick_sort_divide_conquer(&mut arr[..pivot_index]);
    quick_sort_divide_conquer(&mut arr[pivot_index + 1..]);
}
```

### 7.3 并行分治

**并行分治特征：**
- 子问题之间相互独立
- 可以并行执行
- 合并操作需要同步

**并行复杂度：**
$$T_p(n) = T(n/p) + O(\log p)$$
其中 $p$ 是处理器数量。

---

## 8. 贪心算法

### 8.1 贪心原理

**定义 8.1.1 (贪心算法)**
贪心算法在每一步选择中都采取当前状态下最好或最优的选择。

**贪心特征：**
1. **贪心选择性质**：局部最优选择
2. **最优子结构**：问题的最优解包含子问题的最优解

**定理 8.1.1 (贪心正确性)**
如果问题具有贪心选择性质和最优子结构，则贪心算法能正确求解。

### 8.2 贪心选择

#### 8.2.1 活动选择问题

**算法 8.2.1 (活动选择)**
```rust
pub struct Activity {
    start: usize,
    finish: usize,
}

pub fn activity_selection(activities: &mut [Activity]) -> Vec<usize> {
    activities.sort_by_key(|a| a.finish);
    
    let mut selected = Vec::new();
    let mut last_finish = 0;
    
    for (i, activity) in activities.iter().enumerate() {
        if activity.start >= last_finish {
            selected.push(i);
            last_finish = activity.finish;
        }
    }
    
    selected
}
```

**贪心选择策略：**
选择结束时间最早的活动。

#### 8.2.2 Huffman 编码

**算法 8.2.2 (Huffman 编码)**
```rust
use std::collections::BinaryHeap;
use std::cmp::Reverse;

pub struct HuffmanNode {
    frequency: usize,
    left: Option<Box<HuffmanNode>>,
    right: Option<Box<HuffmanNode>>,
}

pub fn build_huffman_tree(frequencies: &[usize]) -> Option<Box<HuffmanNode>> {
    let mut heap: BinaryHeap<Reverse<Box<HuffmanNode>>> = frequencies
        .iter()
        .map(|&freq| Reverse(Box::new(HuffmanNode {
            frequency: freq,
            left: None,
            right: None,
        })))
        .collect();
    
    while heap.len() > 1 {
        let left = heap.pop().unwrap().0;
        let right = heap.pop().unwrap().0;
        
        let parent = Box::new(HuffmanNode {
            frequency: left.frequency + right.frequency,
            left: Some(left),
            right: Some(right),
        });
        
        heap.push(Reverse(parent));
    }
    
    heap.pop().map(|node| node.0)
}
```

### 8.3 最优性证明

**交换论证：**
通过证明任何最优解都可以通过有限次交换转换为贪心解来证明贪心算法的正确性。

---

## 9. 回溯算法

### 9.1 回溯原理

**定义 9.1.1 (回溯算法)**
回溯算法通过尝试所有可能的解来找到问题的解，当发现当前路径不能得到解时，回退到上一步。

**回溯特征：**
1. **状态空间树**：问题的解空间形成树结构
2. **深度优先搜索**：按深度优先顺序探索解空间
3. **剪枝**：提前终止不可能产生解的分支

### 9.2 状态空间搜索

#### 9.2.1 N 皇后问题

**算法 9.2.1 (N 皇后)**
```rust
pub fn solve_n_queens(n: usize) -> Vec<Vec<String>> {
    let mut board = vec![vec!['.'; n]; n];
    let mut solutions = Vec::new();
    
    backtrack_n_queens(&mut board, 0, &mut solutions);
    solutions
}

fn backtrack_n_queens(board: &mut Vec<Vec<char>>, row: usize, solutions: &mut Vec<Vec<String>>) {
    if row == board.len() {
        solutions.push(board.iter().map(|r| r.iter().collect()).collect());
        return;
    }
    
    for col in 0..board.len() {
        if is_valid_placement(board, row, col) {
            board[row][col] = 'Q';
            backtrack_n_queens(board, row + 1, solutions);
            board[row][col] = '.';
        }
    }
}

fn is_valid_placement(board: &[Vec<char>], row: usize, col: usize) -> bool {
    // 检查列
    for r in 0..row {
        if board[r][col] == 'Q' {
            return false;
        }
    }
    
    // 检查对角线
    for r in 0..row {
        let c1 = col as i32 - (row as i32 - r as i32);
        let c2 = col as i32 + (row as i32 - r as i32);
        
        if (c1 >= 0 && c1 < board.len() as i32 && board[r][c1 as usize] == 'Q') ||
           (c2 >= 0 && c2 < board.len() as i32 && board[r][c2 as usize] == 'Q') {
            return false;
        }
    }
    
    true
}
```

### 9.3 剪枝优化

**剪枝策略：**
1. **约束传播**：利用约束条件减少搜索空间
2. **启发式剪枝**：使用启发式函数指导搜索
3. **对称性剪枝**：利用问题的对称性避免重复搜索

---

## 10. 并行算法

### 10.1 并行模型

**定义 10.1.1 (并行计算模型)**
并行计算模型定义了并行算法的执行方式和复杂度分析。

**PRAM 模型：**
- 共享内存模型
- 处理器可以并行访问内存
- 分为 EREW、CREW、CRCW 等变体

**定理 10.1.1 (并行加速比)**
并行算法的加速比定义为：
$$S_p = \frac{T_1}{T_p}$$
其中 $T_1$ 是串行时间，$T_p$ 是并行时间。

### 10.2 并行排序

#### 10.2.1 并行归并排序

**算法 10.2.1 (并行归并排序)**
```rust
use rayon::prelude::*;

pub fn parallel_merge_sort<T: Ord + Send + Sync>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let mid = arr.len() / 2;
    let (left, right) = arr.split_at_mut(mid);
    
    rayon::join(
        || parallel_merge_sort(left),
        || parallel_merge_sort(right)
    );
    
    merge(arr, mid);
}
```

**并行复杂度：**
$$T_p(n) = O\left(\frac{n \log n}{p} + \log p\right)$$

### 10.3 并行搜索

#### 10.3.1 并行深度优先搜索

**算法 10.3.1 (并行 DFS)**
```rust
use rayon::prelude::*;

pub fn parallel_dfs(graph: &Graph, start: usize) -> Vec<usize> {
    let mut visited = vec![false; graph.adjacency_list.len()];
    let mut result = Vec::new();
    
    parallel_dfs_recursive(graph, start, &mut visited, &mut result);
    result
}

fn parallel_dfs_recursive(graph: &Graph, vertex: usize, visited: &mut [bool], result: &mut Vec<usize>) {
    visited[vertex] = true;
    result.push(vertex);
    
    if let Some(neighbors) = graph.get_neighbors(vertex) {
        let unvisited: Vec<usize> = neighbors.iter()
            .filter(|&&n| !visited[n])
            .cloned()
            .collect();
        
        unvisited.par_iter().for_each(|&neighbor| {
            parallel_dfs_recursive(graph, neighbor, visited, result);
        });
    }
}
```

---

## 总结

Rust 的算法与数据结构实现具有以下特点：

1. **内存安全**：所有权系统确保算法实现的安全性
2. **零成本抽象**：高级抽象不带来运行时开销
3. **类型安全**：类型系统防止算法实现错误
4. **并发支持**：内置的并发原语支持并行算法

通过形式化的理论框架，我们可以：
- 严格证明算法的正确性
- 分析算法的时间空间复杂度
- 设计高效的并行算法
- 指导算法的最佳实践

这个理论框架为 Rust 算法编程提供了坚实的数学基础，确保算法的正确性和效率。 