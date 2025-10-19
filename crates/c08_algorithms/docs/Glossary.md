# C08 算法: 术语表 (Glossary)

> **文档定位**: 算法核心术语快速参考，涵盖复杂度、数据结构、算法设计等关键概念  
> **使用方式**: 通过术语索引快速查找定义，理解算法核心概念  
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [README](./README.md) | [FAQ](./FAQ.md)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.75+  
**文档类型**: 📚 参考资料

---

## 📋 术语索引

[A](#算法-algorithm) | [B](#大o记号-big-o-notation) | [D](#动态规划-dynamic-programming) | [G](#贪心算法-greedy-algorithm) | [H](#哈希表-hash-table) | [T](#时间复杂度-time-complexity)

**快速跳转**:

- [C08 算法: 术语表 (Glossary)](#c08-算法-术语表-glossary)
  - [📋 术语索引](#-术语索引)
  - [术语详解](#术语详解)
    - [算法 (Algorithm)](#算法-algorithm)
    - [时间复杂度 (Time Complexity)](#时间复杂度-time-complexity)
    - [空间复杂度 (Space Complexity)](#空间复杂度-space-complexity)
    - [大O记号 (Big-O Notation)](#大o记号-big-o-notation)
    - [递归 (Recursion)](#递归-recursion)
    - [动态规划 (Dynamic Programming)](#动态规划-dynamic-programming)
    - [贪心算法 (Greedy Algorithm)](#贪心算法-greedy-algorithm)
    - [分治法 (Divide and Conquer)](#分治法-divide-and-conquer)
    - [回溯法 (Backtracking)](#回溯法-backtracking)
    - [哈希表 (Hash Table)](#哈希表-hash-table)
    - [二叉搜索树 (Binary Search Tree)](#二叉搜索树-binary-search-tree)
    - [图 (Graph)](#图-graph)
    - [堆 (Heap)](#堆-heap)
    - [单调栈 (Monotonic Stack)](#单调栈-monotonic-stack)
    - [前缀和 (Prefix Sum)](#前缀和-prefix-sum)
  - [📚 延伸阅读](#-延伸阅读)

---

## 术语详解

### 算法 (Algorithm)

**定义**: 解决特定问题的一系列明确指令或步骤。

**特征**:

- 输入: 零个或多个输入
- 输出: 至少一个输出
- 明确性: 每步清晰无歧义
- 有限性: 有限步骤内终止
- 有效性: 每步可执行

**Rust示例**:

```rust
// 欧几里得算法求最大公约数
fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}
```

**相关**: [algorithm_index](./algorithm_index.md)

---

### 时间复杂度 (Time Complexity)

**定义**: 算法执行所需的计算次数随输入规模增长的趋势。

**常见复杂度**:

- O(1) - 常数时间
- O(log n) - 对数时间
- O(n) - 线性时间
- O(n log n) - 线性对数时间
- O(n²) - 平方时间
- O(2ⁿ) - 指数时间

**相关**: [algorithm_complexity](./algorithm_complexity.md)

---

### 空间复杂度 (Space Complexity)

**定义**: 算法执行所需的额外内存空间随输入规模增长的趋势。

**示例**:

```rust
// O(1) 空间
fn sum(arr: &[i32]) -> i32 {
    arr.iter().sum()  // 只需常数空间
}

// O(n) 空间
fn reverse(arr: &[i32]) -> Vec<i32> {
    arr.iter().rev().copied().collect()  // 需要n空间
}
```

**相关**: [algorithm_complexity](./algorithm_complexity.md)

---

### 大O记号 (Big-O Notation)

**定义**: 描述算法复杂度上界的数学记号。

**含义**: f(n) = O(g(n)) 表示存在常数c和n₀，使得对所有n ≥ n₀，有 f(n) ≤ c·g(n)

**示例**:

```rust
// O(n²)
for i in 0..n {
    for j in 0..n {  // 嵌套循环
        // ...
    }
}

// O(log n)
let mut x = n;
while x > 1 {
    x /= 2;  // 每次减半
}
```

**相关**: [algorithm_complexity](./algorithm_complexity.md)

---

### 递归 (Recursion)

**定义**: 函数直接或间接调用自身的编程技术。

**要素**:

- 基本情况 (Base Case): 终止条件
- 递归情况 (Recursive Case): 自我调用

**示例**:

```rust
// 递归计算阶乘
fn factorial(n: u64) -> u64 {
    match n {
        0 | 1 => 1,              // 基本情况
        n => n * factorial(n-1)  // 递归情况
    }
}
```

**相关**: [ASYNC_RECURSION_ANALYSIS](./ASYNC_RECURSION_ANALYSIS.md)

---

### 动态规划 (Dynamic Programming)

**定义**: 通过将问题分解为子问题，并存储子问题的解来避免重复计算的算法设计方法。

**核心思想**:

- 重叠子问题
- 最优子结构
- 记忆化或制表法

**示例**:

```rust
// 动态规划求斐波那契数
fn fibonacci_dp(n: usize) -> u64 {
    if n <= 1 {
        return n as u64;
    }
    
    let mut dp = vec![0; n + 1];
    dp[1] = 1;
    
    for i in 2..=n {
        dp[i] = dp[i-1] + dp[i-2];
    }
    
    dp[n]
}
```

**经典问题**:

- 背包问题
- 最长公共子序列
- 最短路径

**相关**: [algorithm_exp系列](./algorithm_exp01.md)

---

### 贪心算法 (Greedy Algorithm)

**定义**: 每步都做出当前最优选择，期望导致全局最优解的算法策略。

**特点**:

- 局部最优
- 无后效性
- 不一定得到全局最优

**示例**:

```rust
// 找零钱问题（贪心）
fn coin_change_greedy(amount: u32, coins: &[u32]) -> Vec<u32> {
    let mut result = Vec::new();
    let mut remaining = amount;
    
    // coins应降序排列
    for &coin in coins {
        while remaining >= coin {
            result.push(coin);
            remaining -= coin;
        }
    }
    
    result
}
```

**经典问题**:

- 活动选择
- 霍夫曼编码
- 最小生成树 (Prim/Kruskal)

**相关**: [algorithm_index](./algorithm_index.md)

---

### 分治法 (Divide and Conquer)

**定义**: 将问题分解为更小的子问题，递归解决子问题，然后合并结果的算法策略。

**步骤**:

1. 分解 (Divide): 分成子问题
2. 解决 (Conquer): 递归解决
3. 合并 (Combine): 合并结果

**示例**:

```rust
// 归并排序
fn merge_sort<T: Ord + Clone>(arr: &mut [T]) {
    let len = arr.len();
    if len <= 1 {
        return;
    }
    
    let mid = len / 2;
    
    // 分解
    merge_sort(&mut arr[..mid]);
    merge_sort(&mut arr[mid..]);
    
    // 合并
    let mut temp = arr.to_vec();
    merge(&arr[..mid], &arr[mid..], &mut temp);
    arr.copy_from_slice(&temp);
}

fn merge<T: Ord>(left: &[T], right: &[T], result: &mut [T]) {
    // 合并逻辑
}
```

**经典算法**:

- 归并排序
- 快速排序
- 二分查找

**相关**: [algorithm_index](./algorithm_index.md)

---

### 回溯法 (Backtracking)

**定义**: 通过试探性地构建解决方案，当发现当前路径无法得到有效解时回退到上一步的算法策略。

**核心思想**:

- 深度优先搜索
- 剪枝优化
- 撤销选择

**示例**:

```rust
// N皇后问题
fn solve_n_queens(n: usize) -> Vec<Vec<String>> {
    let mut result = Vec::new();
    let mut board = vec![vec!['.'; n]; n];
    backtrack(0, &mut board, &mut result);
    result
}

fn backtrack(row: usize, board: &mut Vec<Vec<char>>, result: &mut Vec<Vec<String>>) {
    if row == board.len() {
        // 找到一个解
        result.push(board.iter().map(|r| r.iter().collect()).collect());
        return;
    }
    
    for col in 0..board.len() {
        if is_valid(board, row, col) {
            board[row][col] = 'Q';           // 选择
            backtrack(row + 1, board, result); // 递归
            board[row][col] = '.';           // 撤销
        }
    }
}

fn is_valid(board: &[Vec<char>], row: usize, col: usize) -> bool {
    // 检查是否有效
    true
}
```

**经典问题**:

- N皇后
- 数独
- 全排列

**相关**: [algorithm_index](./algorithm_index.md)

---

### 哈希表 (Hash Table)

**定义**: 通过哈希函数将键映射到数组索引，实现O(1)平均时间复杂度的查找、插入和删除的数据结构。

**Rust中的实现**: `HashMap`, `HashSet`

**示例**:

```rust
use std::collections::HashMap;

let mut map = HashMap::new();
map.insert("key", "value");  // O(1)
map.get("key");              // O(1)
map.remove("key");           // O(1)
```

**冲突解决**:

- 链地址法 (Chaining)
- 开放寻址 (Open Addressing)

**相关**: [data_structures](./data_structures.md)

---

### 二叉搜索树 (Binary Search Tree)

**定义**: 每个节点最多有两个子节点，且左子树所有节点值小于根节点，右子树所有节点值大于根节点的树结构。

**性质**:

- 中序遍历得到有序序列
- 查找、插入、删除: O(log n) 平均，O(n) 最坏

**Rust示例**:

```rust
struct TreeNode<T> {
    val: T,
    left: Option<Box<TreeNode<T>>>,
    right: Option<Box<TreeNode<T>>>,
}

impl<T: Ord> TreeNode<T> {
    fn search(&self, target: &T) -> bool {
        match target.cmp(&self.val) {
            std::cmp::Ordering::Equal => true,
            std::cmp::Ordering::Less => {
                self.left.as_ref().map_or(false, |n| n.search(target))
            }
            std::cmp::Ordering::Greater => {
                self.right.as_ref().map_or(false, |n| n.search(target))
            }
        }
    }
}
```

**变种**:

- AVL树 (平衡)
- 红黑树 (BTreeMap内部实现)
- B树/B+树

**相关**: [data_structures](./data_structures.md)

---

### 图 (Graph)

**定义**: 由顶点(Vertex)和边(Edge)组成的非线性数据结构。

**类型**:

- 有向图/无向图
- 加权图/无权图
- 连通图/非连通图

**表示方法**:

```rust
// 邻接表
use std::collections::HashMap;
type Graph = HashMap<usize, Vec<usize>>;

// 邻接矩阵
type AdjMatrix = Vec<Vec<bool>>;
```

**经典算法**:

- DFS (深度优先搜索)
- BFS (广度优先搜索)
- Dijkstra (最短路径)
- Floyd-Warshall (全源最短路径)
- Kruskal/Prim (最小生成树)

**相关**: [algorithm_index](./algorithm_index.md)

---

### 堆 (Heap)

**定义**: 完全二叉树，每个节点的值都大于等于(最大堆)或小于等于(最小堆)其子节点。

**Rust中的实现**: `BinaryHeap` (最大堆)

**操作**:

```rust
use std::collections::BinaryHeap;

let mut heap = BinaryHeap::new();
heap.push(3);      // O(log n)
heap.push(1);
heap.push(2);
heap.pop();        // O(log n) 返回最大值3
heap.peek();       // O(1) 查看最大值
```

**应用**:

- 优先队列
- 堆排序
- Top K问题

**相关**: [data_structures](./data_structures.md)

---

### 单调栈 (Monotonic Stack)

**定义**: 栈内元素保持单调递增或递减的特殊栈结构。

**应用**: 寻找下一个更大/更小元素

**示例**:

```rust
// 寻找每个元素右侧第一个更大的元素
fn next_greater_elements(nums: Vec<i32>) -> Vec<i32> {
    let n = nums.len();
    let mut result = vec![-1; n];
    let mut stack = Vec::new();
    
    for i in 0..n {
        while !stack.is_empty() && nums[*stack.last().unwrap()] < nums[i] {
            let j = stack.pop().unwrap();
            result[j] = nums[i];
        }
        stack.push(i);
    }
    
    result
}
```

**相关**: [data_structures](./data_structures.md)

---

### 前缀和 (Prefix Sum)

**定义**: 数组前i个元素的和，用于快速计算区间和。

**实现**:

```rust
struct PrefixSum {
    prefix: Vec<i32>,
}

impl PrefixSum {
    fn new(arr: &[i32]) -> Self {
        let mut prefix = vec![0; arr.len() + 1];
        for i in 0..arr.len() {
            prefix[i + 1] = prefix[i] + arr[i];
        }
        Self { prefix }
    }
    
    // 查询区间[l, r]的和: O(1)
    fn range_sum(&self, l: usize, r: usize) -> i32 {
        self.prefix[r + 1] - self.prefix[l]
    }
}
```

**应用**: 区间查询

**相关**: [data_structures](./data_structures.md)

---

## 📚 延伸阅读

- [主索引](./00_MASTER_INDEX.md) - 完整文档导航
- [FAQ](./FAQ.md) - 常见问题解答
- [algorithm_index](./algorithm_index.md) - 算法索引
- [algorithm_complexity](./algorithm_complexity.md) - 复杂度分析
- [data_structures](./data_structures.md) - 数据结构详解
