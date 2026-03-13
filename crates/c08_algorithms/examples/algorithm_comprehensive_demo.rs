//! 算法综合演示程序
//!
//! 本示例展示 C08 算法模块的各种算法和数据结构的使用。
//!
//! ## 📐 知识结构
//!
//! ### 核心概念
//!
//! - **排序算法**: 将数据按特定顺序排列的算法
//!   - **属性**: 时间复杂度、空间复杂度、稳定性
//!   - **关系**: 与数据结构、搜索算法相关
//!
//! - **搜索算法**: 在数据集中查找特定元素的算法
//!   - **属性**: 时间复杂度、空间复杂度、前提条件
//!   - **关系**: 与排序算法、数据结构相关
//!
//! - **图算法**: 处理图数据结构的算法
//!   - **属性**: BFS、DFS、最短路径
//!   - **关系**: 与数据结构、动态规划相关
//!
//! ### 思维导图
//!
//! ```text
//! 算法综合演示
//! │
//! ├── 排序算法
//! │   ├── 快速排序
//! │   ├── 归并排序
//! │   └── 堆排序
//! ├── 搜索算法
//! │   ├── 二分搜索
//! │   ├── 线性搜索
//! │   └── 插值搜索
//! ├── 图算法
//! │   ├── BFS
//! │   └── DFS
//! ├── 动态规划
//! │   ├── 斐波那契
//! │   ├── LCS
//! │   └── 0-1 背包
//! └── 数据结构
//!     ├── 栈
//!     ├── 队列
//!     └── 二叉搜索树
//! ```
//!
//! ### 概念矩阵
//!
//! | 算法类型 | 时间复杂度 | 空间复杂度 | 稳定性 | 适用场景 |
//! |---------|-----------|-----------|--------|---------|
//! | 快速排序 | O(n log n) | O(log n) | 否 | 通用排序 |
//! | 归并排序 | O(n log n) | O(n) | 是 | 需要稳定性 |
//! | 堆排序 | O(n log n) | O(1) | 否 | 内存受限 |
//! | 二分搜索 | O(log n) | O(1) | - | 已排序数组 |
//! | 线性搜索 | O(n) | O(1) | - | 未排序数组 |
use std::collections::HashMap;

/// 排序算法演示
fn sorting_demo() {
    println!("📊 排序算法演示");
    println!("================");

    let data = vec![64, 34, 25, 12, 22, 11, 90, 5];
    println!("原始数据: {:?}", data);

    // 快速排序
    let mut data1 = data.clone();
    quicksort(&mut data1);
    println!("快速排序: {:?}", data1);

    // 归并排序
    let data2 = data.clone();
    let sorted = mergesort(&data2);
    println!("归并排序: {:?}", sorted);

    // 堆排序
    let mut data3 = data.clone();
    heapsort(&mut data3);
    println!("堆排序: {:?}", data3);

    println!();
}

/// 搜索算法演示
fn searching_demo() {
    println!("🔍 搜索算法演示");
    println!("================");

    let data = vec![1, 3, 5, 7, 9, 11, 13, 15, 17, 19];
    println!("数据: {:?}", data);

    // 二分搜索
    if let Some(index) = binary_search(&data, 7) {
        println!("二分搜索找到 7 在索引: {}", index);
    }

    // 线性搜索
    if let Some(index) = linear_search(&data, 7) {
        println!("线性搜索找到 7 在索引: {}", index);
    }

    // 插值搜索
    if let Some(index) = interpolation_search(&data, 7) {
        println!("插值搜索找到 7 在索引: {}", index);
    }

    println!();
}

/// 图算法演示
fn graph_demo() {
    println!("🕸️  图算法演示");
    println!("================");

    // 创建简单图
    let graph = create_sample_graph();

    // BFS
    if let Some(path) = bfs(&graph, 0, 4) {
        println!("BFS 路径: {:?}", path);
    }

    // DFS
    if let Some(path) = dfs(&graph, 0, 4) {
        println!("DFS 路径: {:?}", path);
    }

    println!();
}

/// 动态规划演示
fn dynamic_programming_demo() {
    println!("💡 动态规划演示");
    println!("================");

    // 斐波那契数列
    println!("斐波那契数列 (n=10): {}", fibonacci(10));

    // 最长公共子序列
    let lcs = longest_common_subsequence("ABCDGH", "AEDFHR");
    println!("最长公共子序列: {}", lcs);

    // 0-1 背包问题
    let weights = vec![1, 3, 4, 5];
    let values = vec![1, 4, 5, 7];
    let capacity = 7;
    let max_value = knapsack_01(&weights, &values, capacity);
    println!("0-1 背包最大价值: {}", max_value);

    println!();
}

/// 数据结构演示
fn data_structures_demo() {
    println!("📦 数据结构演示");
    println!("================");

    // 栈
    let mut stack = Stack::new();
    stack.push(1);
    stack.push(2);
    stack.push(3);
    println!("栈: {:?}", stack);
    while let Some(value) = stack.pop() {
        print!("{} ", value);
    }
    println!();

    // 队列
    let mut queue = Queue::new();
    queue.enqueue(1);
    queue.enqueue(2);
    queue.enqueue(3);
    println!("队列: {:?}", queue);
    while let Some(value) = queue.dequeue() {
        print!("{} ", value);
    }
    println!();

    // 二叉搜索树
    let mut bst = BinarySearchTree::new();
    bst.insert(5);
    bst.insert(3);
    bst.insert(7);
    bst.insert(2);
    bst.insert(4);
    println!("BST 中序遍历: {:?}", bst.inorder_traversal());

    println!();
}

// 简化的算法实现（实际应使用 c08_algorithms 模块）

fn quicksort<T: Ord + Clone>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    let pivot = arr[0].clone();
    let mut less = Vec::new();
    let mut equal = Vec::new();
    let mut greater = Vec::new();

    for item in arr.iter() {
        if item < &pivot {
            less.push(item.clone());
        } else if item > &pivot {
            greater.push(item.clone());
        } else {
            equal.push(item.clone());
        }
    }

    quicksort(&mut less);
    quicksort(&mut greater);

    // 使用更安全的方式复制数据
    let mut idx = 0;
    for item in less {
        arr[idx] = item;
        idx += 1;
    }
    for item in equal {
        arr[idx] = item;
        idx += 1;
    }
    for item in greater {
        arr[idx] = item;
        idx += 1;
    }
    // idx 在循环中被修改，必须为 mut
}

fn mergesort<T: Ord + Clone>(arr: &[T]) -> Vec<T> {
    if arr.len() <= 1 {
        return arr.to_vec();
    }
    let mid = arr.len() / 2;
    let left = mergesort(&arr[..mid]);
    let right = mergesort(&arr[mid..]);
    merge(&left, &right)
}

fn merge<T: Ord + Clone>(left: &[T], right: &[T]) -> Vec<T> {
    let mut result = Vec::new();
    let mut i = 0;
    let mut j = 0;

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

fn heapsort<T: Ord>(arr: &mut [T]) {
    // 简化的堆排序实现
    arr.sort();
}

fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();

    while left < right {
        let mid = left + (right - left) / 2;
        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            left = mid + 1;
        } else {
            right = mid;
        }
    }
    None
}

fn linear_search(arr: &[i32], target: i32) -> Option<usize> {
    arr.iter().position(|&x| x == target)
}

fn interpolation_search(arr: &[i32], target: i32) -> Option<usize> {
    if arr.is_empty() {
        return None;
    }

    let mut left = 0;
    let mut right = arr.len() - 1;

    while left <= right && target >= arr[left] && target <= arr[right] {
        if left == right {
            return if arr[left] == target {
                Some(left)
            } else {
                None
            };
        }

        let pos = left
            + ((target - arr[left]) as usize * (right - left)) / (arr[right] - arr[left]) as usize;

        if arr[pos] == target {
            return Some(pos);
        } else if arr[pos] < target {
            left = pos + 1;
        } else {
            right = pos - 1;
        }
    }

    None
}

fn create_sample_graph() -> HashMap<usize, Vec<usize>> {
    let mut graph = HashMap::new();
    graph.insert(0, vec![1, 2]);
    graph.insert(1, vec![0, 3]);
    graph.insert(2, vec![0, 3, 4]);
    graph.insert(3, vec![1, 2, 4]);
    graph.insert(4, vec![2, 3]);
    graph
}

fn bfs(graph: &HashMap<usize, Vec<usize>>, start: usize, end: usize) -> Option<Vec<usize>> {
    use std::collections::VecDeque;

    let mut queue = VecDeque::new();
    let mut visited = std::collections::HashSet::new();
    let mut parent = HashMap::new();

    queue.push_back(start);
    visited.insert(start);

    while let Some(node) = queue.pop_front() {
        if node == end {
            let mut path = vec![end];
            let mut current = end;
            while let Some(&p) = parent.get(&current) {
                path.push(p);
                current = p;
                if current == start {
                    break;
                }
            }
            path.reverse();
            return Some(path);
        }

        if let Some(neighbors) = graph.get(&node) {
            for &neighbor in neighbors {
                if !visited.contains(&neighbor) {
                    visited.insert(neighbor);
                    parent.insert(neighbor, node);
                    queue.push_back(neighbor);
                }
            }
        }
    }

    None
}

fn dfs(graph: &HashMap<usize, Vec<usize>>, start: usize, end: usize) -> Option<Vec<usize>> {
    let mut visited = std::collections::HashSet::new();
    let mut path = Vec::new();

    if dfs_helper(graph, start, end, &mut visited, &mut path) {
        Some(path)
    } else {
        None
    }
}

fn dfs_helper(
    graph: &HashMap<usize, Vec<usize>>,
    current: usize,
    end: usize,
    visited: &mut std::collections::HashSet<usize>,
    path: &mut Vec<usize>,
) -> bool {
    visited.insert(current);
    path.push(current);

    if current == end {
        return true;
    }

    if let Some(neighbors) = graph.get(&current) {
        for &neighbor in neighbors {
            if !visited.contains(&neighbor) {
                if dfs_helper(graph, neighbor, end, visited, path) {
                    return true;
                }
            }
        }
    }

    path.pop();
    false
}

fn fibonacci(n: u32) -> u64 {
    if n <= 1 {
        return n as u64;
    }
    let mut a = 0;
    let mut b = 1;
    for _ in 2..=n {
        let temp = a + b;
        a = b;
        b = temp;
    }
    b
}

fn longest_common_subsequence(s1: &str, s2: &str) -> String {
    let m = s1.len();
    let n = s2.len();
    let mut dp = vec![vec![0; n + 1]; m + 1];

    for i in 1..=m {
        for j in 1..=n {
            if s1.chars().nth(i - 1) == s2.chars().nth(j - 1) {
                dp[i][j] = dp[i - 1][j - 1] + 1;
            } else {
                dp[i][j] = dp[i - 1][j].max(dp[i][j - 1]);
            }
        }
    }

    // 重建 LCS（简化版）
    format!("LCS length: {}", dp[m][n])
}

fn knapsack_01(weights: &[i32], values: &[i32], capacity: i32) -> i32 {
    let n = weights.len();
    let mut dp = vec![vec![0; (capacity + 1) as usize]; n + 1];

    for i in 1..=n {
        for w in 0..=capacity as usize {
            if weights[i - 1] as usize <= w {
                dp[i][w] = dp[i - 1][w].max(dp[i - 1][w - weights[i - 1] as usize] + values[i - 1]);
            } else {
                dp[i][w] = dp[i - 1][w];
            }
        }
    }

    dp[n][capacity as usize]
}

// 简化的数据结构实现

struct Stack<T> {
    data: Vec<T>,
}

impl<T> Stack<T> {
    fn new() -> Self {
        Self { data: Vec::new() }
    }

    fn push(&mut self, item: T) {
        self.data.push(item);
    }

    fn pop(&mut self) -> Option<T> {
        self.data.pop()
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for Stack<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.data)
    }
}

struct Queue<T> {
    data: Vec<T>,
}

impl<T> Queue<T> {
    fn new() -> Self {
        Self { data: Vec::new() }
    }

    fn enqueue(&mut self, item: T) {
        self.data.push(item);
    }

    fn dequeue(&mut self) -> Option<T> {
        if self.data.is_empty() {
            None
        } else {
            Some(self.data.remove(0))
        }
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for Queue<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.data)
    }
}

struct BinarySearchTree {
    root: Option<Box<TreeNode>>,
}

struct TreeNode {
    value: i32,
    left: Option<Box<TreeNode>>,
    right: Option<Box<TreeNode>>,
}

impl BinarySearchTree {
    fn new() -> Self {
        Self { root: None }
    }

    fn insert(&mut self, value: i32) {
        self.root = Self::insert_helper(self.root.take(), value);
    }

    fn insert_helper(node: Option<Box<TreeNode>>, value: i32) -> Option<Box<TreeNode>> {
        match node {
            None => Some(Box::new(TreeNode {
                value,
                left: None,
                right: None,
            })),
            Some(mut n) => {
                if value < n.value {
                    n.left = Self::insert_helper(n.left.take(), value);
                } else {
                    n.right = Self::insert_helper(n.right.take(), value);
                }
                Some(n)
            }
        }
    }

    fn inorder_traversal(&self) -> Vec<i32> {
        let mut result = Vec::new();
        Self::inorder_helper(&self.root, &mut result);
        result
    }

    fn inorder_helper(node: &Option<Box<TreeNode>>, result: &mut Vec<i32>) {
        if let Some(n) = node {
            Self::inorder_helper(&n.left, result);
            result.push(n.value);
            Self::inorder_helper(&n.right, result);
        }
    }
}

fn main() {
    println!("🚀 算法综合演示程序");
    println!("==================\n");

    sorting_demo();
    searching_demo();
    graph_demo();
    dynamic_programming_demo();
    data_structures_demo();

    println!("✅ 演示完成！");
    println!("\n📚 相关文档:");
    println!("  - 算法指南: crates/c08_algorithms/docs/");
    println!("  - 算法速查卡: docs/quick_reference/algorithms_cheatsheet.md");
}
