//! # 异步递归综合示例
//!
//! 本示例展示4种异步递归实现模式及其应用：
//! 1. Box + Pin 手动封装
//! 2. async-recursion 宏
//! 3. 尾递归优化
//! 4. Stream/Iterator转换
//!
//! 对标：Rust 1.90 / Edition 2024

use std::future::Future;
use std::pin::Pin;
use futures::stream::{self, Stream, StreamExt};
use tokio::sync::mpsc;

/// ============================================================================
/// 模式1: Box + Pin 手动封装
/// ============================================================================

/// ## 异步归并排序（Box + Pin）
///
/// ### 递归关系
/// ```text
/// T(n) = 2T(n/2) + Θ(n)
/// 通过主定理: T(n) = Θ(n log n)
/// ```
///
/// ### 实现要点
/// - 使用 `Pin<Box<dyn Future>>` 间接引用
/// - 并行递归：`tokio::join!` 同时处理左右子数组
/// - 堆分配开销：每次递归 O(1) 分配
pub fn merge_sort_async_boxed(
    data: Vec<i32>,
) -> Pin<Box<dyn Future<Output = Vec<i32>> + Send>> {
    Box::pin(async move {
        // 基础情况
        if data.len() <= 1 {
            return data;
        }

        let mid = data.len() / 2;
        let (left, right) = data.split_at(mid);

        // 并行递归（关键优势）
        let (left_sorted, right_sorted) = tokio::join!(
            merge_sort_async_boxed(left.to_vec()),
            merge_sort_async_boxed(right.to_vec())
        );

        merge(left_sorted, right_sorted)
    })
}

/// 归并两个有序数组
fn merge(left: Vec<i32>, right: Vec<i32>) -> Vec<i32> {
    let mut result = Vec::with_capacity(left.len() + right.len());
    let mut i = 0;
    let mut j = 0;

    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            result.push(left[i]);
            i += 1;
        } else {
            result.push(right[j]);
            j += 1;
        }
    }

    result.extend_from_slice(&left[i..]);
    result.extend_from_slice(&right[j..]);
    result
}

/// ## 异步二分查找（Box + Pin）
///
/// ### 复杂度
/// ```text
/// 时间：O(log n)
/// 空间：O(log n) 堆分配（每次递归）
/// ```
pub fn binary_search_async<T>(
    arr: Vec<T>,
    target: T,
) -> Pin<Box<dyn Future<Output = Option<usize>> + Send>>
where
    T: Ord + Clone + Send + 'static,
{
    Box::pin(async move {
        if arr.is_empty() {
            return None;
        }

        let mid = arr.len() / 2;
        match arr[mid].cmp(&target) {
            std::cmp::Ordering::Equal => Some(mid),
            std::cmp::Ordering::Less => {
                let right = arr[mid + 1..].to_vec();
                binary_search_async(right, target)
                    .await
                    .map(|idx| idx + mid + 1)
            }
            std::cmp::Ordering::Greater => {
                let left = arr[..mid].to_vec();
                binary_search_async(left, target).await
            }
        }
    })
}

/// ============================================================================
/// 模式2: async-recursion 宏（需要 async-recursion crate）
/// ============================================================================

/// ## 异步快速排序（宏版本）
///
/// ### 使用 async-recursion
/// ```rust
/// use async_recursion::async_recursion;
///
/// #[async_recursion]
/// async fn quick_sort_async_macro(data: Vec<i32>) -> Vec<i32> {
///     if data.len() <= 1 {
///         return data;
///     }
///
///     let pivot = data[data.len() - 1];
///     let (mut left, mut right): (Vec<_>, Vec<_>) = data[..data.len() - 1]
///         .iter()
///         .partition(|&&x| x < pivot);
///
///     // 并行递归
///     let (left_sorted, right_sorted) = tokio::join!(
///         quick_sort_async_macro(left.iter().copied().collect()),
///         quick_sort_async_macro(right.iter().copied().collect())
///     );
///
///     let mut result = left_sorted;
///     result.push(pivot);
///     result.extend(right_sorted);
///     result
/// }
/// ```
///
/// ### 优点
/// - 语法简洁，无需手动 Box
/// - 宏自动处理 Pin 封装
/// - 性能与手动 Box 相当

/// ## 异步斐波那契（记忆化）
///
/// ### 使用共享状态缓存
/// ```text
/// 优化策略：
/// 1. 先检查缓存，避免重复计算
/// 2. 使用并行计算 tokio::join!
/// 3. 结果写入缓存供后续使用
///
/// 时间复杂度：O(n) 有缓存
/// 空间复杂度：O(n) 缓存存储
/// ```
pub fn fibonacci_memo_async(
    n: u64,
    cache: std::sync::Arc<tokio::sync::Mutex<std::collections::HashMap<u64, u64>>>,
) -> Pin<Box<dyn Future<Output = u64> + Send>> {
    Box::pin(async move {
        // 检查缓存
        {
            let cache_guard = cache.lock().await;
            if let Some(&result) = cache_guard.get(&n) {
                return result;
            }
        }

        // 基础情况
        if n <= 1 {
            let mut cache_guard = cache.lock().await;
            cache_guard.insert(n, n);
            return n;
        }

        // 递归计算（并行）
        let (a, b) = tokio::join!(
            fibonacci_memo_async(n - 1, cache.clone()),
            fibonacci_memo_async(n - 2, cache.clone())
        );

        let result = a + b;

        // 存入缓存
        {
            let mut cache_guard = cache.lock().await;
            cache_guard.insert(n, result);
        }

        result
    })
}

/// ## 异步斐波那契（动态规划优化版）
///
/// ### 迭代实现，避免递归开销
pub async fn fibonacci_dp_async(n: u64) -> u64 {
    if n <= 1 {
        return n;
    }

    let mut dp = vec![0; (n + 1) as usize];
    dp[1] = 1;

    for i in 2..=n as usize {
        dp[i] = dp[i - 1] + dp[i - 2];

        // 每10步yield一次
        if i % 10 == 0 {
            tokio::task::yield_now().await;
        }
    }

    dp[n as usize]
}

/// ============================================================================
/// 模式3: 尾递归优化
/// ============================================================================

/// ## 尾递归阶乘（可转换为迭代）
///
/// ### 尾递归定义
/// ```text
/// 尾递归：递归调用是函数体最后一个操作
/// 好处：编译器可优化为循环，节省栈空间
/// ```
pub fn factorial_tail_async(
    n: u64,
    acc: u64,
) -> Pin<Box<dyn Future<Output = u64> + Send>> {
    Box::pin(async move {
        if n == 0 {
            acc
        } else {
            factorial_tail_async(n - 1, n * acc).await
        }
    })
}

/// ## 迭代版本（推荐）
///
/// ### 优势
/// - 无递归开销
/// - 空间复杂度 O(1)
/// - 可定期 yield 避免阻塞
pub async fn factorial_iter(n: u64) -> u64 {
    let mut acc = 1;
    for i in 1..=n {
        acc *= i;
        // 每100次迭代yield一次，避免阻塞事件循环
        if i % 100 == 0 {
            tokio::task::yield_now().await;
        }
    }
    acc
}

/// ## 尾递归求和
pub fn sum_tail_async(
    arr: Vec<i32>,
    acc: i32,
) -> Pin<Box<dyn Future<Output = i32> + Send>> {
    Box::pin(async move {
        if arr.is_empty() {
            acc
        } else {
            let new_acc = acc + arr[0];
            sum_tail_async(arr[1..].to_vec(), new_acc).await
        }
    })
}

/// ============================================================================
/// 模式4: Stream/Iterator 转换
/// ============================================================================

/// ## 斐波那契 Stream
///
/// ### 使用 unfold 实现惰性生成
/// ```text
/// unfold(初始状态, |状态| async { 计算下一个值 })
/// ```
pub fn fibonacci_stream(n: u64) -> Pin<Box<dyn Stream<Item = u64> + Send>> {
    Box::pin(stream::unfold((0, 1, 0), move |(a, b, count)| async move {
        if count >= n {
            None
        } else {
            Some((a, (b, a + b, count + 1)))
        }
    }))
}

/// ## 异步树遍历 Stream
///
/// ### 深度优先遍历二叉树
#[derive(Debug, Clone)]
pub struct TreeNode {
    pub value: i32,
    pub left: Option<Box<TreeNode>>,
    pub right: Option<Box<TreeNode>>,
}

impl TreeNode {
    pub fn new(value: i32) -> Self {
        TreeNode {
            value,
            left: None,
            right: None,
        }
    }

    pub fn with_children(
        value: i32,
        left: Option<Box<TreeNode>>,
        right: Option<Box<TreeNode>>,
    ) -> Self {
        TreeNode { value, left, right }
    }
}

/// DFS遍历（先序）
pub fn dfs_stream(root: Option<Box<TreeNode>>) -> Pin<Box<dyn Stream<Item = i32> + Send>> {
    Box::pin(stream::unfold(vec![root], |mut stack| async move {
        while let Some(node_opt) = stack.pop() {
            if let Some(node) = node_opt {
                // 先右后左（因为栈是后进先出）
                if let Some(right) = node.right {
                    stack.push(Some(right));
                }
                if let Some(left) = node.left {
                    stack.push(Some(left));
                }

                return Some((node.value, stack));
            }
        }
        None
    }))
}

/// ## 并发 Channel Stream
///
/// ### 使用 channel 实现生产者-消费者
pub fn producer_stream(count: usize) -> mpsc::Receiver<i32> {
    let (tx, rx) = mpsc::channel(100);

    tokio::spawn(async move {
        for i in 0..count {
            if tx.send(i as i32).await.is_err() {
                break;
            }
            tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        }
    });

    rx
}

/// ============================================================================
/// 算法应用示例
/// ============================================================================

/// ## 异步动态规划：最长公共子序列
///
/// ### 递归关系
/// ```text
/// LCS[i][j] =
///   if i = 0 or j = 0: 0
///   else if X[i] = Y[j]: LCS[i-1][j-1] + 1
///   else: max(LCS[i-1][j], LCS[i][j-1])
/// ```
pub async fn lcs_async(x: Vec<char>, y: Vec<char>) -> usize {
    let m = x.len();
    let n = y.len();

    // 使用二维数组缓存
    let mut dp = vec![vec![0; n + 1]; m + 1];

    for i in 1..=m {
        for j in 1..=n {
            dp[i][j] = if x[i - 1] == y[j - 1] {
                dp[i - 1][j - 1] + 1
            } else {
                dp[i - 1][j].max(dp[i][j - 1])
            };

            // 定期yield
            if (i * j) % 100 == 0 {
                tokio::task::yield_now().await;
            }
        }
    }

    dp[m][n]
}

/// ## 异步回溯：N皇后问题
///
/// ### 回溯框架
pub fn n_queens_async(n: usize) -> Pin<Box<dyn Future<Output = Vec<Vec<usize>>> + Send>> {
    Box::pin(async move {
        let mut solutions = Vec::new();
        let mut board = Vec::new();
        backtrack_queens(n, &mut board, &mut solutions).await;
        solutions
    })
}

fn backtrack_queens<'a>(
    n: usize,
    board: &'a mut Vec<usize>,
    solutions: &'a mut Vec<Vec<usize>>,
) -> Pin<Box<dyn Future<Output = ()> + Send + 'a>> {
    Box::pin(async move {
        if board.len() == n {
            solutions.push(board.clone());
            return;
        }

        for col in 0..n {
            if is_valid_queen(board, col) {
                board.push(col);
                backtrack_queens(n, board, solutions).await;
                board.pop();

                // 定期yield
                tokio::task::yield_now().await;
            }
        }
    })
}

fn is_valid_queen(board: &[usize], col: usize) -> bool {
    let row = board.len();
    for (r, &c) in board.iter().enumerate() {
        if c == col || (row as i32 - r as i32).abs() == (col as i32 - c as i32).abs() {
            return false;
        }
    }
    true
}

/// ============================================================================
/// 主函数：演示所有模式
/// ============================================================================

#[tokio::main]
async fn main() {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║              异步递归综合示例                                ║");
    println!("║              Rust 1.90 / Edition 2024                         ║");
    println!("╚══════════════════════════════════════════════════════════════╝");

    // 模式1: Box + Pin
    println!("\n【模式1】Box + Pin 手动封装");
    println!("{}", "─".repeat(60));

    let data = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5];
    println!("原始数据: {:?}", data);
    let sorted = merge_sort_async_boxed(data).await;
    println!("归并排序: {:?}", sorted);

    let arr = vec![1, 3, 5, 7, 9, 11, 13, 15];
    let target = 7;
    match binary_search_async(arr.clone(), target).await {
        Some(idx) => println!("二分查找 {}: 找到，索引={}", target, idx),
        None => println!("二分查找 {}: 未找到", target),
    }

    // 模式2: 记忆化斐波那契
    println!("\n【模式2】异步斐波那契（记忆化 & 动态规划）");
    println!("{}", "─".repeat(60));

    let cache = std::sync::Arc::new(tokio::sync::Mutex::new(std::collections::HashMap::new()));
    let n = 20;
    let result_memo = fibonacci_memo_async(n, cache).await;
    let result_dp = fibonacci_dp_async(n).await;
    println!("F({}) [记忆化] = {}", n, result_memo);
    println!("F({}) [动态规划] = {}", n, result_dp);

    // 模式3: 尾递归
    println!("\n【模式3】尾递归优化");
    println!("{}", "─".repeat(60));

    let n = 10;
    let result_tail = factorial_tail_async(n, 1).await;
    let result_iter = factorial_iter(n).await;
    println!("阶乘 {}! (尾递归) = {}", n, result_tail);
    println!("阶乘 {}! (迭代)   = {}", n, result_iter);

    // 模式4: Stream
    println!("\n【模式4】Stream/Iterator");
    println!("{}", "─".repeat(60));

    print!("斐波那契前10项: ");
    let mut stream = fibonacci_stream(10);
    let mut fib_values = Vec::new();
    while let Some(val) = stream.next().await {
        fib_values.push(val);
    }
    println!("{:?}", fib_values);

    // 树遍历
    let tree = Some(Box::new(TreeNode::with_children(
        1,
        Some(Box::new(TreeNode::with_children(
            2,
            Some(Box::new(TreeNode::new(4))),
            Some(Box::new(TreeNode::new(5))),
        ))),
        Some(Box::new(TreeNode::new(3))),
    )));

    print!("树DFS遍历: ");
    let mut dfs = dfs_stream(tree);
    let mut dfs_values = Vec::new();
    while let Some(val) = dfs.next().await {
        dfs_values.push(val);
    }
    println!("{:?}", dfs_values);

    // 算法应用
    println!("\n【算法应用】");
    println!("{}", "─".repeat(60));

    let x = "ABCBDAB".chars().collect();
    let y = "BDCABA".chars().collect();
    let lcs_len = lcs_async(x, y).await;
    println!("LCS长度: {}", lcs_len);

    let n = 4;
    let solutions = n_queens_async(n).await;
    println!("{}皇后问题: {}个解", n, solutions.len());

    // 总结
    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║                           总结                                ║");
    println!("╠══════════════════════════════════════════════════════════════╣");
    println!("║ ✓ 模式1（Box+Pin）: 通用，手动控制                           ║");
    println!("║ ✓ 模式2（async-recursion）: 简洁，宏自动处理                ║");
    println!("║ ✓ 模式3（尾递归）: 可优化为迭代                              ║");
    println!("║ ✓ 模式4（Stream）: 惰性求值，内存友好                        ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
}

/// ============================================================================
/// 测试模块
/// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_merge_sort_async() {
        let data = vec![5, 2, 8, 1, 9];
        let sorted = merge_sort_async_boxed(data).await;
        assert_eq!(sorted, vec![1, 2, 5, 8, 9]);
    }

    #[tokio::test]
    async fn test_binary_search_async() {
        let arr = vec![1, 3, 5, 7, 9];
        assert_eq!(binary_search_async(arr.clone(), 5).await, Some(2));
        assert_eq!(binary_search_async(arr.clone(), 4).await, None);
    }

    #[tokio::test]
    async fn test_fibonacci_memo() {
        let cache = std::sync::Arc::new(tokio::sync::Mutex::new(std::collections::HashMap::new()));
        assert_eq!(fibonacci_memo_async(0, cache.clone()).await, 0);
        assert_eq!(fibonacci_memo_async(1, cache.clone()).await, 1);
        assert_eq!(fibonacci_memo_async(10, cache.clone()).await, 55);
    }

    #[tokio::test]
    async fn test_fibonacci_dp() {
        assert_eq!(fibonacci_dp_async(0).await, 0);
        assert_eq!(fibonacci_dp_async(1).await, 1);
        assert_eq!(fibonacci_dp_async(10).await, 55);
        assert_eq!(fibonacci_dp_async(20).await, 6765);
    }

    #[tokio::test]
    async fn test_factorial_iter() {
        assert_eq!(factorial_iter(0).await, 1);
        assert_eq!(factorial_iter(5).await, 120);
        assert_eq!(factorial_iter(10).await, 3628800);
    }

    #[tokio::test]
    async fn test_fibonacci_stream() {
        let mut stream = fibonacci_stream(6);
        let mut values = Vec::new();
        while let Some(val) = stream.next().await {
            values.push(val);
        }
        assert_eq!(values, vec![0, 1, 1, 2, 3, 5]);
    }

    #[tokio::test]
    async fn test_lcs_async() {
        let x = "ABCBDAB".chars().collect();
        let y = "BDCABA".chars().collect();
        assert_eq!(lcs_async(x, y).await, 4);
    }

    #[tokio::test]
    async fn test_n_queens() {
        let solutions = n_queens_async(4).await;
        assert_eq!(solutions.len(), 2);

        let solutions = n_queens_async(8).await;
        assert_eq!(solutions.len(), 92);
    }
}
