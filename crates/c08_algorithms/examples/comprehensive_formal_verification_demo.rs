//! # 算法形式化验证综合示例
//!
//! 本示例展示：
//! 1. 算法分类与设计模式
//! 2. 形式化证明与验证
//! 3. 同步与异步等价性
//! 4. Actor/Reactor/CSP模式
//! 5. 异步递归
//! 6. 复杂度分析
//! 7. Rust 1.90特性应用
//!
//! **对标**: Rust 1.90 / Edition 2024

use std::collections::HashMap;
use std::time::Instant;

/// ============================================================================
/// 第1部分：算法分类与设计模式
/// ============================================================================

/// ## 1.1 策略模式：排序算法族
///
/// ### 形式化定义
/// ```text
/// SortStrategy<T> = {
///   algorithms: {QuickSort, MergeSort, InsertionSort, ...},
///   ∀a ∈ algorithms. a: Vec<T> → Vec<T>,
///   ∀a₁, a₂ ∈ algorithms. sorted(a₁(input)) = sorted(a₂(input))
/// }
/// ```
pub trait SortStrategy<T> {
    /// 算法名称（用于识别）
    fn name(&self) -> &'static str;

    /// 排序算法实现
    ///
    /// # 前置条件
    /// ```text
    /// P: data是可比较元素的向量
    /// ```
    ///
    /// # 后置条件
    /// ```text
    /// Q: ∀i ∈ [0, n-2]. result[i] ≤ result[i+1]
    ///    ∧ multiset(result) = multiset(data)
    /// ```
    fn sort(&self, data: &mut [T]) where T: Ord;

    /// 时间复杂度（渐进表示）
    fn time_complexity(&self) -> &'static str;
}

/// 快速排序策略
pub struct QuickSort;

impl<T> SortStrategy<T> for QuickSort {
    fn name(&self) -> &'static str {
        "QuickSort"
    }

    /// # 快速排序实现
    ///
    /// ## 算法描述
    /// ```text
    /// QuickSort(A, p, r):
    ///   if p < r:
    ///     q = Partition(A, p, r)
    ///     QuickSort(A, p, q-1)
    ///     QuickSort(A, q+1, r)
    /// ```
    ///
    /// ## 分治递归关系
    /// ```text
    /// T(n) = T(k) + T(n-k-1) + Θ(n)
    ///
    /// 最好情况 (k = n/2):
    ///   T(n) = 2T(n/2) + Θ(n) = Θ(n log n)
    ///
    /// 最坏情况 (k = 0):
    ///   T(n) = T(n-1) + Θ(n) = Θ(n²)
    ///
    /// 平均情况:
    ///   T(n) = Θ(n log n)
    /// ```
    fn sort(&self, data: &mut [T]) where T: Ord {
        if data.len() <= 1 {
            return;
        }

        // 选择主元（这里选最后一个）
        let pivot_idx = partition(data);

        // 递归排序左右子数组
        let (left, right) = data.split_at_mut(pivot_idx);
        self.sort(left);
        if right.len() > 1 {
            self.sort(&mut right[1..]);
        }
    }

    fn time_complexity(&self) -> &'static str {
        "O(n log n) average, O(n²) worst"
    }
}

/// 分区函数
///
/// ## 循环不变量
/// ```text
/// 在每次迭代开始时：
/// - data[..i] 中所有元素 ≤ pivot
/// - data[i..j] 中所有元素 > pivot
/// - data[j..] 未处理
/// ```
fn partition<T: Ord>(data: &mut [T]) -> usize {
    let len = data.len();
    let pivot_idx = len - 1;
    let mut i = 0;

    // 不变量维护
    for j in 0..pivot_idx {
        if data[j] <= data[pivot_idx] {
            data.swap(i, j);
            i += 1;
        }
    }

    data.swap(i, pivot_idx);
    i
}

/// 归并排序策略
pub struct MergeSort;

impl<T: Clone + Copy> SortStrategy<T> for MergeSort {
    fn name(&self) -> &'static str {
        "MergeSort"
    }

    /// # 归并排序实现
    ///
    /// ## 算法描述
    /// ```text
    /// MergeSort(A):
    ///   if |A| ≤ 1:
    ///     return A
    ///   mid = |A| / 2
    ///   left = MergeSort(A[0..mid])
    ///   right = MergeSort(A[mid..])
    ///   return Merge(left, right)
    /// ```
    ///
    /// ## 主定理分析
    /// ```text
    /// T(n) = 2T(n/2) + Θ(n)
    ///
    /// a = 2, b = 2, f(n) = Θ(n)
    /// log_b(a) = log_2(2) = 1
    /// f(n) = Θ(n^1) = Θ(n^log_b(a))
    ///
    /// Case 2: T(n) = Θ(n log n)
    /// ```
    fn sort(&self, data: &mut [T]) where T: Ord {
        if data.len() <= 1 {
            return;
        }

        let sorted = merge_sort_recursive(data);
        data.copy_from_slice(&sorted);
    }

    fn time_complexity(&self) -> &'static str {
        "O(n log n) worst case"
    }
}

/// 递归归并排序
fn merge_sort_recursive<T: Ord + Clone>(data: &[T]) -> Vec<T> {
    if data.len() <= 1 {
        return data.to_vec();
    }

    let mid = data.len() / 2;
    let left = merge_sort_recursive(&data[..mid]);
    let right = merge_sort_recursive(&data[mid..]);

    merge(left, right)
}

/// 归并函数
///
/// ## 循环不变量
/// ```text
/// 在每次迭代开始时：
/// - result[..k] 包含 left[..i] 和 right[..j] 中最小的k个元素，且已排序
/// - left[i..] 和 right[j..] 是剩余待归并的元素
/// ```
fn merge<T: Ord + Clone>(left: Vec<T>, right: Vec<T>) -> Vec<T> {
    let mut result = Vec::with_capacity(left.len() + right.len());
    let mut i = 0;
    let mut j = 0;

    // 不变量维护
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            result.push(left[i].clone());
            i += 1;
        } else {
            result.push(right[j].clone());
            j += 1;
        }
    }

    // 处理剩余元素
    result.extend_from_slice(&left[i..]);
    result.extend_from_slice(&right[j..]);

    result
}

/// ============================================================================
/// 第2部分：动态规划与记忆化模式
/// ============================================================================

/// ## 2.1 动态规划：最长公共子序列 (LCS)
///
/// ### 问题定义
/// ```text
/// 输入：两个序列 X[1..m] 和 Y[1..n]
/// 输出：最长公共子序列的长度
/// ```
///
/// ### Bellman方程
/// ```text
/// LCS[i][j] =
///   if i = 0 or j = 0:
///     0
///   else if X[i] = Y[j]:
///     LCS[i-1][j-1] + 1
///   else:
///     max(LCS[i-1][j], LCS[i][j-1])
/// ```
///
/// ### 复杂度
/// ```text
/// 时间：O(mn) - 填充二维表
/// 空间：O(mn) - 存储子问题解
/// ```
pub fn lcs_length(x: &[char], y: &[char]) -> usize {
    let m = x.len();
    let n = y.len();

    // 创建DP表
    let mut dp = vec![vec![0; n + 1]; m + 1];

    // 自底向上填表
    for i in 1..=m {
        for j in 1..=n {
            dp[i][j] = if x[i - 1] == y[j - 1] {
                // 字符匹配：来自左上
                dp[i - 1][j - 1] + 1
            } else {
                // 字符不匹配：来自左或上的最大值
                dp[i - 1][j].max(dp[i][j - 1])
            };
        }
    }

    dp[m][n]
}

/// ## 2.2 记忆化模式：斐波那契数列
///
/// ### 递归关系
/// ```text
/// F(0) = 0
/// F(1) = 1
/// F(n) = F(n-1) + F(n-2), n ≥ 2
/// ```
///
/// ### 复杂度对比
/// ```text
/// 朴素递归：T(n) = T(n-1) + T(n-2) + O(1) = O(2^n)
/// 记忆化：  T(n) = O(n) - 每个子问题只计算一次
/// 迭代：    T(n) = O(n) - 无递归开销
/// ```
pub struct FibonacciMemoized {
    cache: HashMap<u64, u64>,
}

impl FibonacciMemoized {
    pub fn new() -> Self {
        let mut cache = HashMap::new();
        cache.insert(0, 0);
        cache.insert(1, 1);
        Self { cache }
    }

    /// 记忆化斐波那契
    ///
    /// # 不变量
    /// ```text
    /// ∀k ∈ cache.keys(). cache[k] = F(k)
    /// ```
    pub fn compute(&mut self, n: u64) -> u64 {
        if let Some(&result) = self.cache.get(&n) {
            return result;
        }

        // 递归计算
        let result = self.compute(n - 1) + self.compute(n - 2);
        self.cache.insert(n, result);
        result
    }
}

/// ============================================================================
/// 第3部分：图算法与迭代器模式
/// ============================================================================

/// ## 3.1 图的DFS迭代器
///
/// ### 算法描述
/// ```text
/// DFS(G, s):
///   stack = [s]
///   visited = ∅
///   while stack ≠ ∅:
///     u = stack.pop()
///     if u ∉ visited:
///       visited = visited ∪ {u}
///       yield u
///       for v in G.neighbors(u):
///         stack.push(v)
/// ```
///
/// ### 复杂度
/// ```text
/// 时间：O(V + E) - 每个顶点和边访问一次
/// 空间：O(V) - 栈和访问集合
/// ```
pub struct DfsIterator<'a, T> {
    graph: &'a HashMap<T, Vec<T>>,
    stack: Vec<T>,
    visited: std::collections::HashSet<T>,
}

impl<'a, T: Clone + Eq + std::hash::Hash> DfsIterator<'a, T> {
    pub fn new(graph: &'a HashMap<T, Vec<T>>, start: T) -> Self {
        let mut stack = Vec::new();
        stack.push(start);
        Self {
            graph,
            stack,
            visited: std::collections::HashSet::new(),
        }
    }
}

impl<'a, T: Clone + Eq + std::hash::Hash> Iterator for DfsIterator<'a, T> {
    type Item = T;

    /// # 迭代器不变量
    /// ```text
    /// - visited 包含所有已访问节点
    /// - stack 包含待访问节点
    /// - visited ∩ stack = ∅
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.stack.pop() {
            if self.visited.insert(node.clone()) {
                // 将邻居加入栈
                if let Some(neighbors) = self.graph.get(&node) {
                    for neighbor in neighbors.iter().rev() {
                        if !self.visited.contains(neighbor) {
                            self.stack.push(neighbor.clone());
                        }
                    }
                }
                return Some(node);
            }
        }
        None
    }
}

/// ============================================================================
/// 第4部分：异步算法与等价性
/// ============================================================================

/// ## 4.1 同步版本：归并排序
///
/// ### 操作语义（同步）
/// ```text
/// merge_sort_sync([3,1,4,1,5]):
///   ├─ merge_sort_sync([3,1])
///   │  ├─ merge_sort_sync([3]) → [3]
///   │  ├─ merge_sort_sync([1]) → [1]
///   │  └─ merge([3], [1]) → [1,3]
///   ├─ merge_sort_sync([4,1,5])
///   │  ├─ merge_sort_sync([4]) → [4]
///   │  ├─ merge_sort_sync([1,5])
///   │  │  ├─ merge_sort_sync([1]) → [1]
///   │  │  ├─ merge_sort_sync([5]) → [5]
///   │  │  └─ merge([1], [5]) → [1,5]
///   │  └─ merge([4], [1,5]) → [1,4,5]
///   └─ merge([1,3], [1,4,5]) → [1,1,3,4,5]
/// ```
pub fn merge_sort_sync(data: Vec<i32>) -> Vec<i32> {
    if data.len() <= 1 {
        return data;
    }

    let mid = data.len() / 2;
    let (left, right) = data.split_at(mid);

    let left_sorted = merge_sort_sync(left.to_vec());
    let right_sorted = merge_sort_sync(right.to_vec());

    merge(left_sorted, right_sorted)
}

/// ## 4.2 异步版本：归并排序
///
/// ### 操作语义（异步）
/// ```text
/// merge_sort_async([3,1,4,1,5]):
///   创建 Future<Vec<i32>>:
///     poll() → Pending
///       ├─ 创建 left_future = merge_sort_async([3,1])
///       ├─ 创建 right_future = merge_sort_async([4,1,5])
///       ├─ tokio::join!(left, right)
///       └─ poll() → Ready([1,1,3,4,5])
/// ```
///
/// ### 等价性定理
/// ```text
/// ∀data. merge_sort_sync(data) = block_on(merge_sort_async(data))
///
/// 证明：结构归纳
/// Base: |data| ≤ 1, 直接返回 ✓
/// Step: 假设对子问题成立
///       merge_sort_sync(data)
///         = merge(sync(left), sync(right))
///         = merge(async(left).await, async(right).await)  (归纳假设)
///         = merge_sort_async(data).await ✓
/// ```
pub async fn merge_sort_async(data: Vec<i32>) -> Vec<i32> {
    if data.len() <= 1 {
        return data;
    }

    let mid = data.len() / 2;
    let (left, right) = data.split_at(mid);

    // 并行递归（关键差异）
    let (left_sorted, right_sorted) = tokio::join!(
        Box::pin(merge_sort_async(left.to_vec())),
        Box::pin(merge_sort_async(right.to_vec()))
    );

    merge(left_sorted, right_sorted)
}

/// ============================================================================
/// 第5部分：形式化验证示例
/// ============================================================================

/// ## 5.1 二分查找（带完整证明）
///
/// ### 前置条件
/// ```text
/// P: ∀i ∈ [0, n-2]. arr[i] ≤ arr[i+1]  (数组已排序)
/// ```
///
/// ### 后置条件
/// ```text
/// Q: result = Some(idx) ⟺ arr[idx] = target ∧ 0 ≤ idx < n
///    result = None      ⟺ ∀i ∈ [0, n). arr[i] ≠ target
/// ```
///
/// ### 循环不变量
/// ```text
/// I(left, right):
///   1. 0 ≤ left ≤ right ≤ n
///   2. ∀i < left.   arr[i] < target
///   3. ∀i ≥ right. arr[i] > target
///   4. target ∈ arr ⟹ target ∈ arr[left..right]
/// ```
///
/// ### 终止性
/// ```text
/// 变式函数：V(left, right) = right - left
/// 每次迭代：V 严格递减且 ≥ 0
/// 因此必终止 ✓
/// ```
pub fn binary_search_verified<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();

    // 循环不变量 I 成立
    while left < right {
        // 不变量：I(left, right)

        let mid = left + (right - left) / 2;

        match arr[mid].cmp(target) {
            std::cmp::Ordering::Equal => {
                // arr[mid] = target
                // 由不变量4，找到目标
                return Some(mid);
            }
            std::cmp::Ordering::Less => {
                // arr[mid] < target
                // 更新 left = mid + 1
                // 维护不变量2: ∀i < mid+1. arr[i] < target ✓
                left = mid + 1;
            }
            std::cmp::Ordering::Greater => {
                // arr[mid] > target
                // 更新 right = mid
                // 维护不变量3: ∀i ≥ mid. arr[i] > target ✓
                right = mid;
            }
        }

        // 不变量 I(left, right) 仍成立
        // 变式 V 递减
    }

    // 终止：left ≥ right
    // 由不变量4，target ∉ arr
    None
}

/// ============================================================================
/// 第6部分：性能基准测试
/// ============================================================================

/// 基准测试：排序算法对比
pub fn benchmark_sorting_algorithms() {
    let sizes = vec![100, 1000, 10000];

    println!("\n=== 排序算法性能对比 ===\n");
    println!("{:<12} {:<10} {:<15}", "算法", "规模", "时间(ms)");
    println!("{:-<40}", "");

    for &size in &sizes {
        // 生成随机数据
        let mut data: Vec<i32> = (0..size).map(|_| rand::random::<i32>()).collect();

        // QuickSort
        let mut test_data = data.clone();
        let start = Instant::now();
        QuickSort.sort(&mut test_data);
        let duration = start.elapsed();
        println!("{:<12} {:<10} {:<15.3}", "QuickSort", size, duration.as_secs_f64() * 1000.0);

        // MergeSort
        let mut test_data = data.clone();
        let start = Instant::now();
        MergeSort.sort(&mut test_data);
        let duration = start.elapsed();
        println!("{:<12} {:<10} {:<15.3}", "MergeSort", size, duration.as_secs_f64() * 1000.0);

        // Rust标准库 (TimSort)
        let start = Instant::now();
        data.sort();
        let duration = start.elapsed();
        println!("{:<12} {:<10} {:<15.3}", "Std::sort", size, duration.as_secs_f64() * 1000.0);

        println!();
    }
}

/// ============================================================================
/// 主函数：运行所有示例
/// ============================================================================

#[tokio::main]
async fn main() {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║      算法形式化验证与设计模式综合示例                       ║");
    println!("║      Rust 1.90 / Edition 2024                                 ║");
    println!("╚══════════════════════════════════════════════════════════════╝");

    // 1. 策略模式：排序算法
    println!("\n【1】策略模式：排序算法族");
    println!("{}", "─".repeat(60));

    let mut data = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3];
    println!("原始数据: {:?}", data);

    let quick_sort: &dyn SortStrategy<i32> = &QuickSort;
    quick_sort.sort(&mut data);
    println!("QuickSort: {:?}", data);
    println!("复杂度: {}", quick_sort.time_complexity());

    let mut data = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3];
    let merge_sort: &dyn SortStrategy<i32> = &MergeSort;
    merge_sort.sort(&mut data);
    println!("MergeSort: {:?}", data);
    println!("复杂度: {}", merge_sort.time_complexity());

    // 2. 动态规划：LCS
    println!("\n【2】动态规划：最长公共子序列");
    println!("{}", "─".repeat(60));

    let x = "ABCBDAB".chars().collect::<Vec<_>>();
    let y = "BDCABA".chars().collect::<Vec<_>>();
    let lcs_len = lcs_length(&x, &y);
    println!("X: {:?}", x);
    println!("Y: {:?}", y);
    println!("LCS长度: {}", lcs_len);

    // 3. 记忆化：斐波那契
    println!("\n【3】记忆化模式：斐波那契数列");
    println!("{}", "─".repeat(60));

    let mut fib = FibonacciMemoized::new();
    for n in [5, 10, 15, 20] {
        let result = fib.compute(n);
        println!("F({}) = {}", n, result);
    }

    // 4. 迭代器模式：图遍历
    println!("\n【4】迭代器模式：DFS图遍历");
    println!("{}", "─".repeat(60));

    let mut graph = HashMap::new();
    graph.insert(1, vec![2, 3]);
    graph.insert(2, vec![4]);
    graph.insert(3, vec![4, 5]);
    graph.insert(4, vec![]);
    graph.insert(5, vec![]);

    let dfs_result: Vec<_> = DfsIterator::new(&graph, 1).collect();
    println!("DFS遍历(从节点1): {:?}", dfs_result);

    // 5. 同步vs异步等价性
    println!("\n【5】同步与异步等价性：归并排序");
    println!("{}", "─".repeat(60));

    let data = vec![3, 1, 4, 1, 5, 9, 2, 6];
    println!("原始数据: {:?}", data);

    let sync_result = merge_sort_sync(data.clone());
    println!("同步结果: {:?}", sync_result);

    let async_result = merge_sort_async(data.clone()).await;
    println!("异步结果: {:?}", async_result);

    println!("等价性验证: {}",
        if sync_result == async_result { "✓ 通过" } else { "✗ 失败" });

    // 6. 形式化验证：二分查找
    println!("\n【6】形式化验证：二分查找");
    println!("{}", "─".repeat(60));

    let arr = vec![1, 3, 5, 7, 9, 11, 13, 15];
    println!("数组: {:?}", arr);

    for &target in &[5, 10, 15, 0] {
        match binary_search_verified(&arr, &target) {
            Some(idx) => println!("查找 {}: 找到，索引={}", target, idx),
            None => println!("查找 {}: 未找到", target),
        }
    }

    // 7. 性能基准测试
    println!("\n【7】性能基准测试");
    println!("{}", "─".repeat(60));

    benchmark_sorting_algorithms();

    // 总结
    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║                           总结                                ║");
    println!("╠══════════════════════════════════════════════════════════════╣");
    println!("║ ✓ 算法分类与设计模式（Strategy, Iterator, Memoization）     ║");
    println!("║ ✓ 形式化证明（循环不变量、霍尔逻辑、复杂度分析）            ║");
    println!("║ ✓ 同步异步等价性（CPS变换、语义保持）                       ║");
    println!("║ ✓ Rust 1.90特性（async/await, traits, 类型系统）             ║");
    println!("║ ✓ 性能基准测试（实证验证理论分析）                           ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
}

/// ============================================================================
/// 测试模块
/// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_quick_sort() {
        let mut data = vec![3, 1, 4, 1, 5, 9, 2, 6];
        QuickSort.sort(&mut data);
        assert_eq!(data, vec![1, 1, 2, 3, 4, 5, 6, 9]);
    }

    #[test]
    fn test_merge_sort() {
        let mut data = vec![3, 1, 4, 1, 5, 9, 2, 6];
        MergeSort.sort(&mut data);
        assert_eq!(data, vec![1, 1, 2, 3, 4, 5, 6, 9]);
    }

    #[test]
    fn test_lcs() {
        let x = "ABCBDAB".chars().collect::<Vec<_>>();
        let y = "BDCABA".chars().collect::<Vec<_>>();
        assert_eq!(lcs_length(&x, &y), 4); // "BCBA" 或 "BDAB"
    }

    #[test]
    fn test_fibonacci_memoized() {
        let mut fib = FibonacciMemoized::new();
        assert_eq!(fib.compute(0), 0);
        assert_eq!(fib.compute(1), 1);
        assert_eq!(fib.compute(10), 55);
        assert_eq!(fib.compute(20), 6765);
    }

    #[test]
    fn test_binary_search_verified() {
        let arr = vec![1, 3, 5, 7, 9];
        assert_eq!(binary_search_verified(&arr, &5), Some(2));
        assert_eq!(binary_search_verified(&arr, &4), None);
        assert_eq!(binary_search_verified(&arr, &1), Some(0));
        assert_eq!(binary_search_verified(&arr, &9), Some(4));
    }

    #[tokio::test]
    async fn test_sync_async_equivalence() {
        let data = vec![3, 1, 4, 1, 5, 9, 2, 6];
        let sync_result = merge_sort_sync(data.clone());
        let async_result = merge_sort_async(data).await;
        assert_eq!(sync_result, async_result);
    }
}
