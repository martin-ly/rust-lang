//! 异步递归深度分析 - Async Recursion Deep Analysis
//!
//! # 概述 (Overview)
//!
//! 本模块深入分析 Rust 中的异步递归，包括：
//! - 异步递归与同步递归的等价关系
//! - 异步递归的实现技术（Box、async-recursion）
//! - 尾递归优化在异步中的应用
//! - 递归与迭代的转换证明
//! - 内存模型与栈管理
//!
//! # 理论基础 (Theoretical Foundations)
//!
//! ## 1. 递归的形式化定义
//!
//! ### 1.1 同步递归
//!
//! ```text
//! 递归函数 f : A → B 定义为：
//! f(x) = if base_case(x) then base_value(x)
//!        else combine(f(rec_call(x)))
//!
//! 示例: 阶乘
//! fact(n) = if n ≤ 1 then 1
//!           else n * fact(n - 1)
//! ```
//!
//! ### 1.2 异步递归
//!
//! ```text
//! 异步递归函数 f_async : A → Future<B> 定义为：
//! f_async(x) = async {
//!   if base_case(x) then return base_value(x)
//!   else combine(await f_async(rec_call(x)))
//! }
//!
//! 示例: 异步阶乘
//! fact_async(n) = async {
//!   if n ≤ 1 then return 1
//!   else return n * await fact_async(n - 1)
//! }
//! ```
//!
//! ## 2. 异步递归的挑战
//!
//! ### 2.1 大小问题 (Sized Issue)
//!
//! ```text
//! 问题: 异步函数返回 impl Future，其大小在编译时未知
//!
//! async fn f(n: u32) -> u32 {
//!     if n == 0 { 0 }
//!     else { f(n-1).await + 1 }  // ❌ 编译错误
//! }
//!
//! 原因: Future 包含捕获的状态，递归调用导致无限大小
//! sizeof(F) = sizeof(State) + sizeof(F)  // 无法求解
//! ```
//!
//! ### 2.2 解决方案: Box 堆分配
//!
//! ```text
//! 使用 Box 打破循环依赖：
//! sizeof(Box<F>) = sizeof(pointer) = 8 bytes (64-bit)
//!
//! fn f(n: u32) -> Pin<Box<dyn Future<Output = u32>>> {
//!     Box::pin(async move {
//!         if n == 0 { 0 }
//!         else { f(n-1).await + 1 }  // ✓ 正确
//!     })
//! }
//! ```
//!
//! ## 3. 递归与迭代的等价性
//!
//! ### 3.1 尾递归 (Tail Recursion)
//!
//! ```text
//! 尾递归定义: f 是尾递归的，如果递归调用是函数的最后一个操作
//!
//! 尾递归形式:
//! f(x, acc) = if base_case(x) then acc
//!             else f(rec_call(x), update(acc))
//!
//! 等价迭代形式:
//! f_iter(x) = {
//!     let mut acc = init;
//!     while !base_case(x) {
//!         acc = update(acc);
//!         x = rec_call(x);
//!     }
//!     acc
//! }
//! ```
//!
//! ### 3.2 一般递归到迭代的转换
//!
//! ```text
//! 使用显式栈模拟递归:
//!
//! 递归版本:
//! fn f(x) = if base(x) then g(x)
//!           else h(x, f(left(x)), f(right(x)))
//!
//! 迭代版本:
//! fn f_iter(x) = {
//!     stack = [x];
//!     while !stack.is_empty() {
//!         current = stack.pop();
//!         if base(current) { process(g(current)) }
//!         else { stack.push(right(current)); stack.push(left(current)); }
//!     }
//! }
//! ```
//!
//! ## 4. 异步递归的内存模型
//!
//! ```text
//! 同步递归: 使用系统栈
//! - 每次调用占用栈帧
//! - 深度受限于栈大小 (通常 2-8 MB)
//!
//! 异步递归: 使用堆内存
//! - 每个 Future 在堆上分配 (通过 Box)
//! - 深度受限于堆大小 (通常远大于栈)
//! - 可以处理更深的递归
//! ```

use std::future::Future;
use std::pin::Pin;
use std::time::Duration;
use tokio::time::sleep;

/// # 示例 1: 基本异步递归
///
/// 展示如何正确实现异步递归函数
pub mod basic_async_recursion {
    use super::*;

    /// 同步递归: 计算阶乘
    ///
    /// ## 形式化定义
    /// ```text
    /// fact : ℕ → ℕ
    /// fact(n) = Π_{i=1}^{n} i
    ///
    /// 递归定义:
    /// fact(0) = 1
    /// fact(n) = n × fact(n-1)
    /// ```
    pub fn factorial_sync(n: u64) -> u64 {
        if n <= 1 {
            1
        } else {
            n * factorial_sync(n - 1)
        }
    }

    /// 异步递归: 计算阶乘（使用 Box 实现）
    ///
    /// ## 实现要点
    /// ```text
    /// 1. 返回类型: Pin<Box<dyn Future<Output = u64>>>
    /// 2. 使用 Box::pin 包装 async block
    /// 3. async move 捕获所有权
    /// ```
    pub fn factorial_async(n: u64) -> Pin<Box<dyn Future<Output = u64> + Send>> {
        Box::pin(async move {
            if n <= 1 {
                1
            } else {
                // 模拟异步操作
                sleep(Duration::from_micros(1)).await;
                n * factorial_async(n - 1).await
            }
        })
    }

    /// 尾递归异步版本（避免装箱）
    ///
    /// ## 使用尾递归避免装箱开销
    pub async fn factorial_async_tail_wrapper(n: u64) -> u64 {
        factorial_async_tail_impl(n, 1).await
    }

    fn factorial_async_tail_impl(n: u64, acc: u64) -> Pin<Box<dyn Future<Output = u64> + Send>> {
        Box::pin(async move {
            if n <= 1 {
                acc
            } else {
                sleep(Duration::from_micros(1)).await;
                factorial_async_tail_impl(n - 1, n * acc).await
            }
        })
    }

    /// 验证等价性
    pub async fn verify_equivalence() {
        println!("\n=== 异步递归基础示例 ===");

        for n in 0..=10 {
            let sync_result = factorial_sync(n);
            let async_result = factorial_async(n).await;

            assert_eq!(
                sync_result, async_result,
                "等价性验证失败: n={}, sync={}, async={}",
                n, sync_result, async_result
            );

            println!("✓ fact({:2}) = {:10}", n, sync_result);
        }

        println!("✓ 同步递归与异步递归语义等价");
    }
}

/// # 示例 2: 尾递归优化
///
/// 展示尾递归及其在异步中的应用
pub mod tail_recursion {
    use super::*;

    /// 非尾递归版本: 阶乘
    ///
    /// ## 问题
    /// ```text
    /// fact(5) = 5 * fact(4)
    ///         = 5 * (4 * fact(3))
    ///         = 5 * (4 * (3 * fact(2)))
    ///         = 5 * (4 * (3 * (2 * fact(1))))
    ///         = 5 * (4 * (3 * (2 * 1)))
    ///
    /// 需要保留所有中间状态，栈深度 = n
    /// ```
    pub fn factorial_non_tail(n: u64) -> u64 {
        if n <= 1 {
            1
        } else {
            n * factorial_non_tail(n - 1) // 递归调用后还有乘法操作
        }
    }

    /// 尾递归版本: 阶乘
    ///
    /// ## 优化
    /// ```text
    /// fact_tail(5, 1) = fact_tail(4, 5)
    ///                 = fact_tail(3, 20)
    ///                 = fact_tail(2, 60)
    ///                 = fact_tail(1, 120)
    ///                 = 120
    ///
    /// 只需保留当前状态，可以优化为循环
    /// ```
    pub fn factorial_tail(n: u64, acc: u64) -> u64 {
        if n <= 1 {
            acc
        } else {
            factorial_tail(n - 1, n * acc) // 递归调用是最后一个操作
        }
    }

    /// 异步尾递归版本
    pub fn factorial_async_tail(
        n: u64,
        acc: u64,
    ) -> Pin<Box<dyn Future<Output = u64> + Send>> {
        Box::pin(async move {
            if n <= 1 {
                acc
            } else {
                sleep(Duration::from_micros(1)).await;
                factorial_async_tail(n - 1, n * acc).await
            }
        })
    }

    /// 迭代版本（等价于尾递归）
    ///
    /// ## 等价性证明
    /// ```text
    /// 对于所有 n,
    /// factorial_tail(n, 1) = factorial_iter(n)
    ///
    /// 证明: 归纳法
    /// Base case: n = 1
    ///   factorial_tail(1, 1) = 1
    ///   factorial_iter(1) = 1
    ///   ✓
    ///
    /// Inductive step: 假设 n = k 成立
    ///   factorial_tail(k+1, 1) = factorial_tail(k, k+1)
    ///   = factorial_tail(k-1, k*(k+1))
    ///   = ...
    ///   = (k+1)!
    ///
    ///   factorial_iter(k+1) 经过 k+1 次迭代也得到 (k+1)!
    ///   ✓
    /// ```
    pub fn factorial_iter(n: u64) -> u64 {
        let mut acc = 1;
        let mut i = n;
        while i > 1 {
            acc *= i;
            i -= 1;
        }
        acc
    }

    /// 异步迭代版本
    pub async fn factorial_async_iter(n: u64) -> u64 {
        let mut acc = 1;
        let mut i = n;
        while i > 1 {
            sleep(Duration::from_micros(1)).await;
            acc *= i;
            i -= 1;
        }
        acc
    }

    /// 验证所有版本的等价性
    pub async fn verify_all_versions() {
        println!("\n=== 尾递归优化示例 ===");

        for n in 1..=10 {
            let non_tail = factorial_non_tail(n);
            let tail = factorial_tail(n, 1);
            let iter = factorial_iter(n);
            let async_tail = factorial_async_tail(n, 1).await;
            let async_iter = factorial_async_iter(n).await;

            assert_eq!(non_tail, tail);
            assert_eq!(tail, iter);
            assert_eq!(iter, async_tail);
            assert_eq!(async_tail, async_iter);

            println!(
                "✓ n={:2} | 非尾递归={:10} | 尾递归={:10} | 迭代={:10} | 异步尾递归={:10} | 异步迭代={:10}",
                n, non_tail, tail, iter, async_tail, async_iter
            );
        }

        println!("✓ 所有版本语义等价");
    }
}

/// # 示例 3: 树的递归遍历
///
/// 展示更复杂的递归结构
pub mod tree_traversal {
    use super::*;

    /// 二叉树定义
    #[derive(Debug, Clone)]
    pub enum Tree {
        Leaf(i32),
        Node(i32, Box<Tree>, Box<Tree>),
    }

    impl Tree {
        /// 创建示例树
        ///
        /// ```text
        ///       10
        ///      /  \
        ///     5    15
        ///    / \   / \
        ///   3  7  12 20
        /// ```
        pub fn example() -> Self {
            Tree::Node(
                10,
                Box::new(Tree::Node(
                    5,
                    Box::new(Tree::Leaf(3)),
                    Box::new(Tree::Leaf(7)),
                )),
                Box::new(Tree::Node(
                    15,
                    Box::new(Tree::Leaf(12)),
                    Box::new(Tree::Leaf(20)),
                )),
            )
        }
    }

    /// 同步递归: 计算树的和
    pub fn sum_sync(tree: &Tree) -> i32 {
        match tree {
            Tree::Leaf(val) => *val,
            Tree::Node(val, left, right) => val + sum_sync(left) + sum_sync(right),
        }
    }

    /// 异步递归: 计算树的和
    pub fn sum_async(tree: &Tree) -> Pin<Box<dyn Future<Output = i32> + Send + '_>> {
        Box::pin(async move {
            match tree {
                Tree::Leaf(val) => *val,
                Tree::Node(val, left, right) => {
                    sleep(Duration::from_micros(1)).await;
                    // 并发计算左右子树
                    let (left_sum, right_sum) =
                        futures::join!(sum_async(left), sum_async(right));
                    val + left_sum + right_sum
                }
            }
        })
    }

    /// 迭代版本: 使用显式栈
    ///
    /// ## 转换方法
    /// ```text
    /// 1. 创建栈存储待处理节点
    /// 2. 深度优先遍历
    /// 3. 累加所有值
    /// ```
    pub fn sum_iter(tree: &Tree) -> i32 {
        let mut stack = vec![tree];
        let mut total = 0;

        while let Some(current) = stack.pop() {
            match current {
                Tree::Leaf(val) => {
                    total += val;
                }
                Tree::Node(val, left, right) => {
                    total += val;
                    stack.push(right);
                    stack.push(left);
                }
            }
        }

        total
    }

    /// 异步迭代版本
    pub async fn sum_async_iter(tree: &Tree) -> i32 {
        let mut stack = vec![tree];
        let mut total = 0;

        while let Some(current) = stack.pop() {
            sleep(Duration::from_micros(1)).await;
            match current {
                Tree::Leaf(val) => {
                    total += val;
                }
                Tree::Node(val, left, right) => {
                    total += val;
                    stack.push(right);
                    stack.push(left);
                }
            }
        }

        total
    }

    /// 验证等价性
    pub async fn verify_equivalence() {
        println!("\n=== 树遍历递归示例 ===");

        let tree = Tree::example();
        println!("示例树: {:?}", tree);

        let sync_result = sum_sync(&tree);
        let async_result = sum_async(&tree).await;
        let iter_result = sum_iter(&tree);
        let async_iter_result = sum_async_iter(&tree).await;

        assert_eq!(sync_result, async_result);
        assert_eq!(async_result, iter_result);
        assert_eq!(iter_result, async_iter_result);

        println!("同步递归:   {}", sync_result);
        println!("异步递归:   {}", async_result);
        println!("同步迭代:   {}", iter_result);
        println!("异步迭代:   {}", async_iter_result);
        println!("✓ 所有版本语义等价");
    }
}

/// # 示例 4: 深度递归与栈溢出
///
/// 展示异步递归在深度场景下的优势
pub mod deep_recursion {
    use super::*;

    /// 同步递归: 求和 1 到 n
    /// ⚠️ 注意: 深度过大会导致栈溢出
    pub fn sum_to_n_sync(n: u64) -> u64 {
        if n == 0 {
            0
        } else {
            n + sum_to_n_sync(n - 1)
        }
    }

    /// 异步递归: 求和 1 到 n
    /// ✓ 使用堆内存，可以处理更深的递归
    pub fn sum_to_n_async(n: u64) -> Pin<Box<dyn Future<Output = u64> + Send>> {
        Box::pin(async move {
            if n == 0 {
                0
            } else {
                // 不添加 sleep，避免测试时间过长
                n + sum_to_n_async(n - 1).await
            }
        })
    }

    /// 尾递归版本（不会栈溢出）
    pub fn sum_to_n_tail(n: u64, acc: u64) -> u64 {
        if n == 0 {
            acc
        } else {
            sum_to_n_tail(n - 1, acc + n)
        }
    }

    /// 迭代版本（最高效）
    pub fn sum_to_n_iter(n: u64) -> u64 {
        (1..=n).sum()
    }

    /// 数学公式版本（O(1) 时间复杂度）
    ///
    /// ## 数学证明
    /// ```text
    /// sum(1..n) = Σ_{i=1}^{n} i = n(n+1)/2
    ///
    /// 证明 (归纳法):
    /// Base: n=1, sum=1, formula=1(1+1)/2=1 ✓
    /// Step: 假设 n=k 成立
    ///   sum(1..k+1) = sum(1..k) + (k+1)
    ///               = k(k+1)/2 + (k+1)
    ///               = (k(k+1) + 2(k+1))/2
    ///               = (k+1)(k+2)/2 ✓
    /// ```
    pub fn sum_to_n_formula(n: u64) -> u64 {
        n * (n + 1) / 2
    }

    /// 测试不同深度
    pub async fn test_different_depths() {
        println!("\n=== 深度递归测试 ===");

        let depths = vec![10, 100, 1000];

        for depth in depths {
            println!("\n深度: {}", depth);

            // 尾递归版本
            let tail_result = sum_to_n_tail(depth, 0);
            println!("  尾递归: {}", tail_result);

            // 迭代版本
            let iter_result = sum_to_n_iter(depth);
            println!("  迭代:   {}", iter_result);

            // 异步递归版本
            let async_result = sum_to_n_async(depth).await;
            println!("  异步递归: {}", async_result);

            // 数学公式
            let formula_result = sum_to_n_formula(depth);
            println!("  数学公式: {}", formula_result);

            assert_eq!(tail_result, iter_result);
            assert_eq!(iter_result, async_result);
            assert_eq!(async_result, formula_result);

            println!("  ✓ 所有方法结果一致");
        }

        // 非常深的递归（只测试非递归方法）
        let very_deep = 1_000_000;
        println!("\n极深递归测试: {}", very_deep);
        let formula = sum_to_n_formula(very_deep);
        let iter = sum_to_n_iter(very_deep);
        assert_eq!(formula, iter);
        println!("  数学公式 = 迭代 = {}", formula);
        println!("  ✓ 非递归方法可以处理任意深度");
    }
}

/// # 示例 5: 互递归 (Mutual Recursion)
///
/// 展示相互调用的递归函数
pub mod mutual_recursion {
    use super::*;

    /// 判断偶数（通过互递归）
    pub fn is_even_sync(n: u32) -> bool {
        if n == 0 {
            true
        } else {
            is_odd_sync(n - 1)
        }
    }

    /// 判断奇数（通过互递归）
    pub fn is_odd_sync(n: u32) -> bool {
        if n == 0 {
            false
        } else {
            is_even_sync(n - 1)
        }
    }

    /// 异步版本: 判断偶数
    pub fn is_even_async(n: u32) -> Pin<Box<dyn Future<Output = bool> + Send>> {
        Box::pin(async move {
            if n == 0 {
                true
            } else {
                is_odd_async(n - 1).await
            }
        })
    }

    /// 异步版本: 判断奇数
    pub fn is_odd_async(n: u32) -> Pin<Box<dyn Future<Output = bool> + Send>> {
        Box::pin(async move {
            if n == 0 {
                false
            } else {
                is_even_async(n - 1).await
            }
        })
    }

    /// 验证互递归
    pub async fn verify_mutual_recursion() {
        println!("\n=== 互递归示例 ===");

        for n in 0..=10 {
            let sync_even = is_even_sync(n);
            let sync_odd = is_odd_sync(n);
            let async_even = is_even_async(n).await;
            let async_odd = is_odd_async(n).await;

            assert_eq!(sync_even, async_even);
            assert_eq!(sync_odd, async_odd);
            assert_ne!(sync_even, sync_odd); // even 和 odd 互补

            println!(
                "n={:2} | 同步: even={:5}, odd={:5} | 异步: even={:5}, odd={:5}",
                n, sync_even, sync_odd, async_even, async_odd
            );
        }

        println!("✓ 互递归验证通过");
    }
}

/// # 综合示例: 运行所有演示
pub async fn run_all_examples() {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║       Rust 异步递归深度分析                              ║");
    println!("║       Async Recursion Deep Analysis                      ║");
    println!("╚══════════════════════════════════════════════════════════╝");

    // 1. 基本异步递归
    basic_async_recursion::verify_equivalence().await;

    // 2. 尾递归优化
    tail_recursion::verify_all_versions().await;

    // 3. 树遍历
    tree_traversal::verify_equivalence().await;

    // 4. 深度递归
    deep_recursion::test_different_depths().await;

    // 5. 互递归
    mutual_recursion::verify_mutual_recursion().await;

    println!("\n════════════════════════════════════════════════════════════");
    println!("所有递归示例执行完成！");
    println!("════════════════════════════════════════════════════════════\n");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_basic_recursion() {
        basic_async_recursion::verify_equivalence().await;
    }

    #[tokio::test]
    async fn test_tail_recursion() {
        tail_recursion::verify_all_versions().await;
    }

    #[tokio::test]
    async fn test_tree_traversal() {
        tree_traversal::verify_equivalence().await;
    }

    #[tokio::test]
    async fn test_deep_recursion() {
        deep_recursion::test_different_depths().await;
    }

    #[tokio::test]
    async fn test_mutual_recursion() {
        mutual_recursion::verify_mutual_recursion().await;
    }
}

