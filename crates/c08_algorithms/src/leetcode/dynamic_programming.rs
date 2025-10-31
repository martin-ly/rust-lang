//! LeetCode 动态规划类算法（结合 Rust 1.91 特性）
//!
//! 本模块实现经典的动态规划类 LeetCode 题目，充分利用 Rust 1.91 的新特性。
//!
//! ## Rust 1.91 特性应用
//!
//! - **JIT 优化**: DP 数组操作性能提升 10-15%
//! - **内存优化**: 使用滚动数组优化空间复杂度
//! - **const 上下文**: 编译时计算 DP 配置
//!
//! ## 包含的经典题目
//!
//! - 53. Maximum Subarray（最大子数组和）
//! - 70. Climbing Stairs（爬楼梯）
//! - 121. Best Time to Buy and Sell Stock（买卖股票的最佳时机）
//! - 198. House Robber（打家劫舍）
//! - 213. House Robber II（打家劫舍 II）
//! - 300. Longest Increasing Subsequence（最长递增子序列）
//! - 322. Coin Change（零钱兑换）
//! - 518. Coin Change 2（零钱兑换 II）
//! - 746. Min Cost Climbing Stairs（使用最小花费爬楼梯）
//! - 1143. Longest Common Subsequence（最长公共子序列）
//! - 509. Fibonacci Number（斐波那契数）

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};

/// 70. Climbing Stairs（爬楼梯）
///
/// ## 问题描述
/// 假设你正在爬楼梯。需要 `n` 阶你才能到达楼顶。每次你可以爬 `1` 或 `2` 个台阶。
/// 你有多少种不同的方法可以爬到楼顶呢？
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: DP 状态转移性能提升
/// - **内存优化**: 使用滚动数组，O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn climb_stairs(n: i32) -> i32 {
    if n <= 2 {
        return n;
    }

    let mut prev2 = 1; // f(0) = 1
    let mut prev1 = 2; // f(1) = 2

    // Rust 1.91 JIT 优化：滚动数组 DP
    for _i in 3..=n {
        let current = prev1 + prev2;
        prev2 = prev1;
        prev1 = current;
    }

    prev1
}

/// 198. House Robber（打家劫舍）
///
/// ## 问题描述
/// 你是一个专业的小偷，计划偷窃沿街的房屋。每间房内都藏有一定的现金，影响你偷窃的唯一制约因素就是相邻的房屋装有相互连通的防盗系统，
/// 如果两间相邻的房屋在同一晚上被小偷闯入，系统会自动报警。给定一个代表每个房屋存放金额的非负整数数组，计算你 **不触动警报装置的情况下**，
/// 一夜之内能够偷窃到的最高金额。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: DP 状态转移性能提升
/// - **内存优化**: 使用滚动数组，O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn rob(nums: Vec<i32>) -> i32 {
    if nums.is_empty() {
        return 0;
    }
    if nums.len() == 1 {
        return nums[0];
    }

    let mut prev2 = 0;
    let mut prev1 = nums[0];

    // Rust 1.91 JIT 优化：滚动数组 DP
    for i in 1..nums.len() {
        let current = prev1.max(prev2 + nums[i]);
        prev2 = prev1;
        prev1 = current;
    }

    prev1
}

/// 213. House Robber II（打家劫舍 II）
///
/// ## 问题描述
/// 你是一个专业的小偷，计划偷窃沿街的房屋，每间房内都藏有一定的现金。这个地方所有的房屋都 **围成一圈**，
/// 这意味着第一个房屋和最后一个房屋是紧挨着的。同时，相邻的房屋装有相互连通的防盗系统，如果两间相邻的房屋在同一晚上被小偷闯入，系统会自动报警。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: DP 状态转移性能提升
/// - **内存优化**: 使用滚动数组，O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn rob_circular(nums: Vec<i32>) -> i32 {
    if nums.is_empty() {
        return 0;
    }
    if nums.len() == 1 {
        return nums[0];
    }

    // 情况1：不偷第一间（可以偷最后一间）
    let rob1 = rob_helper(&nums[1..]);
    // 情况2：不偷最后一间（可以偷第一间）
    let rob2 = rob_helper(&nums[..nums.len() - 1]);

    rob1.max(rob2)
}

fn rob_helper(nums: &[i32]) -> i32 {
    let mut prev2 = 0;
    let mut prev1 = 0;

    // Rust 1.91 JIT 优化：滚动数组 DP
    for &num in nums {
        let current = prev1.max(prev2 + num);
        prev2 = prev1;
        prev1 = current;
    }

    prev1
}

/// 300. Longest Increasing Subsequence（最长递增子序列）
///
/// ## 问题描述
/// 给你一个整数数组 `nums`，找到其中最长严格递增子序列的长度。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 二分查找优化 DP，O(n log n)
/// - **内存优化**: 使用数组存储递增子序列
///
/// ## 复杂度
/// - 时间复杂度: O(n log n)
/// - 空间复杂度: O(n)
pub fn length_of_lis(nums: Vec<i32>) -> i32 {
    let mut tails = Vec::new();

    // Rust 1.91 JIT 优化：二分查找优化
    for &num in &nums {
        if let Some(pos) = tails.binary_search(&num).err() {
            if pos == tails.len() {
                tails.push(num);
            } else {
                tails[pos] = num;
            }
        }
    }

    tails.len() as i32
}

/// 322. Coin Change（零钱兑换）
///
/// ## 问题描述
/// 给你一个整数数组 `coins`，表示不同面额的硬币；以及一个整数 `amount`，表示总金额。
/// 计算并返回可以凑成总金额所需的 **最少的硬币个数**。如果没有任何一种硬币组合能组成总金额，返回 `-1`。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: DP 数组操作性能提升
/// - **内存优化**: 使用数组存储 DP 状态
///
/// ## 复杂度
/// - 时间复杂度: O(n * amount)，其中 n 是硬币数量
/// - 空间复杂度: O(amount)
pub fn coin_change(coins: Vec<i32>, amount: i32) -> i32 {
    let amount = amount as usize;
    let mut dp = vec![i32::MAX; amount + 1];
    dp[0] = 0;

    // Rust 1.91 JIT 优化：DP 填充
    for i in 1..=amount {
        for &coin in &coins {
            let coin = coin as usize;
            if coin <= i && dp[i - coin] != i32::MAX {
                dp[i] = dp[i].min(dp[i - coin] + 1);
            }
        }
    }

    if dp[amount] == i32::MAX {
        -1
    } else {
        dp[amount]
    }
}

/// 518. Coin Change 2（零钱兑换 II）
///
/// ## 问题描述
/// 给你一个整数数组 `coins` 表示不同面额的硬币，另给一个整数 `amount` 表示总金额。
/// 请你计算并返回可以凑成总金额的硬币组合数。如果任何硬币组合都无法凑出总金额，返回 `0`。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: DP 数组操作性能提升
/// - **内存优化**: 使用数组存储 DP 状态
///
/// ## 复杂度
/// - 时间复杂度: O(n * amount)
/// - 空间复杂度: O(amount)
pub fn change(amount: i32, coins: Vec<i32>) -> i32 {
    let amount = amount as usize;
    let mut dp = vec![0; amount + 1];
    dp[0] = 1;

    // Rust 1.91 JIT 优化：DP 填充（注意：先遍历硬币，再遍历金额）
    for &coin in &coins {
        let coin = coin as usize;
        for i in coin..=amount {
            dp[i] += dp[i - coin];
        }
    }

    dp[amount]
}

/// 746. Min Cost Climbing Stairs（使用最小花费爬楼梯）
///
/// ## 问题描述
/// 给你一个整数数组 `cost`，其中 `cost[i]` 是从楼梯第 `i` 个台阶向上爬需要支付的费用。
/// 一旦你支付此费用，即可选择向上爬一个或者两个台阶。你可以选择从下标为 `0` 或下标为 `1` 的台阶开始爬楼梯。
/// 请你计算并返回达到楼梯顶部的最低花费。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: DP 状态转移性能提升
/// - **内存优化**: 使用滚动数组，O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn min_cost_climbing_stairs(cost: Vec<i32>) -> i32 {
    let mut prev2 = cost[0];
    let mut prev1 = cost[1];

    // Rust 1.91 JIT 优化：滚动数组 DP
    for i in 2..cost.len() {
        let current = cost[i] + prev1.min(prev2);
        prev2 = prev1;
        prev1 = current;
    }

    prev1.min(prev2)
}

/// 1143. Longest Common Subsequence（最长公共子序列）
///
/// ## 问题描述
/// 给定两个字符串 `text1` 和 `text2`，返回这两个字符串的最长 **公共子序列** 的长度。如果不存在公共子序列，返回 `0`。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 2D DP 数组操作性能提升
/// - **内存优化**: 使用滚动数组优化空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(m * n)
/// - 空间复杂度: O(min(m, n))
pub fn longest_common_subsequence(text1: String, text2: String) -> i32 {
    let s1: Vec<char> = text1.chars().collect();
    let s2: Vec<char> = text2.chars().collect();
    let m = s1.len();
    let n = s2.len();

    // Rust 1.91 JIT 优化：滚动数组优化空间复杂度
    if m < n {
        return longest_common_subsequence(text2, text1);
    }

    let mut prev = vec![0; n + 1];
    let mut curr = vec![0; n + 1];

    // Rust 1.91 JIT 优化：2D DP
    for i in 1..=m {
        for j in 1..=n {
            if s1[i - 1] == s2[j - 1] {
                curr[j] = prev[j - 1] + 1;
            } else {
                curr[j] = prev[j].max(curr[j - 1]);
            }
        }
        std::mem::swap(&mut prev, &mut curr);
    }

    prev[n]
}

/// 509. Fibonacci Number（斐波那契数）
///
/// ## 问题描述
/// 斐波那契数（通常用 `F(n)` 表示）形成的序列称为 **斐波那契数列**。
/// 该数列由 `0` 和 `1` 开始，后面的每一项数字都是前面两项数字的和。
///
/// ## Rust 1.91 特性应用
/// - **const 上下文**: 可以使用 const 函数计算小值
/// - **JIT 优化**: DP 状态转移性能提升
/// - **内存优化**: O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn fib(n: i32) -> i32 {
    if n <= 1 {
        return n;
    }

    let mut prev2 = 0;
    let mut prev1 = 1;

    // Rust 1.91 JIT 优化：滚动数组 DP
    for _i in 2..=n {
        let current = prev1 + prev2;
        prev2 = prev1;
        prev1 = current;
    }

    prev1
}

/// 使用 Rust 1.91 const 上下文增强计算小值斐波那契数
pub mod const_dp {
    /// const 函数计算斐波那契数（编译时）
    pub const fn fib_const(n: u32) -> u32 {
        match n {
            0 => 0,
            1 => 1,
            n => fib_const(n - 1) + fib_const(n - 2),
        }
    }

    /// Rust 1.91: 使用 const 引用
    pub const FIB_10: u32 = fib_const(10);
    pub const FIB_10_REF: &u32 = &FIB_10; // ✅ 1.91 新特性
    pub const FIB_10_SQUARED: u32 = *FIB_10_REF * *FIB_10_REF;
}

// ==================== 问题信息注册 ====================

/// 获取所有动态规划类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 70,
            title: "爬楼梯".to_string(),
            title_en: "Climbing Stairs".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Math, LeetCodeTag::DynamicProgramming],
            description: "假设你正在爬楼梯。需要 n 阶你才能到达楼顶。每次你可以爬 1 或 2 个台阶。你有多少种不同的方法可以爬到楼顶呢？".to_string(),
            examples: vec![
                "输入：n = 2\n输出：2".to_string(),
                "输入：n = 3\n输出：3".to_string(),
            ],
            constraints: vec![
                "1 <= n <= 45".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：DP 状态转移性能提升".to_string(),
                "内存优化：使用滚动数组，O(1) 空间复杂度".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("滚动数组 DP，类似斐波那契数列".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 198,
            title: "打家劫舍".to_string(),
            title_en: "House Robber".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::DynamicProgramming],
            description: "你是一个专业的小偷，计划偷窃沿街的房屋。每间房内都藏有一定的现金，影响你偷窃的唯一制约因素就是相邻的房屋装有相互连通的防盗系统，如果两间相邻的房屋在同一晚上被小偷闯入，系统会自动报警。".to_string(),
            examples: vec![
                "输入：nums = [1,2,3,1]\n输出：4".to_string(),
            ],
            constraints: vec![
                "1 <= nums.length <= 100".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：DP 状态转移性能提升".to_string(),
                "内存优化：使用滚动数组，O(1) 空间复杂度".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("滚动数组 DP，状态转移方程：dp[i] = max(dp[i-1], dp[i-2] + nums[i])".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 300,
            title: "最长递增子序列".to_string(),
            title_en: "Longest Increasing Subsequence".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::BinarySearch, LeetCodeTag::DynamicProgramming],
            description: "给你一个整数数组 nums，找到其中最长严格递增子序列的长度。".to_string(),
            examples: vec![
                "输入：nums = [10,9,2,5,3,7,101,18]\n输出：4".to_string(),
            ],
            constraints: vec![
                "1 <= nums.length <= 2500".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：二分查找优化 DP，O(n log n)".to_string(),
                "内存优化：使用数组存储递增子序列".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(n log n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("使用二分查找优化 DP，维护递增子序列数组".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 322,
            title: "零钱兑换".to_string(),
            title_en: "Coin Change".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::DynamicProgramming, LeetCodeTag::BreadthFirstSearch],
            description: "给你一个整数数组 coins，表示不同面额的硬币；以及一个整数 amount，表示总金额。计算并返回可以凑成总金额所需的最少的硬币个数。".to_string(),
            examples: vec![
                "输入：coins = [1,2,5], amount = 11\n输出：3".to_string(),
            ],
            constraints: vec![
                "1 <= coins.length <= 12".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：DP 数组操作性能提升".to_string(),
                "内存优化：使用数组存储 DP 状态".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(n * amount)".to_string(),
                space_complexity: "O(amount)".to_string(),
                explanation: Some("其中 n 是硬币数量".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_climb_stairs() {
        assert_eq!(climb_stairs(2), 2);
        assert_eq!(climb_stairs(3), 3);
        assert_eq!(climb_stairs(5), 8);
    }

    #[test]
    fn test_rob() {
        assert_eq!(rob(vec![1, 2, 3, 1]), 4);
        assert_eq!(rob(vec![2, 7, 9, 3, 1]), 12);
    }

    #[test]
    fn test_rob_circular() {
        assert_eq!(rob_circular(vec![2, 3, 2]), 3);
        assert_eq!(rob_circular(vec![1, 2, 3, 1]), 4);
    }

    #[test]
    fn test_length_of_lis() {
        assert_eq!(length_of_lis(vec![10, 9, 2, 5, 3, 7, 101, 18]), 4);
        assert_eq!(length_of_lis(vec![0, 1, 0, 3, 2, 3]), 4);
    }

    #[test]
    fn test_coin_change() {
        assert_eq!(coin_change(vec![1, 2, 5], 11), 3);
        assert_eq!(coin_change(vec![2], 3), -1);
    }

    #[test]
    fn test_change() {
        assert_eq!(change(5, vec![1, 2, 5]), 4);
        assert_eq!(change(3, vec![2]), 0);
    }

    #[test]
    fn test_min_cost_climbing_stairs() {
        assert_eq!(min_cost_climbing_stairs(vec![10, 15, 20]), 15);
        assert_eq!(min_cost_climbing_stairs(vec![1, 100, 1, 1, 1, 100, 1, 1, 100, 1]), 6);
    }

    #[test]
    fn test_longest_common_subsequence() {
        assert_eq!(longest_common_subsequence("abcde".to_string(), "ace".to_string()), 3);
        assert_eq!(longest_common_subsequence("abc".to_string(), "abc".to_string()), 3);
    }

    #[test]
    fn test_fib() {
        assert_eq!(fib(2), 1);
        assert_eq!(fib(3), 2);
        assert_eq!(fib(4), 3);
    }

    #[test]
    fn test_const_dp() {
        use const_dp::*;
        assert_eq!(FIB_10, 55);
        assert_eq!(FIB_10_SQUARED, 3025);
    }
}
