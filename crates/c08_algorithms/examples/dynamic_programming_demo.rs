//! 动态规划算法示例
//!
//! 本示例展示C08算法模块的动态规划算法：
//! - 斐波那契数列
//! - 最长公共子序列（LCS）
//! - 0-1背包问题
//!
//! 运行方式:
//! ```bash
//! cargo run --example dynamic_programming_demo
//! ```
fn main() {
    println!("🚀 动态规划算法示例\n");
    println!("{}", "=".repeat(60));

    // 1. 斐波那契数列
    println!("\n📊 斐波那契数列:");
    println!("{}", "-".repeat(60));
    println!("使用动态规划计算斐波那契数列:");
    for i in 0..10 {
        print!("{} ", fibonacci_dp(i));
    }
    println!();

    // 2. 最长公共子序列（LCS）
    println!("\n📊 最长公共子序列（LCS）:");
    println!("{}", "-".repeat(60));
    let s1 = "ABCDGH";
    let s2 = "AEDFHR";
    let lcs = lcs_dp(s1, s2);
    println!("字符串1: {}", s1);
    println!("字符串2: {}", s2);
    println!("LCS长度: {}", lcs);

    // 3. 0-1背包问题
    println!("\n📊 0-1背包问题:");
    println!("{}", "-".repeat(60));
    let weights = vec![2, 3, 4, 5];
    let values = vec![1, 4, 5, 7];
    let capacity = 9;
    let max_value = knapsack_dp(&weights, &values, capacity);
    println!("物品重量: {:?}", weights);
    println!("物品价值: {:?}", values);
    println!("背包容量: {}", capacity);
    println!("最大价值: {}", max_value);

    // 4. 算法说明
    println!("\n💡 动态规划说明:");
    println!("{}", "-".repeat(60));
    println!("  核心思想: 将问题分解为子问题，存储子问题的解");
    println!("  时间复杂度: 通常为O(n²)或O(nm)");
    println!("  空间复杂度: 通常为O(n)或O(nm)");

    println!("\n✅ 动态规划算法演示完成！");
}

/// 使用动态规划计算斐波那契数列
fn fibonacci_dp(n: usize) -> u64 {
    if n <= 1 {
        return n as u64;
    }
    let mut dp = vec![0u64; n + 1];
    dp[0] = 0;
    dp[1] = 1;
    for i in 2..=n {
        dp[i] = dp[i - 1] + dp[i - 2];
    }
    dp[n]
}

/// 最长公共子序列（LCS）
fn lcs_dp(s1: &str, s2: &str) -> usize {
    let s1: Vec<char> = s1.chars().collect();
    let s2: Vec<char> = s2.chars().collect();
    let m = s1.len();
    let n = s2.len();
    let mut dp = vec![vec![0; n + 1]; m + 1];

    for i in 1..=m {
        for j in 1..=n {
            if s1[i - 1] == s2[j - 1] {
                dp[i][j] = dp[i - 1][j - 1] + 1;
            } else {
                dp[i][j] = dp[i - 1][j].max(dp[i][j - 1]);
            }
        }
    }
    dp[m][n]
}

/// 0-1背包问题
fn knapsack_dp(weights: &[usize], values: &[usize], capacity: usize) -> usize {
    let n = weights.len();
    let mut dp = vec![vec![0; capacity + 1]; n + 1];

    for i in 1..=n {
        for w in 0..=capacity {
            if weights[i - 1] > w {
                dp[i][w] = dp[i - 1][w];
            } else {
                dp[i][w] = dp[i - 1][w].max(dp[i - 1][w - weights[i - 1]] + values[i - 1]);
            }
        }
    }
    dp[n][capacity]
}
