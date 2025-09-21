//! # 动态规划算法模块
//! 
//! 本模块实现了各种动态规划算法。

//use serde::{Serialize, Deserialize};

/// 动态规划算法实现
pub struct DynamicProgrammingAlgorithms;

impl DynamicProgrammingAlgorithms {
    /// 最长公共子序列
    pub fn longest_common_subsequence(text1: &str, text2: &str) -> i32 {
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

    /// 0-1 背包问题
    pub fn knapsack_01(weights: &[i32], values: &[i32], capacity: i32) -> i32 {
        let n = weights.len();
        let mut dp = vec![vec![0; (capacity + 1) as usize]; n + 1];
        
        for i in 1..=n {
            for w in 0..=capacity {
                if weights[i - 1] <= w {
                    dp[i][w as usize] = dp[i - 1][w as usize].max(
                        dp[i - 1][(w - weights[i - 1]) as usize] + values[i - 1]
                    );
                } else {
                    dp[i][w as usize] = dp[i - 1][w as usize];
                }
            }
        }
        
        dp[n][capacity as usize]
    }
}
