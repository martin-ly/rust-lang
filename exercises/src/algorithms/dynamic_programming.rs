//! # 动态规划练习 / Dynamic Programming Exercises
//!
//! 本模块包含经典 DP 问题的实现与练习：
//! - 0/1 背包
//! - 完全背包
//! - 最长递增子序列 (LIS)
//! - 最长公共子序列 (LCS)
//! - 最小编辑距离
//! - 零钱兑换
//! - 最大子数组和 (Kadane)
//! - 爬楼梯

/// 0/1 背包：在容量为 capacity 的背包中装入最大价值。
/// weights 与 values 长度相同，每个物品只能选一次。
pub fn knapsack_01(weights: &[usize], values: &[usize], capacity: usize) -> usize {
    let n = weights.len();
    let mut dp = vec![0usize; capacity + 1];

    for i in 0..n {
        let w = weights[i];
        let v = values[i];
        if w == 0 {
            continue;
        }
        for c in (w..=capacity).rev() {
            dp[c] = dp[c].max(dp[c - w] + v);
        }
    }
    dp[capacity]
}

/// 完全背包：每种物品有无限件，求恰好或不超过容量时的最大价值。
pub fn unbounded_knapsack(weights: &[usize], values: &[usize], capacity: usize) -> usize {
    let n = weights.len();
    let mut dp = vec![0usize; capacity + 1];

    for i in 0..n {
        let w = weights[i];
        let v = values[i];
        if w == 0 {
            continue;
        }
        for c in w..=capacity {
            dp[c] = dp[c].max(dp[c - w] + v);
        }
    }
    dp[capacity]
}

/// 最长递增子序列长度。
pub fn length_of_lis(nums: &[i32]) -> usize {
    if nums.is_empty() {
        return 0;
    }
    let mut tails = Vec::new();
    for &num in nums {
        match tails.binary_search(&num) {
            Ok(pos) | Err(pos) => {
                if pos == tails.len() {
                    tails.push(num);
                } else {
                    tails[pos] = num;
                }
            }
        }
    }
    tails.len()
}

/// 最长公共子序列长度。
pub fn longest_common_subsequence(text1: &str, text2: &str) -> usize {
    let s1: Vec<char> = text1.chars().collect();
    let s2: Vec<char> = text2.chars().collect();
    let m = s1.len();
    let n = s2.len();
    let mut prev = vec![0usize; n + 1];
    let mut curr = vec![0usize; n + 1];

    for i in 1..=m {
        for j in 1..=n {
            if s1[i - 1] == s2[j - 1] {
                curr[j] = prev[j - 1] + 1;
            } else {
                curr[j] = curr[j - 1].max(prev[j]);
            }
        }
        std::mem::swap(&mut prev, &mut curr);
    }
    prev[n]
}

/// 最小编辑距离：将 word1 转换为 word2 所需的最少操作数。
pub fn min_edit_distance(word1: &str, word2: &str) -> usize {
    let s1: Vec<char> = word1.chars().collect();
    let s2: Vec<char> = word2.chars().collect();
    let m = s1.len();
    let n = s2.len();
    let mut prev = (0..=n).collect::<Vec<usize>>();
    let mut curr = vec![0usize; n + 1];

    for i in 1..=m {
        curr[0] = i;
        for j in 1..=n {
            if s1[i - 1] == s2[j - 1] {
                curr[j] = prev[j - 1];
            } else {
                curr[j] = 1 + curr[j - 1].min(prev[j]).min(prev[j - 1]);
            }
        }
        std::mem::swap(&mut prev, &mut curr);
    }
    prev[n]
}

/// 零钱兑换：凑成金额 amount 所需的最少硬币数，无法凑成返回 None。
pub fn coin_change(coins: &[i32], amount: i32) -> Option<i32> {
    if amount < 0 {
        return None;
    }
    let amount = amount as usize;
    let mut dp = vec![i32::MAX; amount + 1];
    dp[0] = 0;

    for &coin in coins {
        if coin <= 0 {
            continue;
        }
        let coin = coin as usize;
        for a in coin..=amount {
            if dp[a - coin] != i32::MAX {
                dp[a] = dp[a].min(dp[a - coin] + 1);
            }
        }
    }

    if dp[amount] == i32::MAX {
        None
    } else {
        Some(dp[amount])
    }
}

/// 最大子数组和（Kadane 算法）。
pub fn max_subarray_sum(nums: &[i32]) -> i32 {
    if nums.is_empty() {
        return 0;
    }
    let mut max_ending_here = nums[0];
    let mut max_so_far = nums[0];
    for &num in &nums[1..] {
        max_ending_here = num.max(max_ending_here + num);
        max_so_far = max_so_far.max(max_ending_here);
    }
    max_so_far
}

/// 爬楼梯：爬到第 n 阶的方法数（每次可爬 1 或 2 阶）。
pub fn climb_stairs(n: usize) -> usize {
    if n == 0 {
        return 1;
    }
    if n == 1 {
        return 1;
    }
    let mut prev2 = 1usize;
    let mut prev1 = 1usize;
    for _ in 2..=n {
        let curr = prev1 + prev2;
        prev2 = prev1;
        prev1 = curr;
    }
    prev1
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_knapsack_01() {
        let weights = vec![1, 3, 4, 5];
        let values = vec![1, 4, 5, 7];
        assert_eq!(knapsack_01(&weights, &values, 7), 9);
    }

    #[test]
    fn test_knapsack_01_empty() {
        assert_eq!(knapsack_01(&[], &[], 10), 0);
    }

    #[test]
    fn test_unbounded_knapsack() {
        let weights = vec![1, 3, 4, 5];
        let values = vec![10, 40, 50, 70];
        assert_eq!(unbounded_knapsack(&weights, &values, 8), 110);
    }

    #[test]
    fn test_length_of_lis() {
        assert_eq!(length_of_lis(&[10, 9, 2, 5, 3, 7, 101, 18]), 4);
        assert_eq!(length_of_lis(&[0, 1, 0, 3, 2, 3]), 4);
        assert_eq!(length_of_lis(&[]), 0);
    }

    #[test]
    fn test_longest_common_subsequence() {
        assert_eq!(longest_common_subsequence("abcde", "ace"), 3);
        assert_eq!(longest_common_subsequence("abc", "abc"), 3);
        assert_eq!(longest_common_subsequence("abc", "def"), 0);
    }

    #[test]
    fn test_min_edit_distance() {
        assert_eq!(min_edit_distance("horse", "ros"), 3);
        assert_eq!(min_edit_distance("intention", "execution"), 5);
        assert_eq!(min_edit_distance("", "abc"), 3);
    }

    #[test]
    fn test_coin_change() {
        assert_eq!(coin_change(&[1, 2, 5], 11), Some(3));
        assert_eq!(coin_change(&[2], 3), None);
        assert_eq!(coin_change(&[1], 0), Some(0));
    }

    #[test]
    fn test_max_subarray_sum() {
        assert_eq!(max_subarray_sum(&[-2, 1, -3, 4, -1, 2, 1, -5, 4]), 6);
        assert_eq!(max_subarray_sum(&[1]), 1);
        assert_eq!(max_subarray_sum(&[-1, -2, -3]), -1);
    }

    #[test]
    fn test_climb_stairs() {
        assert_eq!(climb_stairs(2), 2);
        assert_eq!(climb_stairs(3), 3);
        assert_eq!(climb_stairs(0), 1);
    }
}
