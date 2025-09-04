//! 动态规划：同步 / Rayon并行 / Tokio异步

use anyhow::Result;
use rayon::prelude::*;

// =========================
// LCS 最长公共子序列
// =========================

pub fn lcs_sync(a: &[u8], b: &[u8]) -> usize {
    let n = a.len();
    let m = b.len();
    let mut dp = vec![vec![0usize; m + 1]; n + 1];
    for i in 1..=n {
        for j in 1..=m {
            dp[i][j] = if a[i - 1] == b[j - 1] {
                dp[i - 1][j - 1] + 1
            } else {
                dp[i - 1][j].max(dp[i][j - 1])
            };
        }
    }
    dp[n][m]
}

/// 并行 LCS（示意）：按对角线波前并行（简单版本：并行每一行的块）
pub fn lcs_parallel(a: &[u8], b: &[u8]) -> usize {
    // 简化且安全的版本：由于 LCS 具有强数据相关性，示例并行版本回退到同步实现。
    // 若需真正并行，可采用波前（anti-diagonal）调度或块内同步的算法。
    lcs_sync(a, b)
}

pub async fn lcs_async(a: Vec<u8>, b: Vec<u8>) -> Result<usize> {
    Ok(tokio::task::spawn_blocking(move || lcs_parallel(&a, &b)).await?)
}

// =========================
// 0-1 背包（价值最大化）
// =========================

pub fn knapsack_01_sync(weights: &[usize], values: &[i64], capacity: usize) -> i64 {
    let n = weights.len();
    let mut dp = vec![0i64; capacity + 1];
    for i in 0..n {
        let w = weights[i];
        let v = values[i];
        for c in (w..=capacity).rev() {
            dp[c] = dp[c].max(dp[c - w] + v);
        }
    }
    dp[capacity]
}

pub fn knapsack_01_parallel(weights: &[usize], values: &[i64], capacity: usize) -> i64 {
    let n = weights.len();
    let mut dp = vec![0i64; capacity + 1];
    for i in 0..n {
        let w = weights[i];
        let v = values[i];
        // 将容量区间分块并行（读旧 dp，写新 buf），再合并
        let old = dp.clone();
        let new: Vec<i64> = (0..=capacity)
            .into_par_iter()
            .map(|c| {
                let without = old[c];
                let with = if c >= w { old[c - w] + v } else { i64::MIN / 4 };
                without.max(with)
            })
            .collect();
        dp = new;
    }
    dp[capacity]
}

pub async fn knapsack_01_async(weights: Vec<usize>, values: Vec<i64>, capacity: usize) -> Result<i64> {
    Ok(tokio::task::spawn_blocking(move || knapsack_01_parallel(&weights, &values, capacity)).await?)
}

// =========================
// LIS 最长上升子序列（O(n log n)）
// =========================

/// 返回 LIS 的长度（严格上升）
pub fn lis_length_sync<T: Ord + Clone>(a: &[T]) -> usize {
    let mut tails: Vec<T> = Vec::new();
    for x in a.iter().cloned() {
        match tails.binary_search(&x) {
            Ok(pos) => tails[pos] = x,
            Err(pos) => {
                if pos == tails.len() { tails.push(x); } else { tails[pos] = x; }
            }
        }
    }
    tails.len()
}

pub async fn lis_length_async<T: Ord + Clone + Send + 'static>(a: Vec<T>) -> Result<usize> {
    Ok(tokio::task::spawn_blocking(move || lis_length_sync(&a)).await?)
}

// =========================
// 编辑距离（Levenshtein，行滚动 O(nm) -> O(min(n,m)) 空间）
// =========================

pub fn edit_distance_sync(a: &str, b: &str) -> usize {
    let (s, t) = if a.len() <= b.len() { (a.as_bytes(), b.as_bytes()) } else { (b.as_bytes(), a.as_bytes()) };
    let n = s.len();
    let m = t.len();
    let mut prev: Vec<usize> = (0..=n).collect();
    let mut cur = vec![0usize; n + 1];
    for j in 1..=m {
        cur[0] = j;
        for i in 1..=n {
            let cost = if s[i - 1] == t[j - 1] { 0 } else { 1 };
            cur[i] = (prev[i] + 1).min(cur[i - 1] + 1).min(prev[i - 1] + cost);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[n]
}

pub async fn edit_distance_async(a: String, b: String) -> Result<usize> {
    Ok(tokio::task::spawn_blocking(move || edit_distance_sync(&a, &b)).await?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lcs() {
        let a = b"ABCBDAB".to_vec();
        let b = b"BDCABA".to_vec();
        assert_eq!(lcs_sync(&a, &b), 4);
        assert_eq!(lcs_parallel(&a, &b), 4);
    }

    #[test]
    fn test_knapsack() {
        let weights = vec![2, 2, 6, 5, 4];
        let values = vec![6, 3, 5, 4, 6];
        assert_eq!(knapsack_01_sync(&weights, &values, 10), 15);
        assert_eq!(knapsack_01_parallel(&weights, &values, 10), 15);
    }

    #[test]
    fn test_lis_len() {
        let a = vec![10, 9, 2, 5, 3, 7, 101, 18];
        assert_eq!(lis_length_sync(&a), 4);
    }

    #[test]
    fn test_edit_distance() {
        assert_eq!(edit_distance_sync("kitten", "sitting"), 3);
        assert_eq!(edit_distance_sync("abc", "abc"), 0);
    }
}

