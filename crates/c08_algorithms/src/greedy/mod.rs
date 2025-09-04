//! 贪心算法：同步 / Rayon并行 / Tokio异步

use anyhow::Result;
use rayon::prelude::*;

// =========================
// 区间调度（最大不重叠区间数）
// =========================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Interval {
    pub start: i64,
    pub end: i64,
}

/// 同步：按结束时间排序选择
pub fn interval_scheduling_sync(mut intervals: Vec<Interval>) -> Vec<Interval> {
    intervals.sort_by_key(|iv| iv.end);
    let mut result = Vec::new();
    let mut current_end = i64::MIN;
    for iv in intervals {
        if iv.start >= current_end {
            result.push(iv);
            current_end = iv.end;
        }
    }
    result
}

/// 并行：并行排序后线性选择
pub fn interval_scheduling_parallel(mut intervals: Vec<Interval>) -> Vec<Interval> {
    intervals.par_sort_unstable_by_key(|iv| iv.end);
    let mut result = Vec::new();
    let mut current_end = i64::MIN;
    for iv in intervals {
        if iv.start >= current_end {
            result.push(iv);
            current_end = iv.end;
        }
    }
    result
}

/// 异步：spawn_blocking 包裹
pub async fn interval_scheduling_async(intervals: Vec<Interval>) -> Result<Vec<Interval>> {
    Ok(tokio::task::spawn_blocking(move || interval_scheduling_parallel(intervals)).await?)
}

// =========================
// 零钱兑换（最少硬币数，贪心对部分币值系统正确）
// =========================

/// 同步：对标准币值系统（如美分）正确
pub fn coin_change_greedy_sync(mut coins: Vec<i64>, mut amount: i64) -> Vec<i64> {
    coins.sort_unstable();
    coins.reverse();
    let mut res = Vec::new();
    for c in coins {
        while amount >= c {
            amount -= c;
            res.push(c);
        }
        if amount == 0 { break; }
    }
    res
}

/// 并行：并行预处理（排序），选择仍为线性
pub fn coin_change_greedy_parallel(mut coins: Vec<i64>, amount: i64) -> Vec<i64> {
    coins.par_sort_unstable();
    let coins: Vec<i64> = coins.into_iter().rev().collect();
    coin_change_greedy_sync(coins, amount)
}

/// 异步：spawn_blocking 包裹
pub async fn coin_change_greedy_async(coins: Vec<i64>, amount: i64) -> Result<Vec<i64>> {
    Ok(tokio::task::spawn_blocking(move || coin_change_greedy_parallel(coins, amount)).await?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_interval_scheduling() {
        let intervals = vec![
            Interval { start: 1, end: 3 },
            Interval { start: 2, end: 4 },
            Interval { start: 3, end: 5 },
            Interval { start: 0, end: 7 },
            Interval { start: 5, end: 9 },
        ];
        let r1 = interval_scheduling_sync(intervals.clone());
        let r2 = interval_scheduling_parallel(intervals.clone());
        assert_eq!(r1.len(), r2.len());
        assert!(!r1.is_empty());
    }

    #[test]
    fn test_coin_change_greedy() {
        let coins = vec![1, 5, 10, 25];
        let r1 = coin_change_greedy_sync(coins.clone(), 41);
        assert_eq!(r1.iter().sum::<i64>(), 41);
        assert!(r1.len() <= 5);

        let r2 = coin_change_greedy_parallel(coins.clone(), 41);
        assert_eq!(r2.iter().sum::<i64>(), 41);
    }

    #[test]
    fn test_async_wrappers() {
        let rt = tokio::runtime::Runtime::new().unwrap();
        let intervals = vec![Interval { start: 1, end: 2 }, Interval { start: 2, end: 3 }];
        let res = rt.block_on(async { interval_scheduling_async(intervals).await.unwrap() });
        assert!(!res.is_empty());

        let coins = vec![1, 2, 5, 10];
        let r = rt.block_on(async { coin_change_greedy_async(coins, 18).await.unwrap() });
        assert_eq!(r.iter().sum::<i64>(), 18);
    }
}

