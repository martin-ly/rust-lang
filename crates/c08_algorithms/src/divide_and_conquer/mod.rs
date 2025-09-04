//! 分治算法：同步 / Rayon并行 / Tokio异步

use anyhow::Result;
use rayon::prelude::*;

// =========================
// 最大子段和（Kadane/分治）
// =========================

/// 同步：Kadane 线性算法
pub fn max_subarray_sum_sync(nums: &[i64]) -> i64 {
    let mut best = i64::MIN;
    let mut cur = 0i64;
    for &x in nums {
        cur = (cur + x).max(x);
        best = best.max(cur);
    }
    best
}

/// 并行（示意）：分块计算局部 (best, prefix, suffix, sum) 再归并
#[derive(Clone, Copy, Debug)]
struct Segment {
    best: i64,
    prefix: i64,
    suffix: i64,
    sum: i64,
}

fn segment_from_slice(slice: &[i64]) -> Segment {
    let mut prefix = i64::MIN;
    let mut cur = 0;
    for &x in slice {
        cur += x;
        prefix = prefix.max(cur);
    }
    let sum: i64 = slice.iter().copied().sum();

    let mut cur = 0;
    let mut suffix = i64::MIN;
    for &x in slice.iter().rev() {
        cur += x;
        suffix = suffix.max(cur);
    }

    let mut best = i64::MIN;
    let mut cur_max = 0;
    for &x in slice {
        cur_max = (cur_max + x).max(x);
        best = best.max(cur_max);
    }

    Segment { best, prefix, suffix, sum }
}

fn merge_segment(left: Segment, right: Segment) -> Segment {
    Segment {
        best: left.best.max(right.best).max(left.suffix + right.prefix),
        prefix: left.prefix.max(left.sum + right.prefix),
        suffix: right.suffix.max(right.sum + left.suffix),
        sum: left.sum + right.sum,
    }
}

pub fn max_subarray_sum_parallel(nums: &[i64]) -> i64 {
    let chunks: Vec<Segment> = nums
        .par_chunks(16_384)
        .map(segment_from_slice)
        .collect();
    if chunks.is_empty() {
        return i64::MIN;
    }
    let total = chunks
        .into_iter()
        .reduce(merge_segment)
        .unwrap_or(Segment { best: i64::MIN, prefix: i64::MIN, suffix: i64::MIN, sum: 0 });
    total.best
}

/// 异步封装
pub async fn max_subarray_sum_async(nums: Vec<i64>) -> Result<i64> {
    Ok(tokio::task::spawn_blocking(move || max_subarray_sum_parallel(&nums)).await?)
}

// =========================
// 平面最近点对（O(n log n) 分治，简化实现）
// =========================

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

fn dist(a: Point, b: Point) -> f64 { ((a.x - b.x).powi(2) + (a.y - b.y).powi(2)).sqrt() }

pub fn closest_pair_sync(mut pts: Vec<Point>) -> f64 {
    pts.sort_by(|a, b| a.x.partial_cmp(&b.x).unwrap());
    closest_pair_rec(&pts)
}

fn closest_pair_rec(pts: &[Point]) -> f64 {
    let n = pts.len();
    if n <= 3 {
        let mut d = f64::INFINITY;
        for i in 0..n {
            for j in i + 1..n {
                d = d.min(dist(pts[i], pts[j]));
            }
        }
        return d;
    }
    let mid = n / 2;
    let midx = pts[mid].x;
    let dl = closest_pair_rec(&pts[..mid]);
    let dr = closest_pair_rec(&pts[mid..]);
    let mut d = dl.min(dr);

    let mut strip: Vec<Point> = pts
        .iter()
        .copied()
        .filter(|p| (p.x - midx).abs() < d)
        .collect();
    strip.sort_by(|a, b| a.y.partial_cmp(&b.y).unwrap());
    let m = strip.len();
    for i in 0..m {
        for j in i + 1..m.min(i + 7) { // 理论上检查后续最多 6 个
            d = d.min(dist(strip[i], strip[j]));
        }
    }
    d
}

pub fn closest_pair_parallel(mut pts: Vec<Point>) -> f64 {
    // 并行预排序
    pts.par_sort_unstable_by(|a, b| a.x.partial_cmp(&b.x).unwrap());
    // 递归仍采用同步（复杂共享结构），但整体速度受益于预处理
    closest_pair_rec(&pts)
}

pub async fn closest_pair_async(pts: Vec<Point>) -> Result<f64> {
    Ok(tokio::task::spawn_blocking(move || closest_pair_parallel(pts)).await?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_max_subarray_sum() {
        let nums = vec![-2,1,-3,4,-1,2,1,-5,4];
        assert_eq!(max_subarray_sum_sync(&nums), 6);
        assert_eq!(max_subarray_sum_parallel(&nums), 6);
    }

    #[test]
    fn test_closest_pair() {
        let pts = vec![
            Point { x: 0.0, y: 0.0 },
            Point { x: 1.0, y: 0.0 },
            Point { x: 2.0, y: 0.0 },
            Point { x: 2.0, y: 2.0 },
        ];
        let d1 = closest_pair_sync(pts.clone());
        let d2 = closest_pair_parallel(pts);
        assert!((d1 - 1.0).abs() < 1e-9);
        assert!((d2 - 1.0).abs() < 1e-9);
    }
}

