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

// =========================
// 快速幂（幂/矩阵幂骨架）
// =========================

pub fn fast_pow_mod(mut base: u64, mut exp: u64, modu: u64) -> u64 {
    if modu == 1 { return 0; }
    let mut res = 1u64 % modu;
    base %= modu;
    while exp > 0 {
        if exp & 1 == 1 { res = res.wrapping_mul(base) % modu; }
        base = base.wrapping_mul(base) % modu;
        exp >>= 1;
    }
    res
}

pub async fn fast_pow_mod_async(base: u64, exp: u64, modu: u64) -> Result<u64> {
    Ok(tokio::task::spawn_blocking(move || fast_pow_mod(base, exp, modu)).await?)
}

// 快速矩阵幂（方阵乘法 + 幂），用于线性递推加速
#[derive(Clone, Debug, PartialEq)]
pub struct Matrix {
    pub n: usize,
    pub a: Vec<Vec<u64>>, // 简化：使用 u64 与取模外传
}

impl Matrix {
    pub fn identity(n: usize) -> Self {
        let mut a = vec![vec![0u64; n]; n];
        for i in 0..n { a[i][i] = 1; }
        Self { n, a }
    }

    pub fn mul_mod(&self, other: &Self, modu: u64) -> Self {
        let n = self.n; assert_eq!(n, other.n);
        let mut c = vec![vec![0u64; n]; n];
        for i in 0..n {
            for k in 0..n {
                let vik = self.a[i][k] % modu;
                if vik == 0 { continue; }
                for j in 0..n {
                    c[i][j] = (c[i][j] + vik.wrapping_mul(other.a[k][j] % modu)) % modu;
                }
            }
        }
        Self { n, a: c }
    }

    pub fn pow_mod(&self, mut e: u64, modu: u64) -> Self {
        let mut base = self.clone();
        let mut res = Matrix::identity(self.n);
        while e > 0 {
            if e & 1 == 1 { res = res.mul_mod(&base, modu); }
            base = base.mul_mod(&base, modu);
            e >>= 1;
        }
        res
    }
}

pub async fn matrix_pow_mod_async(m: Matrix, e: u64, modu: u64) -> Result<Matrix> {
    Ok(tokio::task::spawn_blocking(move || m.pow_mod(e, modu)).await?)
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

    #[test]
    fn test_fast_pow_mod() {
        assert_eq!(fast_pow_mod(2, 10, 1_000_000_007), 1024);
        assert_eq!(fast_pow_mod(123456789, 0, 97), 1 % 97);
    }

    #[test]
    fn test_matrix_pow() {
        // 斐波那契矩阵 [[1,1],[1,0]]^n 乘以 [F1,F0]^T 生成 [F_{n+1}, F_n]
        let fib = Matrix { n: 2, a: vec![vec![1,1], vec![1,0]] };
        let modu = 1_000_000_007u64;
        let m = fib.pow_mod(10, modu); // F_10 = 55
        // m 应该等于 [[F_{11}, F_{10}], [F_{10}, F_9]] = [[89,55],[55,34]]
        assert_eq!(m.a[0][1], 55);
        assert_eq!(m.a[1][0], 55);
    }
}

