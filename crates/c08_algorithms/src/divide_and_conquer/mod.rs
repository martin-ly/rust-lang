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

    Segment {
        best,
        prefix,
        suffix,
        sum,
    }
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
    let chunks: Vec<Segment> = nums.par_chunks(16_384).map(segment_from_slice).collect();
    if chunks.is_empty() {
        return i64::MIN;
    }
    let total = chunks.into_iter().reduce(merge_segment).unwrap_or(Segment {
        best: i64::MIN,
        prefix: i64::MIN,
        suffix: i64::MIN,
        sum: 0,
    });
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

fn dist(a: Point, b: Point) -> f64 {
    ((a.x - b.x).powi(2) + (a.y - b.y).powi(2)).sqrt()
}

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
        for j in i + 1..m.min(i + 7) {
            // 理论上检查后续最多 6 个
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
    if modu == 1 {
        return 0;
    }
    let mut res = 1u64 % modu;
    base %= modu;
    while exp > 0 {
        if exp & 1 == 1 {
            res = res.wrapping_mul(base) % modu;
        }
        base = base.wrapping_mul(base) % modu;
        exp >>= 1;
    }
    res
}

pub async fn fast_pow_mod_async(base: u64, exp: u64, modu: u64) -> Result<u64> {
    Ok(tokio::task::spawn_blocking(move || fast_pow_mod(base, exp, modu)).await?)
}

// Quickselect：第 k 小（0-based）
pub fn quickselect_kth<T: Ord>(data: &mut [T], k: usize) -> Option<&T> {
    if k >= data.len() {
        return None;
    }
    let mut l = 0usize;
    let mut r = data.len() - 1;
    loop {
        let p = partition(data, l, r);
        if k == p {
            break;
        }
        if k < p {
            if p == 0 {
                break;
            }
            r = p - 1;
        } else {
            l = p + 1;
        }
    }
    Some(&data[k])
}

fn partition<T: Ord>(a: &mut [T], l: usize, r: usize) -> usize {
    let mut i = l;
    for j in l..r {
        if a[j] <= a[r] {
            a.swap(i, j);
            i += 1;
        }
    }
    a.swap(i, r);
    i
}

// Karatsuba 大整数乘（字符串十进制简化演示：返回去除前导零的积字符串）
#[allow(dead_code)]
pub fn karatsuba_mul(a: &str, b: &str) -> String {
    fn strip(s: &str) -> &str {
        let s2 = s.trim_start_matches('0');
        if s2.is_empty() { "0" } else { s2 }
    }
    fn add_str(x: &str, y: &str) -> String {
        let (xb, yb) = (x.as_bytes(), y.as_bytes());
        let (mut i, mut j, mut carry) = (xb.len() as isize - 1, yb.len() as isize - 1, 0i32);
        let mut out = Vec::new();
        while i >= 0 || j >= 0 || carry > 0 {
            let xi = if i >= 0 {
                (xb[i as usize] - b'0') as i32
            } else {
                0
            };
            let yj = if j >= 0 {
                (yb[j as usize] - b'0') as i32
            } else {
                0
            };
            let s = xi + yj + carry;
            out.push((s % 10) as u8 + b'0');
            carry = s / 10;
            i -= 1;
            j -= 1;
        }
        out.reverse();
        String::from_utf8(out).unwrap()
    }
    fn sub_str(x: &str, y: &str) -> String {
        // assume x>=y
        let (xb, yb) = (x.as_bytes(), y.as_bytes());
        let (mut i, mut j, mut borrow) = (xb.len() as isize - 1, yb.len() as isize - 1, 0i32);
        let mut out = Vec::new();
        while i >= 0 {
            let xi = (xb[i as usize] - b'0') as i32 - borrow;
            let yj = if j >= 0 {
                (yb[j as usize] - b'0') as i32
            } else {
                0
            };
            let mut d = xi - yj;
            if d < 0 {
                d += 10;
                borrow = 1;
            } else {
                borrow = 0;
            }
            out.push((d as u8) + b'0');
            i -= 1;
            j -= 1;
        }
        while out.len() > 1 && *out.last().unwrap() == b'0' {
            out.pop();
        }
        out.reverse();
        String::from_utf8(out).unwrap()
    }
    fn mul_small(a: &str, b: &str) -> String {
        if a.len() <= 32 && b.len() <= 32 {
            let ai: u128 = a.parse().unwrap_or(0);
            let bi: u128 = b.parse().unwrap_or(0);
            return (ai * bi).to_string();
        }
        karatsuba(a, b)
    }
    fn karatsuba(a: &str, b: &str) -> String {
        let (a, b) = (strip(a), strip(b));
        if a == "0" || b == "0" {
            return "0".to_string();
        }
        let n = a.len().max(b.len());
        if n <= 32 {
            return mul_grade_school(a, b);
        }
        let m = n / 2;
        let (a0, a1) = split_pad(a, m);
        let (b0, b1) = split_pad(b, m);
        let z0 = karatsuba(a0, b0);
        let z2 = karatsuba(a1, b1);
        let s1 = add_str(a0, a1);
        let s2 = add_str(b0, b1);
        let z1 = karatsuba(&s1, &s2);
        let mid = sub_str(&sub_str(&z1, &z0), &z2);
        add_str(&add_shift(&z2, 2 * m), &add_str(&add_shift(&mid, m), &z0))
    }
    fn mul_grade_school(a: &str, b: &str) -> String {
        let (a, b) = (a.as_bytes(), b.as_bytes());
        let mut prod = vec![0u32; a.len() + b.len()];
        for i in (0..a.len()).rev() {
            for j in (0..b.len()).rev() {
                let ai = (a[i] - b'0') as u32;
                let bj = (b[j] - b'0') as u32;
                let p = ai * bj + prod[i + j + 1];
                prod[i + j + 1] = p % 10;
                prod[i + j] += p / 10;
            }
        }
        let mut i = 0;
        while i + 1 < prod.len() && prod[i] == 0 {
            i += 1;
        }
        let s: String = prod[i..]
            .iter()
            .map(|&d| (d as u8 + b'0') as char)
            .collect();
        s
    }
    fn split_pad(s: &str, m: usize) -> (&str, &str) {
        let l = s.len();
        if l <= m {
            ("0", s)
        } else {
            (&s[..l - m], &s[l - m..])
        }
    }
    fn add_shift(s: &str, k: usize) -> String {
        let mut out = s.to_string();
        out.extend(std::iter::repeat_n('0', k));
        out
    }
    strip(&karatsuba(a, b)).to_string()
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
        for i in 0..n {
            a[i][i] = 1;
        }
        Self { n, a }
    }

    pub fn mul_mod(&self, other: &Self, modu: u64) -> Self {
        let n = self.n;
        assert_eq!(n, other.n);
        let mut c = vec![vec![0u64; n]; n];
        for i in 0..n {
            for k in 0..n {
                let vik = self.a[i][k] % modu;
                if vik == 0 {
                    continue;
                }
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
            if e & 1 == 1 {
                res = res.mul_mod(&base, modu);
            }
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
        let nums = vec![-2, 1, -3, 4, -1, 2, 1, -5, 4];
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
    fn test_quickselect_and_karatsuba() {
        let mut v = vec![7, 2, 5, 3, 9, 1, 6, 4, 8];
        let kth = quickselect_kth(&mut v, 4).copied().unwrap();
        assert_eq!(kth, 5);
        assert_eq!(
            karatsuba_mul("12345678901234567890", "9876543210"),
            (12345678901234567890u128 * 9876543210u128).to_string()
        );
    }

    #[test]
    fn test_matrix_pow() {
        // 斐波那契矩阵 [[1,1],[1,0]]^n 乘以 [F1,F0]^T 生成 [F_{n+1}, F_n]
        let fib = Matrix {
            n: 2,
            a: vec![vec![1, 1], vec![1, 0]],
        };
        let modu = 1_000_000_007u64;
        let m = fib.pow_mod(10, modu); // F_10 = 55
        // m 应该等于 [[F_{11}, F_{10}], [F_{10}, F_9]] = [[89,55],[55,34]]
        assert_eq!(m.a[0][1], 55);
        assert_eq!(m.a[1][0], 55);
    }
}
