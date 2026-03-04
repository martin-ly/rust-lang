# Rust 数据并行模式

> **Rust版本**: 1.93.1
> **覆盖范围**: Rayon并行计算、SIMD向量化、GPU加速、矩阵运算
> **权威参考**: Rayon Documentation, packed_simd crate, Rust-GPU

---

## 目录

- [Rust 数据并行模式](#rust-数据并行模式)
  - [目录](#目录)
  - [1. 并行计算理论](#1-并行计算理论)
    - [1.1 Amdahl定律与Gustafson定律](#11-amdahl定律与gustafson定律)
    - [1.2 并行算法复杂度](#12-并行算法复杂度)
    - [1.3 缓存局部性](#13-缓存局部性)
  - [2. Rayon并行计算](#2-rayon并行计算)
    - [2.1 并行迭代器](#21-并行迭代器)
    - [2.2 Fork-Join模式](#22-fork-join模式)
    - [2.3 并行排序](#23-并行排序)
    - [2.4 自定义分区策略](#24-自定义分区策略)
  - [3. SIMD向量化](#3-simd向量化)
    - [3.1 便携式SIMD](#31-便携式simd)
    - [3.2 向量操作](#32-向量操作)
    - [3.3 矩阵运算](#33-矩阵运算)

---

## 1. 并行计算理论

### 1.1 Amdahl定律与Gustafson定律

```rust
/// Amdahl 定律：
/// S_latency(s) = 1 / ((1 - p) + p/s)
///
/// 其中：
/// - p: 可并行部分的比例
/// - s: 并行部分的加速比
///
/// Gustafson 定律：
/// S_speedup = s - α(s - 1)
///
/// 其中：
/// - α: 串行部分的比例

pub struct SpeedupCalculator;

impl SpeedupCalculator {
    /// 计算 Amdahl 加速比
    pub fn amdahl_speedup(parallel_fraction: f64, processors: usize) -> f64 {
        let p = parallel_fraction;
        let s = processors as f64;
        1.0 / ((1.0 - p) + p / s)
    }

    /// 计算 Gustafson 加速比
    pub fn gustafson_speedup(serial_fraction: f64, processors: usize) -> f64 {
        let alpha = serial_fraction;
        let s = processors as f64;
        s - alpha * (s - 1.0)
    }

    /// 计算最大可能加速比（无限处理器）
    pub fn max_speedup(parallel_fraction: f64) -> f64 {
        1.0 / (1.0 - parallel_fraction)
    }

    /// 计算达到目标加速比所需的最小并行比例
    pub fn required_parallel_fraction(target_speedup: f64, processors: usize) -> f64 {
        let s = processors as f64;
        (target_speedup * (s - 1.0)) / (s * (target_speedup - 1.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_amdahl_law() {
        // 90% 并行，10 个处理器
        let speedup = SpeedupCalculator::amdahl_speedup(0.9, 10);
        println!("90% 并行，10 处理器: {:.2}x 加速", speedup);
        // 理论值约 5.26x
        assert!((speedup - 5.26).abs() < 0.1);
    }

    #[test]
    fn test_max_speedup() {
        // 99% 并行的最大加速比
        let max = SpeedupCalculator::max_speedup(0.99);
        println!("99% 并行的最大加速比: {:.2}x", max);
        // 理论值 100x
        assert!((max - 100.0).abs() < 1.0);
    }
}
```

### 1.2 并行算法复杂度

```rust
/// 并行算法复杂度分析
///
/// Work (W): 总操作数
/// Span (S): 关键路径长度
/// Parallelism = W / S

/// 并行求和的复杂度分析
/// Work: O(n)
/// Span: O(log n)
/// Parallelism: O(n / log n)
pub fn parallel_sum_work_span(n: usize) -> (usize, usize) {
    let work = n; // n 次加法
    let span = (n as f64).log2().ceil() as usize; // 树的高度
    (work, span)
}

/// 并行矩阵乘法的复杂度分析
/// Work: O(n³)
/// Span: O(log n) 使用并行归约
pub fn matrix_multiply_work_span(n: usize) -> (usize, usize) {
    let work = n * n * n;
    let span = (n as f64).log2().ceil() as usize;
    (work, span)
}
```

### 1.3 缓存局部性

```rust
/// 缓存优化原则：
/// 1. 时间局部性：重复访问相同数据
/// 2. 空间局部性：访问相邻数据

/// 缓存友好的矩阵遍历（行优先）
pub fn cache_friendly_matrix_access(matrix: &[Vec<f64>]) -> f64 {
    let n = matrix.len();
    let mut sum = 0.0;

    // ✅ 行优先访问，良好的空间局部性
    for i in 0..n {
        for j in 0..n {
            sum += matrix[i][j];
        }
    }
    sum
}

/// 缓存不友好的矩阵遍历（列优先）
pub fn cache_unfriendly_matrix_access(matrix: &[Vec<f64>]) -> f64 {
    let n = matrix.len();
    let mut sum = 0.0;

    // ❌ 列优先访问，差的缓存局部性
    for j in 0..n {
        for i in 0..n {
            sum += matrix[i][j];
        }
    }
    sum
}

/// 分块（Tiling）优化矩阵乘法
pub fn tiled_matrix_multiply(
    a: &[Vec<f64>],
    b: &[Vec<f64>],
    c: &mut [Vec<f64>],
    tile_size: usize,
) {
    let n = a.len();

    for ii in (0..n).step_by(tile_size) {
        for jj in (0..n).step_by(tile_size) {
            for kk in (0..n).step_by(tile_size) {
                // 处理一个 tile
                for i in ii..(ii + tile_size).min(n) {
                    for j in jj..(jj + tile_size).min(n) {
                        for k in kk..(kk + tile_size).min(n) {
                            c[i][j] += a[i][k] * b[k][j];
                        }
                    }
                }
            }
        }
    }
}

/// 缓存行对齐
#[repr(align(64))] // 64 字节对齐（典型缓存行大小）
pub struct CacheAligned<T>(pub T);

/// 伪共享避免
use std::sync::atomic::AtomicU64;

/// ❌ 可能产生伪共享
pub struct FalseSharingCounter {
    counters: Vec<AtomicU64>, // 相邻计数器可能在同一缓存行
}

/// ✅ 避免伪共享
pub struct CachePaddedCounter {
    counters: Vec<CacheAligned<AtomicU64>>,
}
```

---

## 2. Rayon并行计算

### 2.1 并行迭代器

```rust
use rayon::prelude::*;

/// 基础并行迭代
pub fn basic_parallel_iter(data: &[i32]) -> i32 {
    data.par_iter().sum()
}

/// 并行映射
pub fn parallel_map(data: &[i32]) -> Vec<i32> {
    data.par_iter()
        .map(|&x| x * x)
        .collect()
}

/// 并行过滤
pub fn parallel_filter(data: &[i32]) -> Vec<&i32> {
    data.par_iter()
        .filter(|&&x| x % 2 == 0)
        .collect()
}

/// 并行 reduce
pub fn parallel_reduce(data: &[i32]) -> i32 {
    data.par_iter()
        .copied()
        .reduce(|| 0, |a, b| a + b)
}

/// 自定义 reduce
pub fn parallel_product(data: &[f64]) -> f64 {
    data.par_iter()
        .copied()
        .reduce(|| 1.0, |a, b| a * b)
}

/// 并行字符串处理
pub fn parallel_string_processing(lines: &[String]) -> Vec<usize> {
    lines.par_iter()
        .map(|line| line.len())
        .collect()
}

/// 并行转换并合并结果
pub fn parallel_flat_map(words: &[String]) -> Vec<char> {
    words.par_iter()
        .flat_map(|word| word.chars().collect::<Vec<_>>())
        .collect()
}

/// 并行分组
use std::collections::HashMap;

pub fn parallel_group_by(data: &[(String, i32)]) -> HashMap<String, Vec<i32>> {
    data.par_iter()
        .fold(
            || HashMap::new(),
            |mut map, (key, value)| {
                map.entry(key.clone()).or_default().push(*value);
                map
            },
        )
        .reduce(
            || HashMap::new(),
            |mut a, b| {
                for (key, values) in b {
                    a.entry(key).or_default().extend(values);
                }
                a
            },
        )
}
```

### 2.2 Fork-Join模式

```rust
use rayon::join;

/// 基础 Fork-Join
pub fn fork_join_example(a: i32, b: i32) -> (i32, i32) {
    join(
        || expensive_computation(a),
        || expensive_computation(b),
    )
}

fn expensive_computation(n: i32) -> i32 {
    // 模拟耗时计算
    (0..n).map(|i| i * i).sum()
}

/// 并行快速排序
pub fn parallel_quicksort<T: Ord + Send + Clone>(data: &mut [T]) {
    if data.len() <= 1 {
        return;
    }

    if data.len() <= 1000 {
        // 小数组使用串行排序
        data.sort();
        return;
    }

    let mid = partition(data);
    let (left, right) = data.split_at_mut(mid);

    // 并行递归排序
    join(
        || parallel_quicksort(left),
        || parallel_quicksort(&mut right[1..]),
    );
}

fn partition<T: Ord>(data: &mut [T]) -> usize {
    let len = data.len();
    let pivot_index = len / 2;
    data.swap(pivot_index, len - 1);

    let mut i = 0;
    for j in 0..len - 1 {
        if data[j] <= data[len - 1] {
            data.swap(i, j);
            i += 1;
        }
    }

    data.swap(i, len - 1);
    i
}

/// 并行归并排序
pub fn parallel_mergesort<T: Ord + Send + Clone>(data: &mut [T]) {
    if data.len() <= 1000 {
        data.sort();
        return;
    }

    let mid = data.len() / 2;
    let (left, right) = data.split_at_mut(mid);

    let mut left_sorted = left.to_vec();
    let mut right_sorted = right.to_vec();

    join(
        || parallel_mergesort(&mut left_sorted),
        || parallel_mergesort(&mut right_sorted),
    );

    merge(&left_sorted, &right_sorted, data);
}

fn merge<T: Ord + Clone>(left: &[T], right: &[T], output: &mut [T]) {
    let mut i = 0;
    let mut j = 0;
    let mut k = 0;

    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            output[k] = left[i].clone();
            i += 1;
        } else {
            output[k] = right[j].clone();
            j += 1;
        }
        k += 1;
    }

    while i < left.len() {
        output[k] = left[i].clone();
        i += 1;
        k += 1;
    }

    while j < right.len() {
        output[k] = right[j].clone();
        j += 1;
        k += 1;
    }
}

/// 并行树形归约
pub fn parallel_tree_reduce<T, F>(data: &[T], identity: T, op: F) -> T
where
    T: Send + Clone,
    F: Fn(T, T) -> T + Sync,
{
    if data.len() <= 1000 {
        return data.iter().cloned().fold(identity, &op);
    }

    let mid = data.len() / 2;
    let (left, right) = data.split_at(mid);

    let (l_result, r_result) = join(
        || parallel_tree_reduce(left, identity.clone(), &op),
        || parallel_tree_reduce(right, identity, &op),
    );

    op(l_result, r_result)
}
```

### 2.3 并行排序

```rust
use rayon::slice::ParallelSliceMut;

/// Rayon 内置并行排序
pub fn rayon_parallel_sort(data: &mut [i32]) {
    data.par_sort();
}

/// 并行不稳定性排序（更快）
pub fn rayon_parallel_sort_unstable(data: &mut [i32]) {
    data.par_sort_unstable();
}

/// 自定义比较函数的并行排序
#[derive(Debug, Clone)]
pub struct Person {
    name: String,
    age: u32,
}

pub fn sort_by_age(people: &mut [Person]) {
    people.par_sort_by(|a, b| a.age.cmp(&b.age));
}

pub fn sort_by_name(people: &mut [Person]) {
    people.par_sort_by(|a, b| a.name.cmp(&b.name));
}

/// 多级排序
pub fn multi_key_sort(people: &mut [Person]) {
    people.par_sort_by(|a, b| {
        a.age.cmp(&b.age)
            .then_with(|| a.name.cmp(&b.name))
    });
}

/// 并行去重
pub fn parallel_dedup<T: Eq + Send + Clone>(data: &mut Vec<T>) {
    data.par_sort();
    data.dedup();
}
```

### 2.4 自定义分区策略

```rust
use rayon::iter::plumbing::{Consumer, Producer, ProducerCallback, UnindexedConsumer};
use rayon::iter::{ParallelIterator, IndexedParallelIterator};

/// 自定义并行迭代器：块分区
pub struct BlockParallel<I> {
    inner: I,
    block_size: usize,
}

impl<I: ParallelIterator> ParallelIterator for BlockParallel<I> {
    type Item = I::Item;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        self.inner.drive_unindexed(consumer)
    }
}

/// 基于大小的自适应分区
pub fn adaptive_partition<T, F>(
    data: &[T],
    threshold: usize,
    op: F,
) where
    F: Fn(&[T]) + Sync,
{
    if data.len() <= threshold {
        op(data);
    } else {
        let mid = data.len() / 2;
        let (left, right) = data.split_at(mid);

        rayon::join(
            || adaptive_partition(left, threshold, &op),
            || adaptive_partition(right, threshold, &op),
        );
    }
}

/// 线程池自定义配置
use rayon::ThreadPoolBuilder;

pub fn custom_thread_pool() -> rayon::ThreadPool {
    ThreadPoolBuilder::new()
        .num_threads(8)
        .thread_name(|i| format!("worker-{}", i))
        .stack_size(4 * 1024 * 1024) // 4MB 栈
        .build()
        .unwrap()
}

/// 在自定义线程池中执行
pub fn execute_in_pool<F, T>(pool: &rayon::ThreadPool, f: F) -> T
where
    F: FnOnce() -> T + Send,
    T: Send,
{
    pool.install(f)
}
```

---

## 3. SIMD向量化

### 3.1 便携式SIMD

```rust
#![feature(portable_simd)]

use std::simd::{Simd, LaneCount, SupportedLaneCount};

/// 基础 SIMD 操作
pub fn basic_simd_ops() {
    // 4 个 f32 的向量
    let a = Simd::<f32, 4>::from_array([1.0, 2.0, 3.0, 4.0]);
    let b = Simd::<f32, 4>::from_array([5.0, 6.0, 7.0, 8.0]);

    // 向量加法
    let c = a + b;
    println!("{:?}", c.to_array());

    // 向量乘法
    let d = a * b;
    println!("{:?}", d.to_array());

    // 水平求和
    let sum: f32 = c.reduce_sum();
    println!("Sum: {}", sum);
}

/// 通用 SIMD 函数
pub fn simd_add<const N: usize>(a: &[f32], b: &[f32], c: &mut [f32])
where
    LaneCount<N>: SupportedLaneCount,
{
    let chunks = a.len() / N;

    for i in 0..chunks {
        let va = Simd::<f32, N>::from_slice(&a[i * N..]);
        let vb = Simd::<f32, N>::from_slice(&b[i * N..]);
        let vc = va + vb;
        vc.copy_to_slice(&mut c[i * N..]);
    }

    // 处理剩余元素
    for i in (chunks * N)..a.len() {
        c[i] = a[i] + b[i];
    }
}

/// 自动选择最优 SIMD 宽度
pub fn auto_simd_add(a: &[f32], b: &[f32], c: &mut [f32]) {
    // 根据 CPU 特性选择最佳宽度
    if is_x86_feature_detected!("avx512f") {
        simd_add::<16>(a, b, c);
    } else if is_x86_feature_detected!("avx") {
        simd_add::<8>(a, b, c);
    } else if is_x86_feature_detected!("sse") {
        simd_add::<4>(a, b, c);
    } else {
        // 标量回退
        for i in 0..a.len() {
            c[i] = a[i] + b[i];
        }
    }
}
```

### 3.2 向量操作

```rust
use std::simd::{Simd, LaneCount, SupportedLaneCount};

/// SIMD 点积
pub fn simd_dot_product(a: &[f32], b: &[f32]) -> f32 {
    assert_eq!(a.len(), b.len());

    let mut sum = Simd::<f32, 8>::splat(0.0);

    let chunks = a.len() / 8;
    for i in 0..chunks {
        let va = Simd::<f32, 8>::from_slice(&a[i * 8..]);
        let vb = Simd::<f32, 8>::from_slice(&b[i * 8..]);
        sum += va * vb;
    }

    let mut result = sum.reduce_sum();

    // 处理剩余元素
    for i in (chunks * 8)..a.len() {
        result += a[i] * b[i];
    }

    result
}

/// SIMD 数组求和
pub fn simd_sum(data: &[f32]) -> f32 {
    let mut sum = Simd::<f32, 8>::splat(0.0);

    let chunks = data.len() / 8;
    for i in 0..chunks {
        let v = Simd::<f32, 8>::from_slice(&data[i * 8..]);
        sum += v;
    }

    let mut result = sum.reduce_sum();

    for i in (chunks * 8)..data.len() {
        result += data[i];
    }

    result
}

/// SIMD 查找最大值
pub fn simd_max(data: &[f32]) -> f32 {
    if data.is_empty() {
        return f32::NEG_INFINITY;
    }

    let mut max = Simd::<f32, 8>::splat(f32::NEG_INFINITY);

    let chunks = data.len() / 8;
    for i in 0..chunks {
        let v = Simd::<f32, 8>::from_slice(&data[i * 8..]);
        max = max.simd_max(v);
    }

    let mut result = max.reduce_max();

    for i in (chunks * 8)..data.len() {
        result = result.max(data[i]);
    }

    result
}

/// SIMD 条件选择
pub fn simd_clamp(data: &mut [f32], min: f32, max: f32) {
    let min_vec = Simd::<f32, 8>::splat(min);
    let max_vec = Simd::<f32, 8>::splat(max);

    let chunks = data.len() / 8;
    for i in 0..chunks {
        let v = Simd::<f32, 8>::from_slice(&data[i * 8..]);
        let clamped = v.simd_clamp(min_vec, max_vec);
        clamped.copy_to_slice(&mut data[i * 8..]);
    }

    for i in (chunks * 8)..data.len() {
        data[i] = data[i].clamp(min, max);
    }
}
```

### 3.3 矩阵运算

```rust
use std::simd::{Simd, LaneCount, SupportedLaneCount};

/// SIMD 矩阵乘法（基础版本）
pub fn simd_matrix_multiply(a: &[f32], b: &[f32], c: &mut [f32], n: usize) {
    assert_eq!(a.len(), n * n);
    assert_eq!(b.len(), n * n);
    assert_eq!(c.len(), n * n);

    for i in 0..n {
        for j in 0..n {
            let mut sum = Simd::<f32, 8>::splat(0.0);

            let chunks = n / 8;
            for k in 0..chunks {
                let a_idx = i * n + k * 8;
                let b_idx = (k * 8) * n + j;

                let va = Simd::<f32, 8>::from_slice(&a[a_idx..]);
                // b 需要 gather 操作（简化处理）
                let mut vb_array = [0.0f32; 8];
                for l in 0..8 {
                    vb_array[l] = b[(k * 8 + l) * n + j];
                }
                let vb = Simd::<f32, 8>::from_array(vb_array);

                sum += va * vb;
            }

            c[i * n + j] = sum.reduce_sum();
        }
    }
}

/// SIMD + Rayon 并行矩阵乘法
use rayon::prelude::*;

pub fn parallel_simd_matrix_multiply(a: &[f32], b: &[f32], c: &mut [f32], n: usize) {
    c.par_chunks_mut(n)
        .enumerate()
        .for_each(|(i, row)| {
            for j in 0..n {
                let mut sum = Simd::<f32, 8>::splat(0.0);

                let chunks = n / 8;
                for k in 0..chunks {
                    let va = Simd::<f32, 8>::from_slice(&a[i * n + k * 8..]);
                    let mut vb_array = [0.0f32; 8];
                    for l in 0..8 {
                        vb_array[l] = b[(k * 8 + l) * n + j];
                    }
                    let vb = Simd::<f32, 8>::from_array(vb_array);
                    sum += va * vb;
                }

                row[j] = sum.reduce_sum();
            }
        });
}
```

（继续...）
