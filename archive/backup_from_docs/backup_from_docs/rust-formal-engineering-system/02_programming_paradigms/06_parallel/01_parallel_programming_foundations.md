# 并行编程基础（Parallel Programming Foundations）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [并行编程基础（Parallel Programming Foundations）](#并行编程基础parallel-programming-foundations)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [并行 vs 并发](#并行-vs-并发)
    - [并发（Concurrency）](#并发concurrency)
    - [并行（Parallelism）](#并行parallelism)
  - [数据并行](#数据并行)
  - [任务并行](#任务并行)
  - [Rayon 库](#rayon-库)
    - [基本使用](#基本使用)
    - [并行归约](#并行归约)
    - [并行排序](#并行排序)
  - [实践示例](#实践示例)
    - [示例 1：并行图像处理](#示例-1并行图像处理)
    - [示例 2：并行矩阵运算](#示例-2并行矩阵运算)
    - [示例 3：并行搜索](#示例-3并行搜索)
  - [性能优化](#性能优化)
    - [1. 避免过度并行化](#1-避免过度并行化)
    - [2. 使用并行迭代器链](#2-使用并行迭代器链)
    - [3. 自定义并行策略](#3-自定义并行策略)
  - [参考资料](#参考资料)

---

## 概述

并行编程是指同时执行多个计算任务，充分利用多核 CPU 的计算能力。Rust 通过类型系统保证并行安全，避免了数据竞争。

## 并行 vs 并发

### 并发（Concurrency）

多个任务交替执行，看起来同时进行：

```rust
use std::thread;

fn main() {
    let handle1 = thread::spawn(|| {
        for i in 1..5 {
            println!("任务 1: {}", i);
        }
    });

    let handle2 = thread::spawn(|| {
        for i in 1..5 {
            println!("任务 2: {}", i);
        }
    });

    handle1.join().unwrap();
    handle2.join().unwrap();
}
```

### 并行（Parallelism）

多个任务真正同时执行，需要多核 CPU：

```rust
use rayon::prelude::*;

fn main() {
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    let result: Vec<i32> = data
        .par_iter()
        .map(|x| x * 2)
        .collect();

    println!("结果: {:?}", result);
}
```

## 数据并行

数据并行是指将数据分割成多个部分，在不同处理器上并行处理：

```rust
use rayon::prelude::*;

fn parallel_sum(data: &[i32]) -> i32 {
    data.par_iter().sum()
}

fn parallel_map(data: &[i32]) -> Vec<i32> {
    data.par_iter()
        .map(|x| x * x)
        .collect()
}

fn parallel_filter(data: &[i32]) -> Vec<i32> {
    data.par_iter()
        .filter(|&&x| x % 2 == 0)
        .copied()
        .collect()
}
```

## 任务并行

任务并行是指将不同的任务分配给不同的处理器：

```rust
use rayon::prelude::*;
use std::time::Instant;

fn task_parallel_example() {
    let start = Instant::now();

    let (result1, result2, result3) = rayon::join(
        || compute_task1(),
        || compute_task2(),
        || compute_task3(),
    );

    println!("任务1结果: {}", result1);
    println!("任务2结果: {}", result2);
    println!("任务3结果: {}", result3);
    println!("总耗时: {:?}", start.elapsed());
}

fn compute_task1() -> i32 {
    // 模拟计算
    (1..1000000).sum()
}

fn compute_task2() -> i32 {
    // 模拟计算
    (1..2000000).sum()
}

fn compute_task3() -> i32 {
    // 模拟计算
    (1..3000000).sum()
}
```

## Rayon 库

Rayon 是 Rust 中最流行的并行处理库：

### 基本使用

```rust
use rayon::prelude::*;

fn main() {
    let mut data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // 并行迭代
    data.par_iter_mut()
        .for_each(|x| *x *= 2);

    println!("结果: {:?}", data);
}
```

### 并行归约

```rust
use rayon::prelude::*;

fn parallel_reduce() {
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    let sum: i32 = data.par_iter().sum();
    let product: i32 = data.par_iter().product();
    let max: Option<&i32> = data.par_iter().max();
    let min: Option<&i32> = data.par_iter().min();

    println!("和: {}", sum);
    println!("积: {}", product);
    println!("最大值: {:?}", max);
    println!("最小值: {:?}", min);
}
```

### 并行排序

```rust
use rayon::prelude::*;

fn parallel_sort() {
    let mut data = vec![5, 2, 8, 1, 9, 3, 7, 4, 6, 10];

    data.par_sort();
    println!("排序后: {:?}", data);

    data.par_sort_unstable();
    println!("不稳定排序: {:?}", data);
}
```

## 实践示例

### 示例 1：并行图像处理

```rust
use rayon::prelude::*;

pub struct Image {
    width: usize,
    height: usize,
    pixels: Vec<u8>,
}

impl Image {
    pub fn apply_filter_parallel(&mut self, filter: fn(u8) -> u8) {
        self.pixels.par_iter_mut()
            .for_each(|pixel| {
                *pixel = filter(*pixel);
            });
    }

    pub fn grayscale_parallel(&mut self) {
        // 假设每个像素是 RGB (3 bytes)
        self.pixels
            .par_chunks_exact_mut(3)
            .for_each(|rgb| {
                let gray = (rgb[0] as f32 * 0.299
                          + rgb[1] as f32 * 0.587
                          + rgb[2] as f32 * 0.114) as u8;
                rgb[0] = gray;
                rgb[1] = gray;
                rgb[2] = gray;
            });
    }
}
```

### 示例 2：并行矩阵运算

```rust
use rayon::prelude::*;

pub fn parallel_matrix_multiply(a: &[Vec<f64>], b: &[Vec<f64>]) -> Vec<Vec<f64>> {
    let n = a.len();
    let m = b[0].len();
    let p = b.len();

    (0..n)
        .into_par_iter()
        .map(|i| {
            (0..m)
                .map(|j| {
                    (0..p)
                        .map(|k| a[i][k] * b[k][j])
                        .sum()
                })
                .collect()
        })
        .collect()
}
```

### 示例 3：并行搜索

```rust
use rayon::prelude::*;

pub fn parallel_search<T: PartialEq + Send + Sync>(
    data: &[T],
    target: &T,
) -> Option<usize> {
    data.par_iter()
        .position_first(|x| x == target)
}
```

## 性能优化

### 1. 避免过度并行化

```rust
use rayon::prelude::*;

fn smart_parallel(data: &[i32]) -> i32 {
    // 小数据集使用串行处理
    if data.len() < 1000 {
        data.iter().sum()
    } else {
        data.par_iter().sum()
    }
}
```

### 2. 使用并行迭代器链

```rust
use rayon::prelude::*;

fn efficient_parallel_processing(data: &[i32]) -> Vec<i32> {
    data.par_iter()
        .filter(|&&x| x > 0)      // 并行过滤
        .map(|x| x * x)            // 并行映射
        .collect()                 // 并行收集
}
```

### 3. 自定义并行策略

```rust
use rayon::prelude::*;

fn custom_parallel_strategy(data: &[i32]) {
    data.par_chunks(100)  // 将数据分成块
        .for_each(|chunk| {
            // 处理每个块
            process_chunk(chunk);
        });
}

fn process_chunk(chunk: &[i32]) {
    // 处理逻辑
}
```

## 参考资料

- [Rayon 文档](https://docs.rs/rayon/)
- [并发编程基础](../05_concurrent/01_concurrent_programming_foundations.md)
- [并行计算理论](../../01_theoretical_foundations/04_concurrency_models/00_index.md)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回编程范式: [`../00_index.md`](../00_index.md)
