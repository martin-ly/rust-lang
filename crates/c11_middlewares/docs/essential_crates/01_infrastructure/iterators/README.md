# 迭代器增强

> **核心库**: itertools, rayon  
> **适用场景**: 迭代器扩展、并行迭代、函数式编程

---

## 📋 目录

- [迭代器增强](#迭代器增强)
  - [📋 目录](#-目录)
  - [🎯 核心概念](#-核心概念)
  - [🔧 itertools - 迭代器工具包](#-itertools---迭代器工具包)
    - [核心特性](#核心特性)
    - [分组与排序](#分组与排序)
    - [组合与排列](#组合与排列)
    - [窗口与批次](#窗口与批次)
    - [高级组合](#高级组合)
  - [⚡ rayon - 并行迭代](#-rayon---并行迭代)
    - [核心特性1](#核心特性1)
    - [基础并行操作](#基础并行操作)
    - [并行排序与搜索](#并行排序与搜索)
  - [💡 最佳实践](#-最佳实践)
    - [1. 何时使用 itertools](#1-何时使用-itertools)
    - [2. 何时使用 rayon](#2-何时使用-rayon)
    - [3. 性能考虑](#3-性能考虑)
  - [🔧 常见场景](#-常见场景)
    - [场景 1: 数据分析](#场景-1-数据分析)
    - [场景 2: 批量处理](#场景-2-批量处理)
    - [场景 3: 并行文件处理](#场景-3-并行文件处理)
  - [📚 延伸阅读](#-延伸阅读)

---

## 🎯 核心概念

**itertools**: 扩展标准库迭代器，提供强大的函数式操作
**rayon**: 零成本并行迭代器，自动利用多核

---

## 🔧 itertools - 迭代器工具包

### 核心特性

- ✅ 100+ 迭代器方法
- ✅ 零成本抽象
- ✅ 链式调用
- ✅ 惰性求值

### 分组与排序

```rust
use itertools::Itertools;

fn main() {
    // 分组
    let data = vec![1, 2, 2, 3, 3, 3, 4];
    let grouped = data.into_iter()
        .group_by(|&x| x)
        .into_iter()
        .map(|(key, group)| (key, group.count()))
        .collect::<Vec<_>>();
    println!("{:?}", grouped); // [(1, 1), (2, 2), (3, 3), (4, 1)]
    
    // 排序后分组
    let words = vec!["apple", "banana", "apricot", "blueberry"];
    let by_first_letter = words.into_iter()
        .sorted()
        .group_by(|s| s.chars().next().unwrap())
        .into_iter()
        .map(|(key, group)| (key, group.collect::<Vec<_>>()))
        .collect::<Vec<_>>();
    println!("{:?}", by_first_letter);
    
    // 唯一值
    let numbers = vec![1, 2, 2, 3, 3, 3];
    let unique: Vec<_> = numbers.into_iter().unique().collect();
    println!("{:?}", unique); // [1, 2, 3]
}
```

### 组合与排列

```rust
use itertools::Itertools;

fn main() {
    // 笛卡尔积
    let a = vec![1, 2];
    let b = vec!['a', 'b'];
    let product: Vec<_> = a.iter()
        .cartesian_product(b.iter())
        .collect();
    println!("{:?}", product); // [(1, 'a'), (1, 'b'), (2, 'a'), (2, 'b')]
    
    // 组合
    let items = vec![1, 2, 3, 4];
    let combinations: Vec<_> = items.iter()
        .combinations(2)
        .collect();
    println!("{:?}", combinations); // [[1, 2], [1, 3], [1, 4], [2, 3], [2, 4], [3, 4]]
    
    // 排列
    let permutations: Vec<_> = (1..=3)
        .permutations(2)
        .collect();
    println!("{:?}", permutations); // [[1, 2], [1, 3], [2, 1], [2, 3], [3, 1], [3, 2]]
}
```

### 窗口与批次

```rust
use itertools::Itertools;

fn main() {
    // 滑动窗口
    let data = vec![1, 2, 3, 4, 5];
    let windows: Vec<_> = data.iter()
        .tuple_windows::<(_, _, _)>()
        .collect();
    println!("{:?}", windows); // [(1, 2, 3), (2, 3, 4), (3, 4, 5)]
    
    // 分块
    let chunks: Vec<_> = (1..=10)
        .chunks(3)
        .into_iter()
        .map(|chunk| chunk.collect::<Vec<_>>())
        .collect();
    println!("{:?}", chunks); // [[1, 2, 3], [4, 5, 6], [7, 8, 9], [10]]
    
    // 交错
    let a = vec![1, 2, 3];
    let b = vec![10, 20, 30];
    let interleaved: Vec<_> = a.iter().interleave(b.iter()).collect();
    println!("{:?}", interleaved); // [1, 10, 2, 20, 3, 30]
}
```

### 高级组合

```rust
use itertools::Itertools;

fn main() {
    // 多个迭代器合并
    let a = vec![1, 2, 3];
    let b = vec![10, 20];
    let c = vec![100];
    let merged: Vec<_> = itertools::chain!(a, b, c).collect();
    println!("{:?}", merged); // [1, 2, 3, 10, 20, 100]
    
    // 累积和
    let data = vec![1, 2, 3, 4];
    let cumsum: Vec<_> = data.iter()
        .scan(0, |state, &x| {
            *state += x;
            Some(*state)
        })
        .collect();
    println!("{:?}", cumsum); // [1, 3, 6, 10]
    
    // 成对迭代
    let pairs: Vec<_> = (1..=5)
        .tuple_windows::<(_, _)>()
        .collect();
    println!("{:?}", pairs); // [(1, 2), (2, 3), (3, 4), (4, 5)]
}
```

---

## ⚡ rayon - 并行迭代

### 核心特性1

- ✅ 零成本并行
- ✅ 自动工作窃取
- ✅ 数据竞争安全
- ✅ 简单 API

### 基础并行操作

```rust
use rayon::prelude::*;

fn main() {
    // 并行 map
    let data: Vec<_> = (1..=1000).collect();
    let squared: Vec<_> = data.par_iter()
        .map(|&x| x * x)
        .collect();
    
    // 并行 filter
    let evens: Vec<_> = data.par_iter()
        .filter(|&&x| x % 2 == 0)
        .copied()
        .collect();
    
    // 并行 reduce
    let sum: i32 = data.par_iter()
        .sum();
    
    println!("Sum: {}", sum);
}
```

### 并行排序与搜索

```rust
use rayon::prelude::*;

fn main() {
    let mut data: Vec<_> = (1..=1000).rev().collect();
    
    // 并行排序
    data.par_sort();
    
    // 并行搜索
    let found = data.par_iter()
        .find_any(|&&x| x == 500);
    
    println!("Found: {:?}", found);
}
```

---

## 💡 最佳实践

### 1. 何时使用 itertools

```rust
use itertools::Itertools;

// ✅ 复杂的数据转换
fn analyze_data(data: Vec<i32>) -> Vec<(i32, usize)> {
    data.into_iter()
        .sorted()
        .group_by(|&x| x)
        .into_iter()
        .map(|(key, group)| (key, group.count()))
        .collect()
}

// ✅ 组合算法
fn find_pairs_sum_to(nums: &[i32], target: i32) -> Vec<(i32, i32)> {
    nums.iter()
        .combinations(2)
        .filter_map(|pair| {
            if pair[0] + pair[1] == target {
                Some((*pair[0], *pair[1]))
            } else {
                None
            }
        })
        .collect()
}
```

### 2. 何时使用 rayon

```rust
use rayon::prelude::*;

// ✅ CPU 密集型任务
fn process_large_dataset(data: &[f64]) -> Vec<f64> {
    data.par_iter()
        .map(|&x| expensive_computation(x))
        .collect()
}

// ✅ 并行聚合
fn parallel_sum(data: &[i32]) -> i32 {
    data.par_iter().sum()
}

// ❌ 小数据集 (开销大于收益)
fn small_sum(data: &[i32]) -> i32 {
    data.iter().sum() // 串行更快
}
```

### 3. 性能考虑

```rust
use rayon::prelude::*;

// ✅ 合理的粒度
fn process_with_chunk_size(data: &[i32]) -> Vec<i32> {
    data.par_chunks(1000) // 避免过小的任务
        .flat_map(|chunk| {
            chunk.iter().map(|&x| x * 2).collect::<Vec<_>>()
        })
        .collect()
}

// ✅ 避免过度分配
fn avoid_allocation(data: &[i32]) -> i32 {
    data.par_iter() // 不需要 collect
        .map(|&x| x * 2)
        .sum()
}
```

---

## 🔧 常见场景

### 场景 1: 数据分析

```rust
use itertools::Itertools;

fn analyze_sales(sales: Vec<(String, i32)>) -> Vec<(String, i32, f64)> {
    let total: i32 = sales.iter().map(|(_, amount)| amount).sum();
    
    sales.into_iter()
        .sorted_by_key(|(_, amount)| -amount)
        .map(|(product, amount)| {
            let percentage = (amount as f64 / total as f64) * 100.0;
            (product, amount, percentage)
        })
        .collect()
}
```

### 场景 2: 批量处理

```rust
use itertools::Itertools;

fn process_in_batches<T, F>(items: Vec<T>, batch_size: usize, f: F)
where
    F: Fn(&[T]),
{
    items.iter()
        .chunks(batch_size)
        .into_iter()
        .for_each(|chunk| {
            let batch: Vec<_> = chunk.collect();
            f(&batch);
        });
}
```

### 场景 3: 并行文件处理

```rust
use rayon::prelude::*;
use std::fs;

fn process_files_parallel(paths: Vec<String>) -> Vec<usize> {
    paths.par_iter()
        .filter_map(|path| {
            fs::read_to_string(path)
                .ok()
                .map(|content| content.lines().count())
        })
        .collect()
}
```

---

## 📚 延伸阅读

- [itertools 官方文档](https://docs.rs/itertools/)
- [rayon 官方文档](https://docs.rs/rayon/)
- [Rust 迭代器最佳实践](https://doc.rust-lang.org/book/ch13-02-iterators.html)

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
