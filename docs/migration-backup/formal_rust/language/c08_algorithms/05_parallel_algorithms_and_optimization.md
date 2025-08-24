# 并行算法与优化

## 概述

并行算法和性能优化是提升现代计算效率的关键。Rust 通过安全的并发模型和高效的内存管理，为并行算法的实现和性能调优提供了坚实基础。本章系统梳理并行排序、并行搜索、内存优化和性能调优等内容。

## 并行排序

### Rayon 并行排序

```rust
use rayon::prelude::*;

fn parallel_sort(arr: &mut [i32]) {
    arr.par_sort();
}

fn main() {
    let mut data = vec![5, 3, 8, 1, 2];
    parallel_sort(&mut data);
    println!("{:?}", data);
}
```

### 并行归并排序（自定义实现）

```rust
use rayon::join;

fn parallel_merge_sort<T: Ord + Send + Clone>(arr: &mut [T]) {
    let len = arr.len();
    if len <= 1 {
        return;
    }
    let mid = len / 2;
    let (left, right) = arr.split_at_mut(mid);
    join(|| parallel_merge_sort(left), || parallel_merge_sort(right));
    let mut merged = left.to_vec();
    merged.extend_from_slice(right);
    merged.sort();
    arr.copy_from_slice(&merged);
}
```

## 并行搜索

### 并行查找最大值

```rust
use rayon::prelude::*;

fn parallel_max(arr: &[i32]) -> Option<i32> {
    arr.par_iter().cloned().max()
}
```

### 并行过滤

```rust
use rayon::prelude::*;

fn parallel_filter(arr: &[i32], threshold: i32) -> Vec<i32> {
    arr.par_iter().cloned().filter(|&x| x > threshold).collect()
}
```

## 内存优化

### 零拷贝与切片

```rust
fn zero_copy_example() {
    let data = vec![1, 2, 3, 4, 5];
    let slice: &[i32] = &data[1..4];
    println!("{:?}", slice); // [2, 3, 4]
}
```

### 内存池与对象复用

```rust
use std::collections::VecDeque;

struct ObjectPool<T> {
    pool: VecDeque<T>,
}

impl<T> ObjectPool<T> {
    fn new() -> Self {
        ObjectPool { pool: VecDeque::new() }
    }
    fn get(&mut self) -> Option<T> {
        self.pool.pop_front()
    }
    fn put(&mut self, obj: T) {
        self.pool.push_back(obj);
    }
}
```

## 性能调优

### 多线程与任务划分

```rust
use std::thread;

fn multi_thread_sum(arr: &[i32]) -> i32 {
    let mid = arr.len() / 2;
    let (left, right) = arr.split_at(mid);
    let handle = thread::spawn(move || left.iter().sum::<i32>());
    let right_sum: i32 = right.iter().sum();
    let left_sum = handle.join().unwrap();
    left_sum + right_sum
}
```

### 缓存友好性优化

```rust
fn cache_friendly_sum(arr: &[i32]) -> i32 {
    let mut sum = 0;
    for chunk in arr.chunks(64) {
        for &x in chunk {
            sum += x;
        }
    }
    sum
}
```

### SIMD 优化（需 nightly）

```rust
// 需加 #![feature(portable_simd)]
// use std::simd::{Simd, SimdPartialEq};
// 示例略
```

## 工具与实践建议

- 推荐使用 rayon、crossbeam 等高性能并发库
- 使用 cargo bench 进行基准测试
- 利用 flamegraph、perf 等工具分析性能瓶颈
- 关注内存分配与数据局部性

## 总结

并行算法和性能优化是现代高性能计算的核心。Rust 的并发安全和内存管理机制为高效并行编程提供了坚实保障。

### 关键要点

1. **并行排序** - 利用 rayon 等库实现高效并行排序
2. **并行搜索** - 并行查找、过滤等操作提升效率
3. **内存优化** - 零拷贝、内存池等技术减少资源消耗
4. **性能调优** - 多线程、缓存友好、SIMD 等手段提升性能

### 下一步

在下一章中，我们将探讨算法设计与分析，包括算法设计模式、复杂度分析、正确性证明和优化策略。
