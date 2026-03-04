# Rayon并行计算案例分析

## 概述

Rayon是Rust的数据并行库，提供零开销的迭代器并行化。

## 核心设计

### 1. 并行迭代器

```rust
use rayon::prelude::*;

// 串行迭代器 → 并行迭代器 (仅需添加 .par_iter())
let sum: i32 = data
    .par_iter()           // 并行迭代
    .map(|x| x * x)       // 自动并行
    .sum();
```

### 2. 所有权保证

```rust
// 所有权转移版本
let results: Vec<_> = data
    .into_par_iter()      // 消耗所有权
    .map(process)
    .collect();

// 借用版本
let sum = data
    .par_iter()           // 共享借用
    .filter(|x| x > &&0)
    .sum();
```

### 3. 线程安全边界

```rust
// 编译错误: 非Send类型不能跨线程
let rc_data: Rc<Vec<i32>> = ...;
rc_data.par_iter().map(...);  // ERROR!

// 正确: Arc可以跨线程
let arc_data: Arc<Vec<i32>> = ...;
arc_data.par_iter().map(...);  // OK
```

## 工作窃取实现

```
┌─────────────────────────────────────────┐
│  Thread 1       Thread 2       Thread 3 │
│  ┌─────────┐   ┌─────────┐   ┌─────────┐│
│  │ [A,B,C] │   │ [D,E]   │   │ [F]     ││
│  │         │   │         │   │         ││
│  │ 窃取 ←───────┘         │   │         ││
│  │         │              │   │         ││
│  │ [A,B,C] │   └──────────┘   │         ││
│  │   [E]   │                  │         ││
│  └─────────┘                  └─────────┘│
└─────────────────────────────────────────┘
```

## 性能特征

### Fork-Join模型

```rust
// 递归分治
fn quick_sort<T: Ord + Send>(data: &mut [T]) {
    if data.len() <= 1 {
        return;
    }

    let mid = partition(data);
    let (left, right) = data.split_at_mut(mid);

    // 并行排序左右两部分
    rayon::join(
        || quick_sort(left),
        || quick_sort(right),
    );
}
```

### 自适应粒度

Rayon自动决定并行粒度:

- 小任务: 串行执行(减少开销)
- 大任务: 继续分割

## 高级API

### parallel_sort

```rust
// 并行排序
vec.par_sort();
vec.par_sort_unstable();  // 更快但不稳定
```

### 并行归约

```rust
// 自定义归约操作
let result = data
    .par_iter()
    .map(|x| expensive_computation(x))
    .reduce(|| 0, |a, b| a + b);
```

## 结论

Rayon通过所有权和Send/Sync trait，在提供简单并行API的同时保证了线程安全。
