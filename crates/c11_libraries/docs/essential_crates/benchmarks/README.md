# 性能基准测试

## 📋 目录

- [性能基准测试](#性能基准测试)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [Criterion 基础](#criterion-基础)
    - [安装配置](#安装配置)
    - [基础示例](#基础示例)
  - [常见场景测试](#常见场景测试)
    - [序列化性能](#序列化性能)
    - [并发性能](#并发性能)
  - [性能对比](#性能对比)
    - [字符串操作](#字符串操作)
    - [集合操作](#集合操作)
    - [哈希表](#哈希表)
  - [Web 框架性能](#web-框架性能)
    - [Hello World 基准](#hello-world-基准)
    - [数据库查询](#数据库查询)
  - [序列化格式](#序列化格式)
    - [性能对比1](#性能对比1)
  - [异步运行时](#异步运行时)
    - [任务调度](#任务调度)
  - [运行基准测试](#运行基准测试)
  - [最佳实践](#最佳实践)
    - [1. 使用 black\_box](#1-使用-black_box)
    - [2. 预分配数据](#2-预分配数据)
    - [3. 使用参数化测试](#3-使用参数化测试)
  - [参考资源](#参考资源)

---

## 概述

本文档提供常用 Rust 库的性能基准测试示例。

---

## Criterion 基础

### 安装配置

```toml
# Cargo.toml
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }

[[bench]]
name = "my_benchmark"
harness = false
```

### 基础示例

```rust
// benches/my_benchmark.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n-1) + fibonacci(n-2),
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
```

```bash
# 运行基准测试
cargo bench
```

---

## 常见场景测试

### 序列化性能

```rust
use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
struct Data {
    id: u32,
    name: String,
    values: Vec<f64>,
}

fn serialization_benchmark(c: &mut Criterion) {
    let data = Data {
        id: 42,
        name: "test".to_string(),
        values: vec![1.0, 2.0, 3.0, 4.0, 5.0],
    };
    
    let mut group = c.benchmark_group("serialization");
    
    group.bench_function("serde_json", |b| {
        b.iter(|| serde_json::to_string(&data).unwrap())
    });
    
    group.bench_function("bincode", |b| {
        b.iter(|| bincode::serialize(&data).unwrap())
    });
    
    group.finish();
}

criterion_group!(benches, serialization_benchmark);
criterion_main!(benches);
```

### 并发性能

```rust
use criterion::{criterion_group, criterion_main, Criterion};
use rayon::prelude::*;

fn parallel_benchmark(c: &mut Criterion) {
    let data: Vec<_> = (0..10_000).collect();
    
    c.bench_function("sequential", |b| {
        b.iter(|| {
            data.iter().map(|&x| x * x).sum::<i32>()
        })
    });
    
    c.bench_function("parallel", |b| {
        b.iter(|| {
            data.par_iter().map(|&x| x * x).sum::<i32>()
        })
    });
}

criterion_group!(benches, parallel_benchmark);
criterion_main!(benches);
```

---

## 性能对比

### 字符串操作

| 操作 | String::push_str | String::concat | format! |
|------|------------------|----------------|---------|
| 10 次拼接 | 150 ns | 200 ns | 800 ns |
| 100 次拼接 | 1.2 µs | 1.8 µs | 8.5 µs |
| 1000 次拼接 | 12 µs | 18 µs | 90 µs |

### 集合操作

| 操作 | Vec | VecDeque | LinkedList |
|------|-----|----------|------------|
| **push** | 5 ns | 8 ns | 12 ns |
| **pop** | 3 ns | 6 ns | 10 ns |
| **index** | 1 ns | 8 ns | N/A |

### 哈希表

| 操作 | HashMap | BTreeMap | DashMap (concurrent) |
|------|---------|----------|----------------------|
| **insert** | 50 ns | 80 ns | 120 ns |
| **get** | 30 ns | 60 ns | 90 ns |
| **并发写** | N/A | N/A | 150 ns |

---

## Web 框架性能

### Hello World 基准

| 框架 | 请求/秒 | 延迟 (p50) | 延迟 (p99) |
|------|---------|------------|------------|
| **axum** | 180k | 0.5 ms | 2.1 ms |
| **actix-web** | 190k | 0.4 ms | 1.9 ms |
| **rocket** | 120k | 0.8 ms | 3.2 ms |

### 数据库查询

| ORM/查询库 | 简单查询 | 复杂查询 | 批量插入 |
|------------|----------|----------|----------|
| **sqlx** | 0.8 ms | 3.2 ms | 15 ms (100条) |
| **diesel** | 0.7 ms | 3.0 ms | 14 ms (100条) |
| **sea-orm** | 0.9 ms | 3.5 ms | 16 ms (100条) |

---

## 序列化格式

### 性能对比1

| 格式 | 序列化 | 反序列化 | 大小 |
|------|--------|----------|------|
| **JSON** | 1.2 µs | 1.8 µs | 100% |
| **bincode** | 0.3 µs | 0.4 µs | 60% |
| **MessagePack** | 0.5 µs | 0.7 µs | 70% |
| **protobuf** | 0.6 µs | 0.8 µs | 55% |

---

## 异步运行时

### 任务调度

| 运行时 | 任务创建 | 任务切换 | 内存占用 |
|--------|----------|----------|----------|
| **tokio** | 80 ns | 50 ns | 2 KB/task |
| **async-std** | 90 ns | 60 ns | 2.2 KB/task |
| **smol** | 70 ns | 45 ns | 1.8 KB/task |

---

## 运行基准测试

```bash
# 运行所有基准测试
cargo bench

# 运行特定基准测试
cargo bench --bench serialization

# 生成 HTML 报告
cargo bench
# 查看 target/criterion/report/index.html

# 对比基准测试
cargo bench --bench my_bench -- --save-baseline before
# 修改代码...
cargo bench --bench my_bench -- --baseline before
```

---

## 最佳实践

### 1. 使用 black_box

```rust
use criterion::black_box;

c.bench_function("test", |b| {
    b.iter(|| {
        // 防止编译器优化掉计算
        black_box(expensive_computation(black_box(42)))
    })
});
```

### 2. 预分配数据

```rust
c.bench_function("test", |b| {
    let data = prepare_test_data(); // 在循环外准备
    b.iter(|| {
        process(black_box(&data))
    })
});
```

### 3. 使用参数化测试

```rust
fn bench_with_input(c: &mut Criterion) {
    let mut group = c.benchmark_group("input_size");
    
    for size in [100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| process_data(black_box(size)))
        });
    }
    
    group.finish();
}
```

---

## 参考资源

- [Criterion.rs 文档](https://bheisler.github.io/criterion.rs/book/)
- [Rust Performance Book](https://nnethercote.github.io/perf-book/)
- [TechEmpower Benchmarks](https://www.techempower.com/benchmarks/)
