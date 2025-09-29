# 性能基准测试指南 / Performance Benchmarking Guide

## 概述 / Overview

本指南介绍如何在 Rust 项目中设置和使用性能基准测试，包括 Criterion、Miri、Loom 等工具的使用。

This guide introduces how to set up and use performance benchmarking in Rust projects, including the usage of Criterion, Miri, Loom, and other tools.

## 工具选择 / Tool Selection

### 1. Criterion - 性能基准测试 / Performance Benchmarking

Criterion 是 Rust 生态中最成熟的基准测试框架，提供统计分析、图表生成等功能。

```toml
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }

[[bench]]
name = "my_benchmark"
harness = false
```

### 2. Miri - 未定义行为检测 / Undefined Behavior Detection

Miri 是一个 Rust 解释器，可以检测未定义行为和内存安全问题。

```bash
# 安装 Miri
rustup component add miri

# 运行 Miri 测试
cargo miri test
```

### 3. Loom - 并发测试 / Concurrency Testing

Loom 是一个并发测试工具，可以探索所有可能的线程调度。

```toml
[dev-dependencies]
loom = "0.7"
```

## 基准测试设置 / Benchmark Setup

### 1. 基础基准测试 / Basic Benchmark

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

fn bench_fibonacci(c: &mut Criterion) {
    c.bench_function("fibonacci 20", |b| {
        b.iter(|| fibonacci(black_box(20)))
    });
}

criterion_group!(benches, bench_fibonacci);
criterion_main!(benches);
```

### 2. 比较基准测试 / Comparison Benchmark

```rust
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

fn bench_fibonacci_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("fibonacci_comparison");
    
    for i in [10, 15, 20].iter() {
        group.bench_with_input(BenchmarkId::new("recursive", i), i, |b, i| {
            b.iter(|| fibonacci_recursive(black_box(*i)))
        });
        
        group.bench_with_input(BenchmarkId::new("iterative", i), i, |b, i| {
            b.iter(|| fibonacci_iterative(black_box(*i)))
        });
    }
    
    group.finish();
}

fn fibonacci_recursive(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci_recursive(n - 1) + fibonacci_recursive(n - 2),
    }
}

fn fibonacci_iterative(n: u64) -> u64 {
    let mut a = 1;
    let mut b = 1;
    
    for _ in 2..=n {
        let temp = a + b;
        a = b;
        b = temp;
    }
    
    b
}

criterion_group!(benches, bench_fibonacci_comparison);
criterion_main!(benches);
```

### 3. 异步基准测试 / Async Benchmark

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use tokio::runtime::Runtime;

async fn async_operation(input: u64) -> u64 {
    tokio::time::sleep(std::time::Duration::from_millis(1)).await;
    input * 2
}

fn bench_async_operation(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    c.bench_function("async_operation", |b| {
        b.to_async(&rt).iter(|| async_operation(black_box(42)))
    });
}

criterion_group!(benches, bench_async_operation);
criterion_main!(benches);
```

## 并发测试 / Concurrency Testing

### 1. Loom 基础测试 / Basic Loom Test

```rust
use loom::sync::atomic::{AtomicUsize, Ordering};
use loom::sync::Arc;
use loom::thread;

#[test]
fn test_atomic_operations() {
    loom::model(|| {
        let atomic = Arc::new(AtomicUsize::new(0));
        let atomic_clone = atomic.clone();
        
        let t1 = thread::spawn(move || {
            atomic_clone.fetch_add(1, Ordering::SeqCst);
        });
        
        let t2 = thread::spawn(move || {
            atomic.fetch_add(1, Ordering::SeqCst);
        });
        
        t1.join().unwrap();
        t2.join().unwrap();
        
        assert_eq!(atomic.load(Ordering::SeqCst), 2);
    });
}
```

### 2. 复杂并发场景 / Complex Concurrency Scenario

```rust
use loom::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use loom::sync::Arc;
use loom::thread;
use std::sync::Mutex;

#[test]
fn test_producer_consumer() {
    loom::model(|| {
        let buffer = Arc::new(Mutex::new(Vec::new()));
        let count = Arc::new(AtomicUsize::new(0));
        let done = Arc::new(AtomicBool::new(false));
        
        // 生产者线程
        let buffer_clone = buffer.clone();
        let count_clone = count.clone();
        let done_clone = done.clone();
        
        let producer = thread::spawn(move || {
            for i in 0..10 {
                let mut buf = buffer_clone.lock().unwrap();
                buf.push(i);
                count_clone.fetch_add(1, Ordering::SeqCst);
            }
            done_clone.store(true, Ordering::SeqCst);
        });
        
        // 消费者线程
        let consumer = thread::spawn(move || {
            let mut consumed = 0;
            loop {
                if done.load(Ordering::SeqCst) && count.load(Ordering::SeqCst) == consumed {
                    break;
                }
                
                if let Ok(mut buf) = buffer.try_lock() {
                    if let Some(item) = buf.pop() {
                        consumed += 1;
                        // 处理项目
                    }
                }
            }
            consumed
        });
        
        producer.join().unwrap();
        let consumed = consumer.join().unwrap();
        
        assert_eq!(consumed, 10);
    });
}
```

## 内存安全测试 / Memory Safety Testing

### 1. Miri 基础测试 / Basic Miri Test

```rust
#[cfg(test)]
mod miri_tests {
    use super::*;
    
    #[test]
    fn test_memory_safety() {
        // 测试未定义行为
        let mut vec = Vec::new();
        vec.push(1);
        vec.push(2);
        
        // 安全的访问
        assert_eq!(vec[0], 1);
        assert_eq!(vec[1], 2);
        
        // 测试边界情况
        if let Some(last) = vec.last() {
            assert_eq!(*last, 2);
        }
    }
    
    #[test]
    fn test_unsafe_code() {
        unsafe {
            let mut data = [1, 2, 3, 4, 5];
            let ptr = data.as_mut_ptr();
            
            // 安全的指针操作
            *ptr.add(0) = 10;
            *ptr.add(1) = 20;
            
            assert_eq!(data[0], 10);
            assert_eq!(data[1], 20);
        }
    }
}
```

### 2. 数据竞争检测 / Data Race Detection

```rust
#[cfg(test)]
mod race_condition_tests {
    use std::sync::{Arc, Mutex};
    use std::thread;
    
    #[test]
    fn test_no_data_race() {
        let data = Arc::new(Mutex::new(0));
        let mut handles = vec![];
        
        for _ in 0..10 {
            let data_clone = data.clone();
            let handle = thread::spawn(move || {
                let mut num = data_clone.lock().unwrap();
                *num += 1;
            });
            handles.push(handle);
        }
        
        for handle in handles {
            handle.join().unwrap();
        }
        
        assert_eq!(*data.lock().unwrap(), 10);
    }
}
```

## 性能分析 / Performance Analysis

### 1. 火焰图生成 / Flame Graph Generation

```bash
# 安装 perf 工具
sudo apt-get install linux-tools-common linux-tools-generic

# 运行基准测试并生成火焰图
cargo bench -- --profile-time=10
```

### 2. 内存分析 / Memory Analysis

```bash
# 使用 valgrind 进行内存分析
valgrind --tool=memcheck --leak-check=full cargo test

# 使用 heaptrack 进行堆分析
heaptrack cargo test
```

### 3. CPU 分析 / CPU Analysis

```bash
# 使用 perf 进行 CPU 分析
perf record --call-graph dwarf cargo bench
perf report
```

## 持续集成 / Continuous Integration

### 1. GitHub Actions 配置 / GitHub Actions Configuration

```yaml
name: Performance Tests

on: [push, pull_request]

jobs:
  benchmark:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: stable
          components: rustfmt, clippy
      
      - name: Run benchmarks
        run: cargo bench
      
      - name: Upload benchmark results
        uses: actions/upload-artifact@v3
        with:
          name: benchmark-results
          path: target/criterion/
  
  miri:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: nightly
          components: miri
      
      - name: Run Miri tests
        run: cargo miri test
```

### 2. 性能回归检测 / Performance Regression Detection

```rust
use criterion::{criterion_group, criterion_main, Criterion};

fn bench_regression_test(c: &mut Criterion) {
    let mut group = c.benchmark_group("regression");
    
    // 设置性能阈值
    group.measurement_time(std::time::Duration::from_secs(10));
    group.sample_size(1000);
    
    group.bench_function("critical_path", |b| {
        b.iter(|| {
            // 关键路径代码
            critical_operation()
        })
    });
    
    group.finish();
}

criterion_group!(benches, bench_regression_test);
criterion_main!(benches);
```

## 最佳实践 / Best Practices

### 1. 基准测试最佳实践 / Benchmarking Best Practices

- 使用 `black_box` 防止编译器优化
- 设置合适的测量时间
- 多次运行确保结果稳定
- 比较不同实现的性能

### 2. 并发测试最佳实践 / Concurrency Testing Best Practices

- 使用 Loom 测试所有可能的调度
- 测试边界条件和错误情况
- 验证内存安全和数据竞争
- 测试取消和超时机制

### 3. 性能优化最佳实践 / Performance Optimization Best Practices

- 先测量，后优化
- 使用性能分析工具
- 关注关键路径
- 考虑缓存友好性

## 工具链集成 / Toolchain Integration

### 1. 开发环境配置 / Development Environment

```bash
# 安装所有必要工具
rustup component add clippy rustfmt
rustup component add miri --toolchain nightly
cargo install cargo-criterion
cargo install cargo-udeps
```

### 2. 预提交钩子 / Pre-commit Hooks

```bash
#!/bin/bash
# .git/hooks/pre-commit

# 运行格式化检查
cargo fmt --all -- --check

# 运行 clippy 检查
cargo clippy --all-targets -- -D warnings

# 运行 Miri 测试
cargo miri test

# 运行基准测试
cargo bench -- --test
```

## 扩展阅读 / Further Reading

- [Criterion Documentation](https://docs.rs/criterion/)
- [Miri Documentation](https://github.com/rust-lang/miri)
- [Loom Documentation](https://docs.rs/loom/)
- [Rust Performance Book](https://nnethercote.github.io/perf-book/)
