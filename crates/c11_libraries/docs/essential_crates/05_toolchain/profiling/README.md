# 性能分析工具 (Profiling Tools)

**类别**: 第5层 - 工具链  
**重要程度**: ⭐⭐⭐⭐  
**更新日期**: 2025-10-20

---

## 📋 目录

- [性能分析工具 (Profiling Tools)](#性能分析工具-profiling-tools)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🔧 核心工具](#-核心工具)
    - [1. criterion (基准测试 ⭐⭐⭐⭐⭐)](#1-criterion-基准测试-)
      - [基础用法](#基础用法)
      - [运行基准测试](#运行基准测试)
      - [高级特性](#高级特性)
    - [2. flamegraph (火焰图 🌟)](#2-flamegraph-火焰图-)
      - [Linux 使用](#linux-使用)
      - [macOS 使用](#macos-使用)
      - [配置文件](#配置文件)
    - [3. cargo-bench (内置)](#3-cargo-bench-内置)
    - [4. pprof (CPU/内存分析 💡)](#4-pprof-cpu内存分析-)
      - [CPU 性能分析](#cpu-性能分析)
      - [与 criterion 集成](#与-criterion-集成)
    - [5. valgrind/cachegrind (高级)](#5-valgrindcachegrind-高级)
      - [内存泄漏检测](#内存泄漏检测)
      - [缓存性能分析](#缓存性能分析)
      - [Callgrind (调用图)](#callgrind-调用图)
    - [6. heaptrack (堆内存分析)](#6-heaptrack-堆内存分析)
    - [7. perf (Linux 系统级)](#7-perf-linux-系统级)
      - [基础用法2](#基础用法2)
      - [高级分析](#高级分析)
  - [💡 最佳实践](#-最佳实践)
    - [1. 基准测试模板](#1-基准测试模板)
    - [2. 性能分析流程](#2-性能分析流程)
    - [3. Profile 配置优化](#3-profile-配置优化)
  - [📊 工具对比](#-工具对比)
    - [性能分析工具选择](#性能分析工具选择)
  - [🎯 实战场景](#-实战场景)
    - [场景1: API 性能优化](#场景1-api-性能优化)
    - [场景2: 算法对比](#场景2-算法对比)
    - [场景3: 内存密集型应用](#场景3-内存密集型应用)
  - [🔗 相关资源](#-相关资源)

## 📋 概述

性能分析工具帮助开发者识别性能瓶颈、优化热点代码、减少资源消耗。

---

## 🔧 核心工具

### 1. criterion (基准测试 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add --dev criterion`  
**用途**: 统计驱动的基准测试框架

#### 基础用法

```rust
// benches/my_benchmark.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
```

**Cargo.toml 配置**:

```toml
[[bench]]
name = "my_benchmark"
harness = false  # 禁用默认 harness

[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }
```

#### 运行基准测试

```bash
# 运行所有基准测试
cargo bench

# 运行特定基准测试
cargo bench fib

# 生成 flamegraph
cargo bench --bench my_benchmark -- --profile-time=5
```

#### 高级特性

```rust
use criterion::{BenchmarkId, Criterion, Throughput};

fn bench_with_input(c: &mut Criterion) {
    let mut group = c.benchmark_group("sorting");
    
    for size in [10, 100, 1000, 10000].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            size,
            |b, &size| {
                let mut vec: Vec<_> = (0..size).collect();
                b.iter(|| vec.sort());
            },
        );
    }
    
    group.finish();
}
```

---

### 2. flamegraph (火焰图 🌟)

**安装**: `cargo install flamegraph`  
**用途**: 生成性能火焰图

#### Linux 使用

```bash
# 安装依赖
sudo apt-get install linux-tools-common linux-tools-generic

# 生成火焰图
cargo flamegraph

# 指定二进制
cargo flamegraph --bin my_app

# 带参数运行
cargo flamegraph -- arg1 arg2

# 设置采样频率
cargo flamegraph --freq 999

# Release 模式
cargo flamegraph --release
```

#### macOS 使用

```bash
# 安装 DTrace
# (macOS 自带)

# 生成火焰图
cargo flamegraph

# 或使用 instruments
instruments -t "Time Profiler" ./target/release/my_app
```

#### 配置文件

```toml
# Cargo.toml
[profile.release]
debug = true  # 保留调试信息，用于火焰图
```

---

### 3. cargo-bench (内置)

**用途**: Rust 内置基准测试

```rust
// benches/simple_bench.rs
#![feature(test)]
extern crate test;

#[bench]
fn bench_add(b: &mut test::Bencher) {
    b.iter(|| {
        let n = test::black_box(100);
        (0..n).fold(0, |a, b| a + b)
    });
}
```

```bash
cargo bench
```

---

### 4. pprof (CPU/内存分析 💡)

**添加依赖**: `cargo add --dev pprof`  
**用途**: CPU 和内存性能分析

#### CPU 性能分析

```rust
use pprof::protos::Message;

fn main() {
    let guard = pprof::ProfilerGuard::new(100).unwrap();
    
    // 运行需要分析的代码
    expensive_computation();
    
    // 生成报告
    if let Ok(report) = guard.report().build() {
        let file = std::fs::File::create("profile.pb").unwrap();
        let profile = report.pprof().unwrap();
        profile.write_to_writer(&mut file).unwrap();
    }
}
```

#### 与 criterion 集成

```rust
use pprof::criterion::{Output, PProfProfiler};

fn config() -> Criterion {
    Criterion::default()
        .with_profiler(PProfProfiler::new(100, Output::Flamegraph(None)))
}

criterion_group! {
    name = benches;
    config = config();
    targets = my_benchmark
}
```

---

### 5. valgrind/cachegrind (高级)

**安装**: `sudo apt-get install valgrind`  
**用途**: 内存和缓存性能分析

#### 内存泄漏检测

```bash
# 检测内存泄漏
cargo build --release
valgrind --leak-check=full ./target/release/my_app

# 更详细的输出
valgrind --leak-check=full --show-leak-kinds=all --track-origins=yes \
    ./target/release/my_app
```

#### 缓存性能分析

```bash
# 缓存命中率分析
valgrind --tool=cachegrind ./target/release/my_app

# 查看结果
cg_annotate cachegrind.out.12345
```

#### Callgrind (调用图)

```bash
# 生成调用图
valgrind --tool=callgrind ./target/release/my_app

# 可视化 (需要 kcachegrind)
kcachegrind callgrind.out.12345
```

---

### 6. heaptrack (堆内存分析)

**安装**: `sudo apt-get install heaptrack`  
**用途**: 堆内存使用分析

```bash
# 分析堆内存
heaptrack ./target/release/my_app

# 查看结果
heaptrack_gui heaptrack.my_app.12345.gz
```

---

### 7. perf (Linux 系统级)

**安装**: `sudo apt-get install linux-tools-common`  
**用途**: Linux 系统级性能分析

#### 基础用法2

```bash
# 记录性能数据
perf record -g ./target/release/my_app

# 查看报告
perf report

# 实时监控
perf top

# CPU 性能计数器
perf stat ./target/release/my_app

# 生成火焰图
perf script | stackcollapse-perf.pl | flamegraph.pl > flame.svg
```

#### 高级分析

```bash
# 缓存未命中分析
perf stat -e cache-misses,cache-references ./target/release/my_app

# 分支预测分析
perf stat -e branch-misses,branches ./target/release/my_app

# 内存带宽分析
perf mem record ./target/release/my_app
perf mem report
```

---

## 💡 最佳实践

### 1. 基准测试模板

```rust
use criterion::{
    black_box, criterion_group, criterion_main,
    BenchmarkId, Criterion, Throughput,
};

fn bench_algorithms(c: &mut Criterion) {
    let mut group = c.benchmark_group("algorithms");
    
    for size in [10, 100, 1000].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        
        // 算法 A
        group.bench_with_input(
            BenchmarkId::new("algo_a", size),
            size,
            |b, size| {
                let data = generate_data(*size);
                b.iter(|| algorithm_a(black_box(&data)));
            },
        );
        
        // 算法 B
        group.bench_with_input(
            BenchmarkId::new("algo_b", size),
            size,
            |b, size| {
                let data = generate_data(*size);
                b.iter(|| algorithm_b(black_box(&data)));
            },
        );
    }
    
    group.finish();
}

criterion_group!(benches, bench_algorithms);
criterion_main!(benches);
```

### 2. 性能分析流程

```bash
#!/bin/bash

# 1. 编译 release 版本（带调试信息）
RUSTFLAGS="-C force-frame-pointers=yes" cargo build --release

# 2. 运行基准测试
cargo bench

# 3. 生成火焰图
cargo flamegraph --release

# 4. 运行 perf 分析
perf record -g --call-graph dwarf ./target/release/my_app
perf report

# 5. 内存分析
heaptrack ./target/release/my_app
```

### 3. Profile 配置优化

```toml
# Cargo.toml
[profile.release]
debug = 1              # 保留部分调试信息
lto = true             # 链接时优化
codegen-units = 1      # 单个代码生成单元
opt-level = 3          # 最大优化

[profile.bench]
inherits = "release"
debug = true           # 基准测试保留完整调试信息
```

---

## 📊 工具对比

### 性能分析工具选择

| 工具 | 用途 | 平台 | 易用性 | 详细度 | 推荐场景 |
|------|------|------|--------|--------|---------|
| **criterion** | 基准测试 | 跨平台 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 算法对比 |
| **flamegraph** | CPU热点 | Linux/Mac | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 整体性能 |
| **perf** | 系统级 | Linux | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 深度分析 |
| **valgrind** | 内存/缓存 | Linux | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 内存问题 |
| **heaptrack** | 堆内存 | Linux | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 内存泄漏 |

---

## 🎯 实战场景

### 场景1: API 性能优化

```rust
use criterion::{Criterion, criterion_group, criterion_main};
use tokio::runtime::Runtime;

fn bench_api_handler(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    c.bench_function("api_handler", |b| {
        b.to_async(&rt).iter(|| async {
            api_handler(black_box(request)).await
        });
    });
}

criterion_group!(benches, bench_api_handler);
criterion_main!(benches);
```

### 场景2: 算法对比

```rust
fn bench_sorting(c: &mut Criterion) {
    let mut group = c.benchmark_group("sorting");
    let data: Vec<i32> = (0..10000).collect();
    
    group.bench_function("std::sort", |b| {
        b.iter(|| {
            let mut v = data.clone();
            v.sort();
        });
    });
    
    group.bench_function("rayon::par_sort", |b| {
        b.iter(|| {
            let mut v = data.clone();
            v.par_sort();
        });
    });
    
    group.finish();
}
```

### 场景3: 内存密集型应用

```bash
# 1. 检测内存泄漏
valgrind --leak-check=full --show-leak-kinds=all \
    ./target/release/my_app

# 2. 堆内存分析
heaptrack ./target/release/my_app
heaptrack_gui heaptrack.*.gz

# 3. 内存分配热点
perf record -g --call-graph dwarf -e 'syscalls:sys_enter_mmap' \
    ./target/release/my_app
```

---

## 🔗 相关资源

- [Criterion.rs Guide](https://bheisler.github.io/criterion.rs/book/)
- [flamegraph on crates.io](https://crates.io/crates/flamegraph)
- [Brendan Gregg's Blog](https://www.brendangregg.com/flamegraphs.html)
- [perf Tutorial](https://perf.wiki.kernel.org/index.php/Tutorial)
- [Valgrind User Manual](https://valgrind.org/docs/manual/manual.html)

---

**导航**: [返回工具链层](../README.md) | [下一类别：调试工具](../debugging/README.md)
