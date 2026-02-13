# 性能调优完整指南

**创建日期**: 2025-12-11
**最后更新**: 2026-01-26
**Rust 版本**: 1.93.0+
**Edition**: 2024

---

## 📋 目录

- [性能调优完整指南](#性能调优完整指南)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🚀 编译优化](#-编译优化)
    - [1. Release 模式](#1-release-模式)
    - [2. 特性标志优化](#2-特性标志优化)
    - [3. 增量编译](#3-增量编译)
  - [💾 内存优化](#-内存优化)
    - [1. 预分配容量](#1-预分配容量)
    - [2. 使用切片而非 Vec](#2-使用切片而非-vec)
    - [3. 使用 Cow 避免克隆](#3-使用-cow-避免克隆)
    - [4. 使用 Box 减少栈分配](#4-使用-box-减少栈分配)
  - [⚡ 运行时优化](#-运行时优化)
    - [1. 迭代器优化](#1-迭代器优化)
    - [2. 避免不必要的克隆](#2-避免不必要的克隆)
    - [3. 使用 `#[inline]` 提示](#3-使用-inline-提示)
    - [4. 使用 `#[cold]` 标记冷路径](#4-使用-cold-标记冷路径)
  - [🔄 并发优化](#-并发优化)
    - [1. 使用 Arc 而非 Rc](#1-使用-arc-而非-rc)
    - [2. 减少锁竞争](#2-减少锁竞争)
    - [3. 使用无锁数据结构](#3-使用无锁数据结构)
    - [4. 工作窃取调度](#4-工作窃取调度)
  - [🌐 异步优化](#-异步优化)
    - [1. 使用 select! 而非 join](#1-使用-select-而非-join)
    - [2. 使用有界通道](#2-使用有界通道)
    - [3. 批量处理](#3-批量处理)
  - [📊 性能分析](#-性能分析)
    - [1. 使用 criterion 基准测试](#1-使用-criterion-基准测试)
    - [2. 使用 perf 分析](#2-使用-perf-分析)
    - [3. 使用 cargo-flamegraph](#3-使用-cargo-flamegraph)
    - [4. 使用 valgrind (Linux)](#4-使用-valgrind-linux)
  - [🎯 优化策略](#-优化策略)
    - [1. 测量优先](#1-测量优先)
    - [2. 热点分析](#2-热点分析)
    - [3. 渐进优化](#3-渐进优化)
  - [📚 相关资源](#-相关资源)

---

## 📋 概述

本文档提供全面的 Rust 性能调优指南，涵盖编译优化、运行时优化、内存管理、并发优化等方面。

---

## 🚀 编译优化

### 1. Release 模式

```toml
# Cargo.toml
[profile.release]
opt-level = 3          # 最高优化级别
lto = true             # 链接时优化
codegen-units = 1      # 减少代码生成单元
panic = "abort"        # 减小二进制大小
strip = true           # 移除符号信息
```

### 2. 特性标志优化

```toml
# 只启用需要的特性
[dependencies]
tokio = { version = "1.0", features = ["rt", "net"] }  # 而非 "full"
serde = { version = "1.0", features = ["derive"] }
```

### 3. 增量编译

```toml
[profile.dev]
incremental = true
```

---

## 💾 内存优化

### 1. 预分配容量

```rust
// ❌ 不好：多次重新分配
let mut vec = Vec::new();
for i in 0..1000 {
    vec.push(i);
}

// ✅ 好：预分配容量
let mut vec = Vec::with_capacity(1000);
for i in 0..1000 {
    vec.push(i);
}
```

### 2. 使用切片而非 Vec

```rust
// ❌ 不好：不必要的分配
fn process(data: Vec<i32>) -> i32 {
    data.iter().sum()
}

// ✅ 好：使用切片
fn process(data: &[i32]) -> i32 {
    data.iter().sum()
}
```

### 3. 使用 Cow 避免克隆

```rust
use std::borrow::Cow;

fn process_data(data: Cow<str>) -> String {
    match data {
        Cow::Borrowed(s) => s.to_uppercase(),
        Cow::Owned(s) => s.to_uppercase(),
    }
}
```

### 4. 使用 Box 减少栈分配

```rust
// 大结构体使用 Box
struct LargeData {
    data: Box<[u8; 1024 * 1024]>,  // 1MB 在堆上
}
```

---

## ⚡ 运行时优化

### 1. 迭代器优化

```rust
// ❌ 不好：多次遍历
let sum: i32 = data.iter().sum();
let max: i32 = *data.iter().max().unwrap();
let min: i32 = *data.iter().min().unwrap();

// ✅ 好：单次遍历
let (sum, max, min) = data.iter().fold(
    (0, i32::MIN, i32::MAX),
    |(s, mx, mn), &x| (s + x, mx.max(x), mn.min(x))
);
```

### 2. 避免不必要的克隆

```rust
// ❌ 不好：不必要的克隆
let cloned = data.clone();
process(cloned);

// ✅ 好：使用引用
process(&data);
```

### 3. 使用 `#[inline]` 提示

```rust
#[inline]
fn hot_function(x: i32) -> i32 {
    x * 2
}
```

### 4. 使用 `#[cold]` 标记冷路径

```rust
#[cold]
fn error_handler() {
    // 错误处理路径，很少执行
}
```

---

## 🔄 并发优化

### 1. 使用 Arc 而非 Rc

```rust
// ❌ 不好：Rc 不能跨线程
use std::rc::Rc;
let data = Rc::new(shared_data);

// ✅ 好：Arc 可以跨线程
use std::sync::Arc;
let data = Arc::new(shared_data);
```

### 2. 减少锁竞争

```rust
// ❌ 不好：长时间持有锁
let mutex = Arc::new(Mutex::new(data));
let guard = mutex.lock().unwrap();
// 长时间操作
drop(guard);

// ✅ 好：最小化锁持有时间
let mutex = Arc::new(Mutex::new(data));
{
    let mut guard = mutex.lock().unwrap();
    // 快速操作
}
// 锁已释放
```

### 3. 使用无锁数据结构

```rust
use c05_threads::lockfree::LockFreeQueue;

let queue = Arc::new(LockFreeQueue::new());
// 无锁操作，性能更好
```

### 4. 工作窃取调度

```rust
use c05_threads::concurrency::work_stealing::WorkStealingQueue;

let queue = WorkStealingQueue::new();
// 自动负载均衡
```

---

## 🌐 异步优化

### 1. 使用 select! 而非 join

```rust
// 当只需要第一个完成的结果时
tokio::select! {
    result = task1() => handle_result1(result),
    result = task2() => handle_result2(result),
}
```

### 2. 使用有界通道

```rust
use tokio::sync::mpsc;

// 有界通道提供背压
let (tx, rx) = mpsc::channel(100);
```

### 3. 批量处理

```rust
use futures::StreamExt;

let mut stream = data_stream.buffer_unordered(10);  // 并发处理 10 个
while let Some(item) = stream.next().await {
    process(item).await;
}
```

---

## 📊 性能分析

### 1. 使用 criterion 基准测试

```rust
use criterion::{criterion_group, criterion_main, Criterion};

fn benchmark_function(c: &mut Criterion) {
    c.bench_function("my_function", |b| {
        b.iter(|| {
            // 被测试的代码
        });
    });
}

criterion_group!(benches, benchmark_function);
criterion_main!(benches);
```

### 2. 使用 perf 分析

```bash
# Linux
perf record --call-graph=dwarf ./target/release/my_app
perf report

# 生成火焰图
perf script | stackcollapse-perf.pl | flamegraph.pl > flamegraph.svg
```

### 3. 使用 cargo-flamegraph

```bash
cargo install flamegraph
cargo flamegraph --bin my_app
```

### 4. 使用 valgrind (Linux)

```bash
valgrind --tool=callgrind ./target/release/my_app
kcachegrind callgrind.out.*
```

---

## 🎯 优化策略

### 1. 测量优先

```rust
// 先测量，再优化
use std::time::Instant;

let start = Instant::now();
// 代码
let elapsed = start.elapsed();
println!("耗时: {:?}", elapsed);
```

### 2. 热点分析

- 使用性能分析工具找出热点
- 优先优化热点代码
- 遵循 80/20 原则

### 3. 渐进优化

- 先确保正确性
- 再优化性能
- 每次优化后测量

---

## 📚 相关资源

- [Rust 性能书](https://nnethercote.github.io/perf-book/)
- [Criterion 文档](https://github.com/bheisler/criterion.rs)
- [Flamegraph 工具](https://github.com/flamegraph-rs/flamegraph)

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 持续更新
**最后更新**: 2026-01-26
