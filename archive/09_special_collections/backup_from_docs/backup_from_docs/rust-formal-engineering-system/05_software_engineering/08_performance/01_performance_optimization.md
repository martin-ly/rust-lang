# 性能优化（Performance Optimization）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [性能优化](#性能优化performance-optimization)
  - [概述](#概述)
  - [性能分析](#性能分析)
  - [内存优化](#内存优化)
  - [CPU 优化](#cpu-优化)
  - [I/O 优化](#io-优化)
  - [实践示例](#实践示例)
  - [最佳实践](#最佳实践)
  - [参考资料](#参考资料)

---

## 概述

性能优化是软件开发中的重要环节。Rust 提供了多种工具和技术来帮助开发者优化程序性能，包括编译器优化、内存管理、并发处理等。

## 性能分析

### 使用 perf

```bash
# 安装 perf
sudo apt-get install linux-perf

# 运行性能分析
perf record --call-graph dwarf ./target/release/my_program
perf report
```

### 使用 flamegraph

```bash
# 安装 flamegraph
cargo install flamegraph

# 生成火焰图
cargo flamegraph --bin my_program
```

### 使用 criterion 进行基准测试

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n-1) + fibonacci(n-2),
    }
}

fn bench_fib(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

criterion_group!(benches, bench_fib);
criterion_main!(benches);
```

## 内存优化

### 减少分配

```rust
// ❌ 不推荐：频繁分配
fn inefficient() -> Vec<String> {
    let mut result = Vec::new();
    for i in 0..1000 {
        result.push(format!("Item {}", i));
    }
    result
}

// ✅ 推荐：预分配容量
fn efficient() -> Vec<String> {
    let mut result = Vec::with_capacity(1000);
    for i in 0..1000 {
        result.push(format!("Item {}", i));
    }
    result
}
```

### 使用对象池

```rust
use std::collections::VecDeque;

pub struct ObjectPool<T> {
    pool: VecDeque<T>,
    factory: Box<dyn Fn() -> T>,
}

impl<T> ObjectPool<T> {
    pub fn new<F>(factory: F) -> Self
    where
        F: Fn() -> T + 'static,
    {
        ObjectPool {
            pool: VecDeque::new(),
            factory: Box::new(factory),
        }
    }

    pub fn get(&mut self) -> T {
        self.pool.pop_front().unwrap_or_else(|| (self.factory)())
    }

    pub fn return_object(&mut self, obj: T) {
        self.pool.push_back(obj);
    }
}
```

### 零拷贝优化

```rust
use bytes::Bytes;

// 使用 Bytes 避免不必要的拷贝
fn zero_copy_example() {
    let data = Bytes::from("hello world");
    let slice = &data[..];  // 零拷贝切片
}
```

## CPU 优化

### 使用 SIMD

```rust
// 使用 packed_simd 或 std::arch
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

#[target_feature(enable = "avx2")]
unsafe fn simd_add(a: &[f32], b: &[f32], result: &mut [f32]) {
    // SIMD 向量化加法
}
```

### 循环优化

```rust
// ❌ 不推荐：低效的循环
fn inefficient_loop(data: &[i32]) -> i32 {
    let mut sum = 0;
    for i in 0..data.len() {
        sum += data[i];
    }
    sum
}

// ✅ 推荐：使用迭代器
fn efficient_loop(data: &[i32]) -> i32 {
    data.iter().sum()
}

// ✅ 推荐：并行处理
use rayon::prelude::*;

fn parallel_loop(data: &[i32]) -> i32 {
    data.par_iter().sum()
}
```

### 内联优化

```rust
// 使用 #[inline] 提示编译器内联函数
#[inline]
fn add(a: i32, b: i32) -> i32 {
    a + b
}

// 对于小函数，使用 #[inline(always)]
#[inline(always)]
fn multiply(a: i32, b: i32) -> i32 {
    a * b
}
```

## I/O 优化

### 缓冲 I/O

```rust
use std::io::{BufReader, BufWriter, Write};
use std::fs::File;

// 使用缓冲读取
fn buffered_read() -> std::io::Result<()> {
    let file = File::open("input.txt")?;
    let reader = BufReader::new(file);
    // 使用 reader 进行缓冲读取
    Ok(())
}

// 使用缓冲写入
fn buffered_write() -> std::io::Result<()> {
    let file = File::create("output.txt")?;
    let mut writer = BufWriter::new(file);
    writer.write_all(b"Hello, world!")?;
    writer.flush()?;
    Ok(())
}
```

### 异步 I/O

```rust
use tokio::fs::File;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

async fn async_io() -> std::io::Result<()> {
    let mut file = File::open("input.txt").await?;
    let mut contents = Vec::new();
    file.read_to_end(&mut contents).await?;

    let mut output = File::create("output.txt").await?;
    output.write_all(&contents).await?;
    Ok(())
}
```

### 批量操作

```rust
// 批量写入而不是逐行写入
fn batch_write(data: &[String]) -> std::io::Result<()> {
    use std::fs::File;
    use std::io::Write;

    let mut file = File::create("output.txt")?;
    let content: String = data.join("\n");
    file.write_all(content.as_bytes())?;
    Ok(())
}
```

## 实践示例

### 示例 1：字符串处理优化

```rust
// ❌ 不推荐：频繁分配字符串
fn inefficient_string_processing(input: &str) -> String {
    let mut result = String::new();
    for word in input.split_whitespace() {
        result.push_str(&word.to_uppercase());
        result.push(' ');
    }
    result
}

// ✅ 推荐：预分配容量
fn efficient_string_processing(input: &str) -> String {
    let words: Vec<&str> = input.split_whitespace().collect();
    let capacity = words.iter().map(|w| w.len() + 1).sum();
    let mut result = String::with_capacity(capacity);

    for word in words {
        result.push_str(&word.to_uppercase());
        result.push(' ');
    }
    result
}
```

### 示例 2：集合操作优化

```rust
use std::collections::HashSet;

// ❌ 不推荐：多次查找
fn inefficient_lookup(data: &[i32], targets: &[i32]) -> Vec<bool> {
    targets.iter()
        .map(|&target| data.contains(&target))
        .collect()
}

// ✅ 推荐：使用 HashSet
fn efficient_lookup(data: &[i32], targets: &[i32]) -> Vec<bool> {
    let set: HashSet<_> = data.iter().copied().collect();
    targets.iter()
        .map(|&target| set.contains(&target))
        .collect()
}
```

### 示例 3：并行处理优化

```rust
use rayon::prelude::*;

// 并行处理大量数据
fn parallel_processing(data: &[i32]) -> Vec<i32> {
    data.par_iter()
        .map(|&x| x * x)
        .filter(|&x| x > 100)
        .collect()
}
```

## 最佳实践

### 1. 测量，不要猜测

```rust
// 使用基准测试工具测量性能
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_operation(c: &mut Criterion) {
    c.bench_function("operation", |b| {
        b.iter(|| {
            // 要测试的操作
            black_box(expensive_operation())
        })
    });
}

criterion_group!(benches, bench_operation);
criterion_main!(benches);
```

### 2. 使用 Release 模式测试

```bash
# 使用优化后的构建进行测试
cargo build --release
cargo test --release
```

### 3. 分析热点代码

```rust
// 使用 #[inline(never)] 标记热点函数以便分析
#[inline(never)]
fn hot_function() {
    // 热点代码
}
```

### 4. 避免过早优化

```rust
// 先确保代码正确，再优化性能
// 使用性能分析工具找出真正的瓶颈
```

## 参考资料

- [性能优化索引](./00_index.md)
- [Criterion 文档](https://docs.rs/criterion/)
- [Rayon 文档](https://docs.rs/rayon/)
- [性能分析工具](../../06_toolchain_ecosystem/06_performance_analysis/00_index.md)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回软件工程: [`../00_index.md`](../00_index.md)
