# 基准测试最小指南

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> 内容已整合至： [performance_benchmarks.md](../../research_notes/experiments/performance_benchmarks.md)

[返回主索引](../00_master_index.md)

---

## 形式化链接

| 文档 | 路径 | 内容 |
| :--- | :--- | :--- |
| **性能基准实验** | [../../research_notes/experiments/performance_benchmarks.md](../../research_notes/experiments/performance_benchmarks.md) | 基准测试方法论、统计分析 |
| **编译器优化** | [../../research_notes/experiments/compiler_optimizations.md](../../research_notes/experiments/compiler_optimizations.md) | 编译器优化分析 |
| **性能调优指南** | [../05_guides/PERFORMANCE_TUNING_GUIDE.md](../05_guides/PERFORMANCE_TUNING_GUIDE.md) | 实用优化技巧 |
| **证明索引** | [../../research_notes/PROOF_INDEX.md](../../research_notes/PROOF_INDEX.md) | 性能相关证明 |
| **工具指南** | [../../research_notes/TOOLS_GUIDE.md](../../research_notes/TOOLS_GUIDE.md) | 基准测试工具使用 |

---

## 基准测试核心概念

### 为什么需要基准测试

```rust
// ❌ 错误：简单计时容易受干扰
fn bad_benchmark() {
    let start = std::time::Instant::now();
    let result = fibonacci(20);
    let elapsed = start.elapsed();
    println!("Result: {}, Time: {:?}", result, elapsed);
    // 问题：未考虑编译器优化、缓存、CPU频率变化、统计变异
}

fn fibonacci(n: u64) -> u64 {
    match n {
        0 | 1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}
```

### 使用 Criterion 进行可靠基准测试

```rust
// Cargo.toml:
// [dev-dependencies]
// criterion = { version = "0.5", features = ["html_reports"] }
//
// [[bench]]
// name = "my_benchmark"
// harness = false

use criterion::{black_box, criterion_group, criterion_main, Criterion};

// 被测试的函数
fn fibonacci(n: u64) -> u64 {
    match n {
        0 | 1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

// 基准测试函数
fn fibonacci_benchmark(c: &mut Criterion) {
    c.bench_function("fib 10", |b| {
        b.iter(|| fibonacci(black_box(10)))
    });

    c.bench_function("fib 20", |b| {
        b.iter(|| fibonacci(black_box(20)))
    });
}

criterion_group!(benches, fibonacci_benchmark);
criterion_main!(benches);
```

### 防止编译器优化（black_box）

```rust
use criterion::black_box;

// black_box 告诉编译器不要优化掉计算
fn bench_with_blackbox(c: &mut Criterion) {
    c.bench_function("sum with black_box", |b| {
        b.iter(|| {
            let input = black_box(vec![1, 2, 3, 4, 5]);
            let sum: i32 = input.iter().sum();
            black_box(sum);  // 防止结果被优化掉
        })
    });
}

// 自定义 black_box（如果不使用 criterion）
pub fn custom_black_box<T>(dummy: T) -> T {
    unsafe {
        let ret = std::ptr::read_volatile(&dummy);
        std::mem::forget(dummy);
        ret
    }
}
```

### 参数化基准测试

```rust
use criterion::{BenchmarkId, Criterion};

// 测试不同输入规模下的性能
fn bench_various_sizes(c: &mut Criterion) {
    let mut group = c.benchmark_group("vector_sum");

    for size in [100, 1000, 10_000, 100_000].iter() {
        let data: Vec<i32> = (0..*size).collect();

        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            &data,
            |b, data| {
                b.iter(|| {
                    data.iter().sum::<i32>()
                })
            },
        );
    }

    group.finish();
}
```

### 比较不同实现

```rust
use criterion::{BenchmarkId, Criterion};

// 实现 1：迭代器
fn sum_iterator(data: &[i32]) -> i32 {
    data.iter().sum()
}

// 实现 2：显式循环
fn sum_loop(data: &[i32]) -> i32 {
    let mut sum = 0;
    for &x in data {
        sum += x;
    }
    sum
}

// 实现 3：递归
fn sum_recursive(data: &[i32]) -> i32 {
    match data.split_first() {
        None => 0,
        Some((first, rest)) => first + sum_recursive(rest),
    }
}

fn bench_comparison(c: &mut Criterion) {
    let data: Vec<i32> = (0..1000).collect();

    let mut group = c.benchmark_group("sum_comparison");

    group.bench_function("iterator", |b| {
        b.iter(|| sum_iterator(black_box(&data)))
    });

    group.bench_function("loop", |b| {
        b.iter(|| sum_loop(black_box(&data)))
    });

    group.bench_function("recursive", |b| {
        b.iter(|| sum_recursive(black_box(&data)))
    });

    group.finish();
}
```

### 异步基准测试

```rust
use criterion::{async_executor::FuturesExecutor, Criterion};

async fn async_fibonacci(n: u64) -> u64 {
    match n {
        0 | 1 => 1,
        n => {
            let (a, b) = tokio::join!(
                async_fibonacci(n - 1),
                async_fibonacci(n - 2)
            );
            a + b
        }
    }
}

fn bench_async(c: &mut Criterion) {
    c.bench_function("async fib 10", |b| {
        b.to_async(FuturesExecutor)
            .iter(|| async_fibonacci(black_box(10)))
    });
}
```

### 吞吐量测量

```rust
use criterion::{Criterion, Throughput};

fn bench_with_throughput(c: &mut Criterion) {
    let data = vec![0u8; 1024 * 1024]; // 1 MB

    let mut group = c.benchmark_group("throughput");

    // 报告处理的数据量
    group.throughput(Throughput::Bytes(data.len() as u64));

    group.bench_function("process_mb", |b| {
        b.iter(|| {
            // 模拟处理 1MB 数据
            data.iter().map(|&x| x.wrapping_add(1)).collect::<Vec<_>>()
        })
    });

    group.finish();
}
```

---

## 基准测试最佳实践

### 统计显著性

```rust
use criterion::{Criterion, SamplingMode};

fn configure_statistics(c: &mut Criterion) {
    let mut group = c.benchmark_group("statistical");

    // 配置采样模式
    group.sampling_mode(SamplingMode::Auto);

    // 设置样本数量
    group.sample_size(200);  // 默认 100

    // 设置测量时间
    group.measurement_time(std::time::Duration::from_secs(10));

    group.bench_function("reliable", |b| {
        b.iter(|| expensive_operation())
    });

    group.finish();
}

fn expensive_operation() -> Vec<u32> {
    (0..10000).map(|x| x * x).collect()
}
```

### 预热与稳定

```rust
use criterion::Criterion;

fn bench_with_warmup(c: &mut Criterion) {
    let mut group = c.benchmark_group("warmup");

    // 设置预热时间
    group.warm_up_time(std::time::Duration::from_secs(3));

    // 设置测量时间
    group.measurement_time(std::time::Duration::from_secs(5));

    group.bench_function("stabilized", |b| {
        b.iter(|| cache_sensitive_operation())
    });

    group.finish();
}

fn cache_sensitive_operation() -> Vec<f64> {
    vec![1.0; 1000].iter().map(|x| x.sqrt()).collect()
}
```

### 基准测试隔离

```rust
// benches/bench1.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench1(c: &mut Criterion) {
    c.bench_function("operation_a", |b| {
        b.iter(|| black_box(42) * 2)
    });
}

criterion_group!(benches, bench1);
criterion_main!(benches);

// 分开的文件进行隔离
// benches/bench2.rs
fn bench2(c: &mut Criterion) {
    c.bench_function("operation_b", |b| {
        b.iter(|| black_box(42) / 2)
    });
}
```

---

## 性能分析工具集成

### 使用 perf 分析

```bash
# 编译并运行基准测试
$ cargo bench -- --profile-time 10

# 使用 perf 进行详细分析
$ perf record -g target/release/deps/my_benchmark-xxx --bench
$ perf report
```

### 使用 cargo-flamegraph

```bash
# 安装
$ cargo install flamegraph

# 生成火焰图
$ cargo flamegraph --bench my_benchmark
```

### 内存分配分析

```rust
// 使用 dhat 进行堆分析
// Cargo.toml:
// [dev-dependencies]
// dhat = "0.3"

#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

fn profile_memory() {
    let _profiler = dhat::Profiler::new_heap();

    // 测试代码
    let data: Vec<Vec<u8>> = (0..1000)
        .map(|i| vec![0; i * 100])
        .collect();

    drop(data);
}
```

---

## 常见陷阱与避免方法

```rust
// ❌ 陷阱 1：测试代码被优化掉
fn bad_bench1(c: &mut Criterion) {
    c.bench_function("optimized_away", |b| {
        b.iter(|| {
            2 + 2  // 编译器会在编译时计算
        })
    });
}

// ✅ 修复：使用 black_box
fn good_bench1(c: &mut Criterion) {
    c.bench_function("not_optimized", |b| {
        b.iter(|| {
            black_box(2) + black_box(2)
        })
    });
}

// ❌ 陷阱 2：在循环内分配
fn bad_bench2(c: &mut Criterion) {
    c.bench_function("alloc_in_loop", |b| {
        b.iter(|| {
            let v: Vec<i32> = (0..1000).collect();  // 每次迭代都分配
            v.iter().sum::<i32>()
        })
    });
}

// ✅ 修复：在循环外分配
fn good_bench2(c: &mut Criterion) {
    let v: Vec<i32> = (0..1000).collect();
    c.bench_function("no_alloc_in_loop", |b| {
        b.iter(|| {
            v.iter().sum::<i32>()
        })
    });
}

// ❌ 陷阱 3：不稳定的输入
fn bad_bench3(c: &mut Criterion) {
    let mut rng = rand::thread_rng();
    c.bench_function("random_input", |b| {
        b.iter(|| {
            let input: u64 = rng.gen();  // 随机输入导致不稳定
            fibonacci(input % 20)
        })
    });
}

// ✅ 修复：使用固定输入
fn good_bench3(c: &mut Criterion) {
    c.bench_function("fixed_input", |b| {
        b.iter(|| {
            fibonacci(black_box(20))  // 固定输入
        })
    });
}
```

---

## 快速开始模板

```rust
// benches/template.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn function_to_benchmark(input: u64) -> u64 {
    // 你的代码
    input * 2
}

fn criterion_benchmark(c: &mut Criterion) {
    // 单个基准测试
    c.bench_function("simple", |b| {
        b.iter(|| function_to_benchmark(black_box(100)))
    });

    // 参数化测试
    let mut group = c.benchmark_group("parameterized");
    for i in [10, 100, 1000] {
        group.bench_with_input(
            criterion::BenchmarkId::from_parameter(i),
            &i,
            |b, i| b.iter(|| function_to_benchmark(black_box(*i))),
        );
    }
    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
```

---

## 相关研究笔记

### 实验分析

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 性能基准实验 | 基准测试方法论 | [../../research_notes/experiments/performance_benchmarks.md](../../research_notes/experiments/performance_benchmarks.md) |
| 编译器优化 | 编译器优化分析 | [../../research_notes/experiments/compiler_optimizations.md](../../research_notes/experiments/compiler_optimizations.md) |
| 并发性能 | 并发性能测试 | [../../research_notes/experiments/concurrency_performance.md](../../research_notes/experiments/concurrency_performance.md) |

### 工具链

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 性能调优指南 | 实用优化技巧 | [../05_guides/PERFORMANCE_TUNING_GUIDE.md](../05_guides/PERFORMANCE_TUNING_GUIDE.md) |

---

## 相关 crates

| crate | 描述 | 路径 |
| :--- | :--- | :--- |
| criterion | 统计基准测试框架 | crates.io |
| iai | 指令计数基准测试 | crates.io |
| divan | 快速基准测试 | crates.io |
