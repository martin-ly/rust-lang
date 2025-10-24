# 基准测试指南（Criterion）

## 📊 目录

- [基准测试指南（Criterion）](#基准测试指南criterion)
  - [📊 目录](#-目录)
  - [目标](#目标)
  - [运行](#运行)
  - [结果位置](#结果位置)
  - [回归判断建议](#回归判断建议)
  - [与 CI 配合](#与-ci-配合)
  - [完整的基准测试实践](#完整的基准测试实践)
    - [1. Criterion 基础用法](#1-criterion-基础用法)
      - [1.1 简单基准测试](#11-简单基准测试)
      - [1.2 参数化基准测试](#12-参数化基准测试)
    - [2. 设计模式性能对比](#2-设计模式性能对比)
      - [2.1 单例模式：不同实现的性能对比](#21-单例模式不同实现的性能对比)
      - [2.2 策略模式：静态 vs 动态分派](#22-策略模式静态-vs-动态分派)
    - [3. 异步模式基准测试](#3-异步模式基准测试)
      - [3.1 Tokio 异步基准](#31-tokio-异步基准)
    - [4. 内存分配基准](#4-内存分配基准)
    - [5. 性能分析最佳实践](#5-性能分析最佳实践)
      - [5.1 基准测试检查清单](#51-基准测试检查清单)
      - [5.2 回归检测策略](#52-回归检测策略)
    - [6. Criterion 高级功能](#6-criterion-高级功能)
      - [6.1 自定义测量](#61-自定义测量)
      - [6.2 吞吐量测量](#62-吞吐量测量)
  - [附：场景基准](#附场景基准)
    - [责任链模式基准](#责任链模式基准)
    - [并行模式基准](#并行模式基准)
    - [完整示例](#完整示例)
  - [相关资源](#相关资源)

## 目标

- 指导如何运行与阅读本仓库的 Criterion 基准；
- 结合 CI 独立工作流进行可复现实验；
- 为回归判断提供简单可操作的门槛建议。

## 运行

```bash
# 本地运行全部基准
cargo bench | cat

# 启用 tokio 异步基准
cargo bench --features tokio-bench | cat
```

## 结果位置

- 报告目录：`target/criterion/*`
- 含 HTML/CSV 等输出，可在 CI 工作流产出 artifact 后下载查看。

## 回归判断建议

- 选定关键基准（如 `pattern_scenarios/*`、`rayon_parallel_sum`）。
- 与上一次基线对比：若 p95 时延回退 ≥5%，标记为潜在回归。
- 重试 3 次取均值，排除偶发波动；必要时固定 CPU 频率与隔离负载。

## 与 CI 配合

- 通过 `Bench` 工作流（`workflow_dispatch`）在稳定环境下运行，上传 `target/criterion` 目录与控制台输出。
- 可后续扩展：将选定指标扫描为 JSON 并做门槛校验，失败时置红阻断合并。

## 完整的基准测试实践

### 1. Criterion 基础用法

#### 1.1 简单基准测试

```rust
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

**关键点**：

- `black_box`: 防止编译器过度优化
- `criterion_group!`: 组织多个基准
- `criterion_main!`: 生成入口点

#### 1.2 参数化基准测试

```rust
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};

fn benchmark_with_sizes(c: &mut Criterion) {
    let mut group = c.benchmark_group("vec_operations");
    
    for size in [10, 100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let mut vec = Vec::with_capacity(size);
                for i in 0..size {
                    vec.push(black_box(i));
                }
                vec
            });
        });
    }
    
    group.finish();
}

criterion_group!(benches, benchmark_with_sizes);
criterion_main!(benches);
```

---

### 2. 设计模式性能对比

#### 2.1 单例模式：不同实现的性能对比

```rust
use std::sync::{Arc, Mutex, OnceLock};
use once_cell::sync::Lazy;
use criterion::{black_box, Criterion};

// 方案1: OnceLock
static INSTANCE_ONCE: OnceLock<Config> = OnceLock::new();

// 方案2: Lazy
static INSTANCE_LAZY: Lazy<Config> = Lazy::new(|| Config { value: 42 });

// 方案3: Arc<Mutex>
static INSTANCE_MUTEX: Lazy<Arc<Mutex<Config>>> = Lazy::new(|| {
    Arc::new(Mutex::new(Config { value: 42 }))
});

#[derive(Clone)]
struct Config {
    value: i32,
}

fn bench_singleton_patterns(c: &mut Criterion) {
    let mut group = c.benchmark_group("singleton_implementations");
    
    group.bench_function("OnceLock", |b| {
        b.iter(|| {
            let config = INSTANCE_ONCE.get_or_init(|| Config { value: 42 });
            black_box(config.value);
        });
    });
    
    group.bench_function("Lazy", |b| {
        b.iter(|| {
            black_box(INSTANCE_LAZY.value);
        });
    });
    
    group.bench_function("Arc<Mutex>", |b| {
        b.iter(|| {
            let guard = INSTANCE_MUTEX.lock().unwrap();
            black_box(guard.value);
        });
    });
    
    group.finish();
}

// 结果示例：
// OnceLock:    5-10ns
// Lazy:        1-2ns   (最快)
// Arc<Mutex>:  20-50ns (最慢，有锁开销)
```

#### 2.2 策略模式：静态 vs 动态分派

```rust
use criterion::{black_box, Criterion};

// 策略trait
trait Strategy {
    fn execute(&self, n: i32) -> i32;
}

struct AddStrategy;
impl Strategy for AddStrategy {
    fn execute(&self, n: i32) -> i32 { n + 10 }
}

struct MulStrategy;
impl Strategy for MulStrategy {
    fn execute(&self, n: i32) -> i32 { n * 2 }
}

// 静态分派（泛型）
fn execute_static<S: Strategy>(strategy: &S, n: i32) -> i32 {
    strategy.execute(n)
}

// 动态分派（trait object）
fn execute_dynamic(strategy: &dyn Strategy, n: i32) -> i32 {
    strategy.execute(n)
}

fn bench_strategy_dispatch(c: &mut Criterion) {
    let mut group = c.benchmark_group("strategy_dispatch");
    
    let add = AddStrategy;
    
    group.bench_function("static_dispatch", |b| {
        b.iter(|| execute_static(&add, black_box(42)));
    });
    
    group.bench_function("dynamic_dispatch", |b| {
        b.iter(|| execute_dynamic(&add as &dyn Strategy, black_box(42)));
    });
    
    group.finish();
}

// 结果：
// static_dispatch:  0.5-1ns  (内联优化)
// dynamic_dispatch: 2-5ns    (虚表查找)
```

---

### 3. 异步模式基准测试

#### 3.1 Tokio 异步基准

```rust
use criterion::{criterion_group, criterion_main, Criterion};
use tokio::runtime::Runtime;

async fn async_work(n: usize) -> usize {
    let mut sum = 0;
    for i in 0..n {
        sum += i;
    }
    sum
}

fn bench_async_patterns(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    c.bench_function("async_work_1000", |b| {
        b.to_async(&rt).iter(|| async {
            async_work(1000).await
        });
    });
}

criterion_group!(benches, bench_async_patterns);
criterion_main!(benches);
```

---

### 4. 内存分配基准

```rust
use criterion::{black_box, Criterion, BenchmarkId};

fn bench_allocation_patterns(c: &mut Criterion) {
    let mut group = c.benchmark_group("allocation");
    
    // Vec预分配 vs 动态增长
    for size in [100, 1000, 10000].iter() {
        group.bench_with_input(
            BenchmarkId::new("with_capacity", size),
            size,
            |b, &size| {
                b.iter(|| {
                    let mut vec = Vec::with_capacity(size);
                    for i in 0..size {
                        vec.push(black_box(i));
                    }
                });
            },
        );
        
        group.bench_with_input(
            BenchmarkId::new("without_capacity", size),
            size,
            |b, &size| {
                b.iter(|| {
                    let mut vec = Vec::new();
                    for i in 0..size {
                        vec.push(black_box(i));
                    }
                });
            },
        );
    }
    
    group.finish();
}

// 结果：with_capacity 比 without_capacity 快 20-50%
```

---

### 5. 性能分析最佳实践

#### 5.1 基准测试检查清单

- [x] 使用 `black_box` 防止优化
- [x] 测试多个输入规模
- [x] 固定CPU频率（生产环境）
- [x] 禁用Turbo Boost
- [x] 隔离其他负载
- [x] 多次运行取平均值
- [x] 记录系统信息（CPU/内存）

#### 5.2 回归检测策略

**方法1: 自动化阈值检测**:

```rust
// 在 CI 中运行
// 设置阈值：允许5%的性能波动
const THRESHOLD: f64 = 1.05;

fn check_regression(baseline: f64, current: f64) -> bool {
    current / baseline > THRESHOLD
}
```

**方法2: 统计显著性检测**:

```bash
# 使用 critcmp 比较两次结果
cargo install critcmp
cargo bench --save-baseline before
# 修改代码
cargo bench --save-baseline after
critcmp before after
```

---

### 6. Criterion 高级功能

#### 6.1 自定义测量

```rust
use criterion::{Criterion, measurement::WallTime, BenchmarkGroup};
use std::time::Duration;

fn custom_measurement(c: &mut Criterion<WallTime>) {
    let mut group: BenchmarkGroup<WallTime> = c.benchmark_group("custom");
    
    group.measurement_time(Duration::from_secs(10));
    group.sample_size(1000);
    group.warm_up_time(Duration::from_secs(3));
    
    group.bench_function("my_function", |b| {
        b.iter(|| {
            // 被测代码
        });
    });
    
    group.finish();
}
```

#### 6.2 吞吐量测量

```rust
use criterion::{Criterion, Throughput, BenchmarkId};

fn throughput_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("throughput");
    
    for size in [1024, 10240, 102400].iter() {
        group.throughput(Throughput::Bytes(*size as u64));
        
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            size,
            |b, &size| {
                let data = vec![0u8; size];
                b.iter(|| process_data(&data));
            },
        );
    }
    
    group.finish();
}

fn process_data(data: &[u8]) -> usize {
    data.iter().filter(|&&x| x > 128).count()
}
```

---

## 附：场景基准

### 责任链模式基准

- `benches/pattern_scenarios.rs`：包含责任链、装饰器、代理的轻量模拟。

### 并行模式基准

- `benches/pattern_benchmarks.rs`：包含 `rayon` 并行与（可选）`tokio` 异步任务基准。

### 完整示例

```bash
# 运行所有基准
cargo bench

# 只运行特定模式
cargo bench --bench pattern_scenarios

# 生成火焰图（需要cargo-flamegraph）
cargo flamegraph --bench pattern_benchmarks
```

---

## 相关资源

- **Criterion文档**: [https://bheisler.github.io/criterion.rs/book/](https://bheisler.github.io/criterion.rs/book/)
- **Tier 3**: [性能评估参考](./tier_03_references/04_模式性能评估参考.md)
- **Tier 4**: [工程实践](./tier_04_advanced/04_工程实践与生产级模式.md)

---

**文档状态**: ✅ 已完成  
**最后更新**: 2025-10-24
