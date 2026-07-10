> **EN**: Benchmarking with Criterion in Rust
> **Summary**: Core Rust concept covering statistical benchmarking with Criterion, regression detection, CI integration, and measurement best practices.
> **权威来源**: [Criterion.rs Book](https://bheisler.github.io/criterion.rs/book/) · [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html) · [Rust Reference](https://doc.rust-lang.org/reference/)
> **受众**: [进阶]
> **内容分级**: [指南级]
> **Bloom 层级**: 应用 → 分析
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **A+P** — ApplicationProcedure
> **定位**: 覆盖 Rust 生态中使用 `criterion` 进行基准测试的完整流程，从简单基准、参数化基准到回归检测与 CI 集成。
> **前置概念**: [Testing](16_testing.md) · [Performance Optimization](../10_performance/15_performance_optimization.md)
> **后置概念**: [Algorithm Engineering Practice](../11_domain_applications/76_algorithm_engineering_practice.md) · [Rust vs C++：性能与抽象对比](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)

---

# 基准测试：Rust 代码性能测量与回归检测

## 一、为什么需要基准测试

在优化 Rust 代码之前，必须先**可重复地测量**性能。`criterion` 是 Rust 生态事实上的统计性基准测试框架，它提供：

- 多次采样与统计置信区间
- 参数化基准（`bench_with_input`）
- 自定义测量时间与吞吐量
- 基线对比与回归检测

## 二、Criterion 基础用法

### 2.1 简单基准

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 | 1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
```

**关键点**：

- `black_box`：阻止编译器对测试目标进行死码消除或常量折叠。
- `criterion_group!` / `criterion_main!`：组织基准并生成 `main` 入口。

### 2.2 参数化基准

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

## 三、回归检测与 CI 集成

### 3.1 基线对比

```bash
# 保存基线
cargo bench --save-baseline before

# 修改代码后再次运行
cargo bench --save-baseline after

# 比较两次结果
cargo install critcmp
critcmp before after
```

### 3.2 自动化阈值检测

```rust
const THRESHOLD: f64 = 1.05; // 允许 5% 波动

fn check_regression(baseline: f64, current: f64) -> bool {
    current / baseline > THRESHOLD
}
```

### 3.3 CI 最佳实践

- 在隔离且稳定的运行器上执行 `cargo bench`。
- 固定 CPU 频率、禁用 Turbo Boost、隔离其他负载。
- 将 `target/criterion` 报告作为 artifact 保存。
- 对关键基准设置 ≥5% 的回归门槛，失败时阻断合并。

## 四、高级测量

### 4.1 自定义测量时间

```rust
use criterion::{Criterion, measurement::WallTime};
use std::time::Duration;

fn custom_measurement(c: &mut Criterion<WallTime>) {
    let mut group = c.benchmark_group("custom");
    group.measurement_time(Duration::from_secs(10));
    group.sample_size(1000);
    group.warm_up_time(Duration::from_secs(3));
    group.bench_function("my_function", |b| b.iter(|| {}));
    group.finish();
}
```

### 4.2 吞吐量测量

```rust
use criterion::{Criterion, Throughput, BenchmarkId};

fn throughput_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("throughput");
    for size in [1024, 10240, 102400].iter() {
        group.throughput(Throughput::Bytes(*size as u64));
        let data = vec![0u8; *size];
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            b.iter(|| data.iter().filter(|&&x| x > 128).count())
        });
    }
    group.finish();
}
```

## 五、基准测试检查清单

- [ ] 使用 `black_box` 防止编译器优化干扰测量。
- [ ] 覆盖多个输入规模，避免单点结论。
- [ ] 固定运行环境（CPU、内存、负载隔离）。
- [ ] 多次运行并记录系统信息。
- [ ] 与上一次基线对比，识别统计显著性回归。
- [ ] 对关键路径设置 CI 阈值并自动告警。

## 六、来源

- [Criterion.rs Book](https://bheisler.github.io/criterion.rs/book/)
- [Rust Performance Book](https://nnethercote.github.io/perf-book/)
