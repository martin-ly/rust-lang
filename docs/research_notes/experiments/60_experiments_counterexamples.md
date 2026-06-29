# 实验与性能研究反例边界

> **内容分级**: [核心级]
> **层级**: L6 (反例边界)
> **Bloom 层级**: L5-L6 (分析/评价)
> **概念族**: 实验研究 / 性能 / 反例边界
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录

- [实验与性能研究反例边界](#实验与性能研究反例边界)
  - [目录](#目录)
  - [1. 基准测试未禁用优化](#1-基准测试未禁用优化)
  - [2. 编译器常量折叠掩盖真实性能](#2-编译器常量折叠掩盖真实性能)
  - [3. 微基准未预热缓存](#3-微基准未预热缓存)
  - [4. 错误使用 `black_box`](#4-错误使用-black_box)
  - [5. 单线程基准推断多线程性能](#5-单线程基准推断多线程性能)
  - [6. 内存分析忽略分配器差异](#6-内存分析忽略分配器差异)
  - [7. 宏展开性能测试未控制输入规模](#7-宏展开性能测试未控制输入规模)
  - [总结](#总结)

---

## 1. 基准测试未禁用优化

### 现象
```rust
#[bench]
fn bench_naive(b: &mut Bencher) {
    b.iter(|| {
        let x = 1 + 1; // ❌ 可能被完全优化掉
    });
}
```

### 后果
测得的是零耗时，无法反映真实算法性能。

### 修复方案
- 使用 `std::hint::black_box` 阻止编译器优化。
- 使用 `criterion` 并传入 `Throughput`。

---

## 2. 编译器常量折叠掩盖真实性能

### 现象
```rust
fn compute() -> i32 {
    factorial(10) // ❌ 编译期可能计算为常量
}
```

### 后果
运行时基准测试显示不现实的低延迟。

### 修复方案
- 输入参数使用 `black_box`。
- 从外部读取输入，避免编译期折叠。

---

## 3. 微基准未预热缓存

### 现象
```rust
fn bench_once(b: &mut Bencher) {
    b.iter(|| heavy_computation(&data));
}
```

### 问题
第一次迭代冷缓存、分支预测未建立，结果波动大。

### 修复方案
- Criterion 自动处理预热；自定义 benchmark 时应包含 warm-up 阶段。
- 多次运行取稳定值。

---

## 4. 错误使用 `black_box`

### 现象
```rust
b.iter(|| {
    let input = black_box(vec![1, 2, 3]); // ❌ 每次迭代重新分配
    process(input);
});
```

### 问题
`black_box` 用于阻止优化，但不应引入额外分配；否则测的是分配开销。

### 修复方案
- 将输入准备放在 `iter` 外部。
- 仅对关键值使用 `black_box`。

---

## 5. 单线程基准推断多线程性能

### 现象
```rust
// 单线程测得算法 A 比 B 快 10%
// 直接推断在多核服务器上 A 也比 B 好
```

### 问题
忽略了锁竞争、缓存一致性、伪共享（false sharing）等多线程因素。

### 修复方案
- 在目标并发度下测试。
- 使用 `criterion` 的多线程场景或自定义 tokio/rt 负载。

---

## 6. 内存分析忽略分配器差异

### 现象
```rust
// 在 glibc malloc 下测得内存占用
// 直接推断 musl/jemalloc 下相同
```

### 问题
不同分配器碎片化和释放策略不同，影响峰值内存和 long-running 占用。

### 修复方案
- 在目标部署环境分配器下测试。
- 使用 `#[global_allocator]` 固定分配器。

---

## 7. 宏展开性能测试未控制输入规模

### 现象
```rust
macro_rules! count {
    ($x:tt) => { 1 };
    ($x:tt $($rest:tt)*) => { 1 + count!($($rest)*) };
}

// 测试时 token 数量变化巨大，结果无法比较
```

### 修复方案
- 使用参数化输入规模。
- 测量编译时间时使用 `cargo build --timings` 或 `-Ztime-passes`。

---

## 总结

| 反例 | 涉及实验 | 后果 | 修复方向 |
|------|----------|------|----------|
| 未禁用优化 | 微基准 | 零耗时假象 | `black_box` / Criterion |
| 常量折叠 | 编译器优化 | 不真实延迟 | 外部输入 / `black_box` |
| 未预热缓存 | 微基准 | 结果波动 | warm-up / 多次运行 |
| 错误 `black_box` | 微基准 | 测到分配开销 | 输入外置 |
| 单线程推断多线程 | 并发基准 | 错误结论 | 目标并发度测试 |
| 忽略分配器 | 内存分析 | 部署偏差 | 固定分配器 |
| 未控制输入规模 | 宏展开 | 不可比 | 参数化 / cargo timings |

> **权威来源**: [Criterion.rs Docs](https://bheisler.github.io/criterion.rs/book/) | [Rust Performance Book](https://nnethercote.github.io/perf-book/) | [Rust Reference – black_box](https://doc.rust-lang.org/std/hint/fn.black_box.html) | [Cargo Timings](https://doc.rust-lang.org/cargo/reference/timings.html)

## 相关概念

- [性能基准测试](10_performance_benchmarks.md)
- [并发性能研究](10_concurrency_performance.md)
- [编译器优化](10_compiler_optimizations.md)
- [宏展开性能分析](10_macro_expansion_performance.md)
- [内存分析](10_memory_analysis.md)
- [知识图谱索引](../10_knowledge_graph_index.md)
