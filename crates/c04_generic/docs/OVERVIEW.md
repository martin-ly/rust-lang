# 概览：泛型与多态（c04_generic）

本模块围绕 Rust 泛型编程：类型参数、特征约束、关联类型、类型构造器、推断、GAT/HRTB 等，系统呈现静态多态的工程化方法。

---

## 目录导航

- 入门与定义（源码）
  - `src/bin/generic_define.rs`
  - `src/generic_define.rs`
  - `src/type_parameter/`
  - `src/type_constructor/`
  - `src/type_inference/`

- 特征与约束（源码）
  - `src/trait_bound/`（`copy.rs`/`clone.rs`/`eq.rs`/`order.rs` 等）
  - `src/associated_type/`

- 多态与抽象（源码）
  - `src/polymorphism/generic_trait.rs`
  - `src/polymorphism/trait_object.rs`
  - `src/natural_transformation/`

- Rust 1.89 对齐
  - `src/rust_189_features.rs`
  - `src/rust_189_gat_hrtbs.rs`
  - 报告：`PROJECT_COMPLETION_REPORT.md`、`FINAL_PROJECT_REPORT.md`、`PROJECT_SUMMARY.md`

---

### 快速开始

1) 先读 `src/bin/generic_define.rs` 与 `src/trait_bound/*`
2) 查看 `associated_type/` 与 `polymorphism/`
3) 跑通 `rust_189_gat_hrtbs.rs` 验证 GAT/HRTB 场景

---

### 待完善与交叉链接

- 增补“类型级编程”与“零成本抽象”的性能基准
- 与 `c02_type_system` 的类型理论与约束互链
- 与 `c05_threads`、`c06_async` 的跨并发场景范式对照

#### 性能基准（补全）

- 基准项：泛型 vs 特化；trait 对象 vs 泛型；inline 与 monomorphization 开销
- 方法：`criterion`、禁用 LTO/启用优化对比；生成汇编对照热点

```rust
use criterion::{criterion_group, criterion_main, Criterion, black_box};

fn generic_sum<T: Copy + Into<u64>>(v: &[T]) -> u64 { v.iter().copied().map(Into::into).sum() }

fn bench_generic(c: &mut Criterion) {
    let v: Vec<u64> = (0..1_000_0).collect();
    c.bench_function("generic_sum", |b| b.iter(|| black_box(generic_sum(&v))));
}

criterion_group!(benches, bench_generic);
criterion_main!(benches);
```

#### 互链

- 与 `c02_type_system`：约束传播、GAT/HRTB 推导与限制
- 与 `c05_threads`/`c06_async`：Send/Sync 影响与跨线程/异步边界的抽象代价
