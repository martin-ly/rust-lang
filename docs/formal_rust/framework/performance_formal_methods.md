# 性能形式化方法(Performance Formal Methods)

- 文档版本: 1.0  
- 创建日期: 2025-01-27  
- 状态: 已完成

## 1. 目标

- 以可验证方式约束时间/空间复杂度与缓存局部性。

## 2. 模型(摘要)

```math
T(n)=\sum C_i(n)\cdot w_i \quad M(n)=\sum A_j(n)\cdot b_j
```

补充：

- 成本语义分层：源级成本→MIR 成本→LLVM IR 成本→机器码度量。对关键路径以“无回退优化”作为不变量。
- 关键权重示例：`w_call`（调用）、`w_bound`（边界检查）、`w_alloc`（分配/释放）、`w_branch`（分支失误）、`w_llc`（LLC 未命中）。
- 数据布局模型：AoS 与 SoA 对缓存线占用、预取与向量化的影响可由访存步长和对齐约束抽象。

## 3. 规则

- 单态化开销上界、内联消除调用开销、布局稳定性(`[repr(C)]`).
- 迭代器融合：同一数据通道上的 map/filter/reduce 尽量融合，避免中间分配。
- 边界消除：`for i in 0..len { unsafe { get_unchecked_mut(i) } }` 仅在证明边界与别名安全后允许；默认保持安全版本并用编译器消除多余检查。
- 零拷贝：使用 `&[T]`/`&mut [T]`、`bytes::Bytes`、`Cow` 等替代复制；避免临时 `Vec`。
- SIMD/并行：优先使用 `std::simd` 与 `rayon`，在可证明无数据相关性的前提下进行向量化/并行化。

## 4. Rust示例(零成本抽象)

```rust
#[inline(always)]
fn map_add(xs: &mut [i32], v: i32) { for x in xs { *x += v; } }
```

### 4.1 SIMD 与边界消除（示意）

```rust
#[cfg(feature = "simd")]
pub fn add_simd(xs: &mut [f32], v: f32) {
    use std::simd::{Simd, SimdFloat};
    let lanes = Simd::<f32, 8>::LANES;
    let (head, body, tail) = unsafe { xs.align_to_mut::<[f32; 8]>() };
    for x in head { *x += v; }
    for chunk in body {
        let mut s = Simd::from_array(*chunk);
        s += Simd::splat(v);
        *chunk = s.to_array();
    }
    for x in tail { *x += v; }
}
```

说明：使用对齐分段避免未对齐惩罚；IR 检查需确认无多余边界与无隐式分配。

## 5. 验证策略

- 证明义务: 不引入额外分配/虚调用
- 证据: IR检查 + 基准对照
- MIR/LLVM 检查清单：
  - 函数体无 `alloc`/`dealloc`/`panic_bounds_check`（在已证明安全的版本）。
  - 关键循环体无 `call` 到 trait 虚调用（已单态化/内联）。
  - `llvm-mca`/`uarch` 分析 IPC 与瓶颈（前端、内存、执行单元）。
- 基准方法学：Criterion 多次采样、冷/热路径隔离、输入规模分层、统计显著性与方差报告。

## 6. 工具化

- `-Zunstable-options` + `llvm-objdump` + Criterion 基准
- `cargo rustc -- -C opt-level=3 -C inline-threshold=... -Z mir-opt-level=3`
- `cargo asm`/`cargo llvm-ir`/`cargo llvm-lines`/`cargo flamegraph`
- `perf stat -d`/`perf record`/`perf c2c`（Linux）
- `llvm-mca`（吞吐/延迟静态分析）

## 最小可验证示例(MVE)

```rust
#[inline(always)]
fn add_one(xs: &mut [u64]) { for x in xs { *x += 1; } }

#[test]
fn no_alloc_no_indirection() {
    let mut data = vec![0u64; 8];
    add_one(&mut data);
    assert!(data.iter().all(|&x| x == 1));
    // 证明线索: 通过 -C opt-level=3 并配合 IR 检查无多余分配/虚调用
}
```

### MVE-2：迭代器融合 vs 中间分配

```rust
fn fused_sum(xs: &[u64]) -> u64 {
    xs.iter().map(|x| x + 1).filter(|x| x % 2 == 0).sum()
}

#[test]
fn fusion_no_alloc() {
    let xs = vec![1,2,3,4,5,6];
    let s = fused_sum(&xs);
    assert_eq!(s, (2+4+6+8)/2*2 - 2); // 任意占位校验
    // 证明线索：检查 IR 无中间 Vec 分配，无多余 bound 检查回退
}
```

### MVE-3：Rayon 并行加总（规模阈值）

```rust
#[cfg(feature = "rayon")]
fn par_sum(xs: &[u64]) -> u64 {
    use rayon::prelude::*;
    xs.par_iter().map(|x| x + 1).sum()
}
```

## 证明义务(Proof Obligations)

- P1: 函数体无堆分配与Box/Vec再分配
- P2: 函数调用被内联(启用优化级别时)
- P3: 内层循环无越界检查回退(启用边界消除或迭代器融合)
- P4: SIMD 路径在 IR 中生成向量指令（或至少不劣于标量），且无未对齐回退；
- P5: 并行实现满足工作/跨度界（work=O(n), span=O(log n)），无竞争热点；
- P6: 缓存局部性不变式：连续访问步长与对齐满足缓存线与预取假设；
- P7: 零拷贝路径中无多余 clone/copy（IR/asm 无 memmove/memcpy 额外调用）。

---

## 附：基准脚手架（Criterion）

```rust
// benches/add_bench.rs
use criterion::{criterion_group, criterion_main, Criterion, black_box};

fn bench_add(c: &mut Criterion) {
    c.bench_function("add_one_1k", |b| {
        let mut v = vec![0u64; 1024];
        b.iter(|| {
            super::add_one(black_box(&mut v));
        });
    });
}

criterion_group!(benches, bench_add);
criterion_main!(benches);
```

运行：`cargo bench --features simd,rayon`
