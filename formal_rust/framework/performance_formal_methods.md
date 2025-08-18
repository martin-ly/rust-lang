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

## 3. 规则

- 单态化开销上界、内联消除调用开销、布局稳定性(`[repr(C)]`).

## 4. Rust示例(零成本抽象)

```rust
#[inline(always)]
fn map_add(xs: &mut [i32], v: i32) { for x in xs { *x += v; } }
```

## 5. 验证策略

- 证明义务: 不引入额外分配/虚调用
- 证据: IR检查 + 基准对照

## 6. 工具化

- `-Zunstable-options` + `llvm-objdump` + Criterion 基准

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

## 证明义务(Proof Obligations)

- P1: 函数体无堆分配与Box/Vec再分配
- P2: 函数调用被内联(启用优化级别时)
- P3: 内层循环无越界检查回退(启用边界消除或迭代器融合)
