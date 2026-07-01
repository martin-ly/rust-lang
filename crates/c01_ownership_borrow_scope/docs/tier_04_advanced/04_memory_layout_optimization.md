# Tier 4: 内存布局优化

> **文档类型**: 高级主题
> **难度**: ⭐⭐⭐⭐⭐
> **适用版本**: Rust 1.92.0+
> **对齐知识综合**: [docs/02_reference/ALIGNMENT_GUIDE.md](../../../../docs/02_reference/ALIGNMENT_GUIDE.md)

---

## 📊 目录

- [Tier 4: 内存布局优化](#tier-4-内存布局优化)
  - [📊 目录](#-目录)
  - [1. 内存对齐](#1-内存对齐)
  - [2. #\[repr(packed)\]](#2-reprpacked)
  - [3. #\[repr(align(N))\]](#3-repralignn)
  - [4. 字段重排序](#4-字段重排序)
  - [5. 零大小类型 (ZST)](#5-零大小类型-zst)
  - [6. 相关文档](#6-相关文档)

## 1. 内存对齐

**对齐**：类型实例的地址必须是 `align_of::<T>()` 的整数倍。标量类型通常「自然对齐」（对齐 = 大小）。

```rust
use std::mem;

#[repr(C)]
struct Aligned {
    a: u8,
    _padding: [u8; 7],
    b: u64,
}

assert_eq!(mem::align_of::<Aligned>(), 8);
assert_eq!(mem::size_of::<Aligned>(), 16);
```

**常用 API**：`mem::align_of::<T>()`、`mem::size_of::<T>()`、`mem::align_of_val(v)`。

---

## 2. #[repr(packed)]

无填充，字段可能未对齐，访问较慢；FFI 慎用。

```rust
#[repr(packed)]
struct Packed {
    a: u8,
    b: u64,
    c: u8,
}

// size = 10 字节 (无填充)
```

---

## 3. #[repr(align(N))]

强制 N 字节对齐，常用于缓存行（64 字节）避免伪共享。

```rust
#[repr(align(64))] // 缓存行对齐
struct CacheAligned {
    data: [u8; 64],
}
```

---

## 4. 字段重排序

`#[repr(Rust)]`（默认）允许编译器重排字段以减少填充。

```rust
// 自动优化
#[repr(Rust)] // 默认
struct Optimized {
    b: u64, // 编译器会重排
    a: u8,
    c: u8,
}
```

**建议**：大字段前置（u64 → u32 → u16 → u8）可减少填充。

---

## 5. 零大小类型 (ZST)

```rust
struct ZeroSized; // size = 0

let v = vec![ZeroSized; 1000]; // 无内存开销
```

---

## 6. 相关文档

- [Tier 4: 03\_所有权性能优化](03_ownership_performance_optimization.md)
- [09\_性能优化参考](../tier_03_references/09_performance_optimization_reference.md) - 数据对齐和填充、缓存友好设计
- [08\_内存安全参考](../tier_03_references/08_memory_safety_reference.md) - 对齐和大小、FFI
- [ALIGNMENT_GUIDE](../../../../docs/02_reference/ALIGNMENT_GUIDE.md) - 对齐知识综合指南（内存/格式化/unsafe/缓存行）
- [type_system 速查卡](../../../../docs/02_reference/quick_reference/type_system.md) - 内存对齐小节
- [c05 缓存行对齐](../../../c05_threads/docs/tier_04_advanced/02_systems_programming_optimization.md#51-缓存行对齐) - 并发场景

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
