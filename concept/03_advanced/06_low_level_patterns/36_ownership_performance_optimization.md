> **内容分级**: [专家级]
> **本节关键术语**: 所有权性能优化 (Ownership Performance Optimization) · Copy on Write (Cow) · 零拷贝 (Zero-Copy) · 内存布局 (Memory Layout) · 移动语义 (Move Semantics) — [完整对照表](../../00_meta/01_terminology/terminology_glossary.md)
>
# 所有权性能优化
>
> **EN**: Ownership Performance Optimization
> **Summary**: Optimize Rust performance through ownership-aware patterns: avoid clones, use Cow, optimize memory layout, zero-copy parsing, and leverage move semantics.
> **受众**: [专家]
> **Bloom 层级**: 应用 → 分析
> **A/S/P 标记**: **A+P** — Application + Procedure
> **定位**: 从所有权视角出发，系统梳理避免不必要拷贝、使用写时复制、优化内存布局、零拷贝解析与移动语义的最佳实践。
> **前置概念**: [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) · [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) · [Smart Pointers](../../02_intermediate/02_memory_management/12_smart_pointers.md)
> **后置概念**: [Performance Optimization](../../06_ecosystem/10_performance/15_performance_optimization.md) · [Zero-Copy Parsing](15_zero_copy_parsing.md)

---

> **来源**: [TRPL — References and Borrowing](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html) · [Rustonomicon — Ownership](https://doc.rust-lang.org/nomicon/ownership.html) · [Rust Performance Book](https://nnethercote.github.io/perf-book/)

## 📑 目录

- [所有权性能优化](#所有权性能优化)
  - [📑 目录](#-目录)
  - [一、避免不必要的 Clone](#一避免不必要的-clone)
  - [二、Copy on Write (Cow)](#二copy-on-write-cow)
  - [三、内存布局优化](#三内存布局优化)
  - [四、零拷贝解析](#四零拷贝解析)
  - [五、移动语义优化](#五移动语义优化)

---

## 一、避免不必要的 Clone

优先使用引用（`&str`、`&[T]`）代替拥有所有权的类型（`String`、`Vec<T>`），避免堆分配。

```rust
// ❌ 不必要的 clone
fn process(data: &String) {
    let owned = data.clone();
}

// ✅ 直接使用切片引用
fn process(data: &str) {}
```

---

## 二、Copy on Write (Cow)

`std::borrow::Cow` 在不需要修改时零成本借用，需要修改时才克隆。

```rust
use std::borrow::Cow;

fn normalize<'a>(input: &'a str) -> Cow<'a, str> {
    if input.contains("special") {
        Cow::Owned(input.replace("special", "normal"))
    } else {
        Cow::Borrowed(input)
    }
}
```

---

## 三、内存布局优化

字段按对齐要求排序，可减少结构体填充（padding）。

```rust
// ❌ 24 字节（含填充）
struct Wasteful { a: u8, b: u64, c: u8 }

// ✅ 16 字节
struct Optimized { b: u64, a: u8, c: u8 }
```

---

## 四、零拷贝解析

使用切片引用原始数据，避免 `Vec<u8>` 分配。

```rust
fn parse_header(data: &[u8]) -> Option<u32> {
    if data.len() < 4 { return None; }
    Some(u32::from_le_bytes([data[0], data[1], data[2], data[3]]))
}
```

---

## 五、移动语义优化

利用 Rust 的默认移动语义，显式转移所有权而非拷贝大型数据。

```rust
fn consume(data: Vec<u8>) -> usize {
    data.len() // data 被移入，无拷贝开销
}
```

---

> 本文档由原 `crates/c01_ownership_borrow_scope/docs/tier_04_advanced/03_ownership_performance_optimization.md` 按 AGENTS.md §6.4 迁移而来，是 `concept/` 中的权威页。
