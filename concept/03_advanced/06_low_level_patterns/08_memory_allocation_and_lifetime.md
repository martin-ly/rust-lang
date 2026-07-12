# 内存分配与生命周期（Memory Allocation and Lifetime）

> **EN**: Memory Allocation and Lifetime
> **Summary**: Rust 内存分配模型：item、heap、stack 与 box 的生命周期（Lifetimes）关系。
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **受众**: [专家]
> **内容分级**: [专家级]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) · [Memory Model](../02_unsafe/06_memory_model.md) · [Variables](09_variables.md)
> **后置概念**: [Smart Pointers](../../02_intermediate/02_memory_management/04_smart_pointers.md) · [Custom Allocators](01_custom_allocators.md) · [The Rust Runtime](07_rust_runtime.md)
> **定理链**: Allocation → Box Lifetime → Heap Stability
> **主要来源**: [Rust Reference — Memory Allocation and Lifetime](https://doc.rust-lang.org/reference/memory-allocation-and-lifetime.html) · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL — Ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — Memory Allocation and Lifetime](https://doc.rust-lang.org/reference/memory-allocation-and-lifetime.html)

---

## 一、Item 的生命周期

程序中的 **item**（函数、模块（Module）、类型）在编译期计算其值，并在 Rust 进程的内存映像中唯一存储。(Source: [Rust Reference — Memory Allocation and Lifetime](https://doc.rust-lang.org/reference/memory-allocation-and-lifetime.html#items))

- item 不是动态分配或释放的。
- item 的生命周期（Lifetimes）与整个程序相同。

---

## 二、Heap（堆）

**堆（heap）** 是 `Box<T>` 等拥有所有权（Ownership）的指针所指向的内存区域。

### 堆分配的生命周期

- 堆分配的生命周期（Lifetimes）取决于指向它的 box 值的生命周期。(Source: [Rust Reference — Heap Allocations](https://doc.rust-lang.org/reference/memory-allocation-and-lifetime.html#heap-allocations))
- box 值可以在栈帧之间传递，也可以存储在堆上，因此堆分配可能超出创建它的栈帧。
- 堆分配保证在其整个生命周期（Lifetimes）中位于堆上的固定位置——移动 box 值本身不会导致堆内存重定位。

---

## 三、Stack（栈）

- 局部变量和临时值分配在栈帧中。
- 栈帧在函数调用时创建，在函数返回时销毁。
- 局部变量默认不可变，使用 `let mut` 声明可变。

更多细节参见 [Variables](09_variables.md)。

---

## 四、Box 与移动

```rust
let b = Box::new(42);
let c = b; // b 被 move，所有权转移到 c
```

- 移动 box 值只是复制指针，不会复制堆上的数据。(Source: [TRPL Ch4 — Ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html))
- 堆数据的所有权（Ownership）随 box 值一起转移。
- 当 box 离开作用域时，堆上的数据被释放。

---

## 五、内存布局优化补充

> 本节内容由 [`crates/c01_ownership_borrow_scope/docs/tier_04_advanced/04_memory_layout_optimization.md`](../../../crates/c01_ownership_borrow_scope/docs/tier_04_advanced/04_memory_layout_optimization.md) 迁移而来，作为 canonical 概念页的工程实践补充。

### 5.1 内存对齐与 repr 属性

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

常用 API：`mem::align_of::<T>()`、`mem::size_of::<T>()`、`mem::align_of_val(v)`。

### 5.2 `#[repr(packed)]`

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

### 5.3 `#[repr(align(N))]`

强制 N 字节对齐，常用于缓存行（64 字节）避免伪共享。

```rust
#[repr(align(64))] // 缓存行对齐
struct CacheAligned {
    data: [u8; 64],
}
```

### 5.4 字段重排序

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

### 5.5 零大小类型 (ZST)

```rust
struct ZeroSized; // size = 0

let v = vec![ZeroSized; 1000]; // 无内存开销
```

---

## 六、相关概念

| 概念 | 关系 |
|:---|:---|
| [Memory Model](../02_unsafe/06_memory_model.md) | 内存分配模型是内存模型的一部分 |
| [Variables](09_variables.md) | 局部变量在栈帧中分配 |
| [Smart Pointers](../../02_intermediate/02_memory_management/04_smart_pointers.md) | `Box`、`Rc`、`Arc` 管理堆内存 |
| [Custom Allocators](01_custom_allocators.md) | 自定义分配器改变堆分配行为 |
| [The Rust Runtime](07_rust_runtime.md) | `#[global_allocator]` 影响堆分配 |

> **权威来源**: [Rust Reference — Memory Allocation and Lifetime](https://doc.rust-lang.org/reference/memory-allocation-and-lifetime.html), [TRPL Ch4 — Ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html), [Rustonomicon — Ownership](https://doc.rust-lang.org/nomicon/ownership.html)
>
> **权威来源对齐变更日志**: 2026-07-10 Stage F L3 补全权威来源块与关键引用 [Authority Source Sprint Batch 10](../../00_meta/02_sources/05_international_authority_index.md)

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/zerocopy — 生态权威 API 文档](https://docs.rs/zerocopy) · [docs.rs/memmap2 — 生态权威 API 文档](https://docs.rs/memmap2)
