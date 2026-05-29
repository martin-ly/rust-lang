# The Rustonomicon 内容对齐

> **Bloom 层级**: L2 (理解)

本文件对照 [The Rustonomicon](https://doc.rust-lang.org/nomicon/) 的章节，列出本项目已覆盖和未覆盖的内容，并标注对应的 crate 位置。

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [The Rustonomicon 内容对齐](#the-rustonomicon-内容对齐)
  - [📑 目录](#目录)
  - [已覆盖内容](#已覆盖内容)
  - [新增补齐内容](#新增补齐内容)
    - [c01: 布局保证 (align, size)](#c01-布局保证-align-size)
    - [c12: FFI 高级用法](#c12-ffi-高级用法)
    - [c13: 裸指针、volatile、内联汇编](#c13-裸指针volatile内联汇编)
  - [待补充内容](#待补充内容)
  - [参考资源](#参考资源)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)
  - [权威来源索引](#权威来源索引)

## 已覆盖内容
>
> **[来源: Rust Official Docs]**

| Rustonomicon 章节 | 项目位置 | 状态 |
|-------------------|----------|------|
| 1.1 Unsafe Rust | `c13_embedded/src/bare_metal_basics.rs` | ✅ |
| 1.2 Meet Safe and Unsafe | `c13_embedded/src/memory_mapped_registers.rs` | ✅ |
| 3.1 Layout | `c01_ownership_borrow_scope/src/layout_guarantees.rs` | ✅ 新增 |
| 3.2 Exotic Sizes (ZST/DST) | `c01_ownership_borrow_scope/src/layout_guarantees.rs` | ✅ 新增 |
| 3.3 ABI/Layout 控制 | `c01_ownership_borrow_scope/src/layout_guarantees.rs` | ✅ 新增 |
| 4.1 Ownership | `c01_ownership_borrow_scope/` 整体 | ✅ |
| 4.2 References | `c01_ownership_borrow_scope/src/borrow_checker/` | ✅ |
| 5.1 Type Conversions | `c02_type_system/` | ✅ |
| 6.1 Uninitialized Memory | `c13_embedded/src/no_std_practices.rs` | ✅ |
| 7.1 Atomics | `c05_threads/src/concurrency/memory_ordering.rs` | ✅ 增强 |
| 7.2 Memory Ordering | `c05_threads/src/concurrency/memory_ordering.rs` | ✅ 增强 |
| 8.1 FFI 基础 | `c13_embedded/src/ffi_c_interop.rs` | ✅ |
| 8.2 FFI 高级用法 | `c12_wasm/src/ffi_advanced.rs` | ✅ 新增 |
| 8.3 Opaque Types / 回调 | `c12_wasm/src/ffi_advanced.rs` | ✅ 新增 |
| 9.1 Drop Check | `c01_ownership_borrow_scope/src/ownership/` | ✅ |
| 10.1 Implementing Vec | `c08_algorithms/src/data_structure/` | ✅ |

## 新增补齐内容
>
> **[来源: Rust Official Docs]**

### c01: 布局保证 (align, size)
>
> **[来源: Rust Official Docs]**

- **文件**: `crates/c01_ownership_borrow_scope/src/layout_guarantees.rs`
- **覆盖**: `size_of`、`align_of`、`offset_of`、`#[repr(C)]`、`#[repr(packed)]`、ZST/DST、padding 计算

### c12: FFI 高级用法
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- **文件**: `crates/c12_wasm/src/ffi_advanced.rs`
- **覆盖**: 不透明结构体、回调封装（trampoline）、RAII 封装、动态库加载概念、可变参数

### c13: 裸指针、volatile、内联汇编
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- **文件**: `crates/c13_embedded/src/raw_pointers_advanced.rs`
- **覆盖**: `*const`/`*mut` 别名规则、`read_volatile`/`write_volatile`、MMIO 操作、`core::arch::asm!`、x86_64 cpuid/rdtsc

## 待补充内容
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 章节 | 说明 | 计划 |
|------|------|------|
| 3.4 Align | `#[repr(align(N))]` 深入 | 已覆盖基础 |
| 5.2 Transmute | `mem::transmute` 安全使用 | 部分覆盖 |
| 6.2 Drop Flags | 废弃内容，暂不跟踪 | - |
| 7.3 Lock-Free 数据结构 | `crossbeam` 集成 | `c05_threads/src/lockfree/` 已有 |
| 9.2 PhantomData | 生命周期/所有权标记 | 部分覆盖 |
| 10.2 Arc/Weak 实现 | 引用计数实现 | 未覆盖 |

## 参考资源
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [The Rustonomicon - 官方文档](https://doc.rust-lang.org/nomicon/)
- [Rust Atomics and Locks - Mara Bos](https://marabos.nl/atomics/)
- [Rust Reference - Type Layout](https://doc.rust-lang.org/reference/type-layout.html)

---

> **权威来源**: [The Rustonomicon](https://doc.rust-lang.org/nomicon/), [Rust Reference](https://doc.rust-lang.org/reference/), [Rust Atomics and Locks — Mara Bos](https://marabos.nl/atomics/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rustonomicon 官方文档来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念

- [02_reference 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**

> **[来源: Rust Reference - doc.rust-lang.org/reference]**

> **[来源: TRPL - The Rust Programming Language]**

> **[来源: Rust Standard Library - doc.rust-lang.org/std]**

> **[来源: ACM - Systems Programming Languages]**

> **[来源: IEEE - Programming Language Standards]**

> **[来源: RFCs - github.com/rust-lang/rfcs]**

> **[来源: Rustonomicon - doc.rust-lang.org/nomicon]**

---

## 权威来源索引

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
