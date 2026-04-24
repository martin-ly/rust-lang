# The Rustonomicon 内容对齐

本文件对照 [The Rustonomicon](https://doc.rust-lang.org/nomicon/) 的章节，列出本项目已覆盖和未覆盖的内容，并标注对应的 crate 位置。

## 已覆盖内容

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

### c01: 布局保证 (align, size)

- **文件**: `crates/c01_ownership_borrow_scope/src/layout_guarantees.rs`
- **覆盖**: `size_of`、`align_of`、`offset_of`、`#[repr(C)]`、`#[repr(packed)]`、ZST/DST、padding 计算

### c12: FFI 高级用法

- **文件**: `crates/c12_wasm/src/ffi_advanced.rs`
- **覆盖**: 不透明结构体、回调封装（trampoline）、RAII 封装、动态库加载概念、可变参数

### c13: 裸指针、volatile、内联汇编

- **文件**: `crates/c13_embedded/src/raw_pointers_advanced.rs`
- **覆盖**: `*const`/`*mut` 别名规则、`read_volatile`/`write_volatile`、MMIO 操作、`core::arch::asm!`、x86_64 cpuid/rdtsc

## 待补充内容

| 章节 | 说明 | 计划 |
|------|------|------|
| 3.4 Align | `#[repr(align(N))]` 深入 | 已覆盖基础 |
| 5.2 Transmute | `mem::transmute` 安全使用 | 部分覆盖 |
| 6.2 Drop Flags | 废弃内容，暂不跟踪 | - |
| 7.3 Lock-Free 数据结构 | `crossbeam` 集成 | `c05_threads/src/lockfree/` 已有 |
| 9.2 PhantomData | 生命周期/所有权标记 | 部分覆盖 |
| 10.2 Arc/Weak 实现 | 引用计数实现 | 未覆盖 |

## 参考资源

- [The Rustonomicon - 官方文档](https://doc.rust-lang.org/nomicon/)
- [Rust Atomics and Locks - Mara Bos](https://marabos.nl/atomics/)
- [Rust Reference - Type Layout](https://doc.rust-lang.org/reference/type-layout.html)
