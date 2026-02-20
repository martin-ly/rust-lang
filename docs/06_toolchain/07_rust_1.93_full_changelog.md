# Rust 1.93 完整变更清单

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-15
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 目录

- [Rust 1.93 完整变更清单](#rust-193-完整变更清单)
  - [目录](#目录)
  - [语言特性](#语言特性)
    - [s390x vector 特性与 is\_s390x\_feature\_detected](#s390x-vector-特性与-is_s390x_feature_detected)
    - [C-style variadic for system ABI](#c-style-variadic-for-system-abi)
    - [cfg 谓词使用关键词报错](#cfg-谓词使用关键词报错)
    - [asm\_cfg（asm! 行上 cfg）](#asm_cfgasm-行上-cfg)
    - [const-eval 指针字节复制](#const-eval-指针字节复制)
    - [LUB coercion 修正](#lub-coercion-修正)
    - [const 含 mutable ref 到 static](#const-含-mutable-ref-到-static)
    - [const\_item\_interior\_mutations lint（warn-by-default）](#const_item_interior_mutations-lintwarn-by-default)
    - [function\_casts\_as\_integer lint（warn-by-default）](#function_casts_as_integer-lintwarn-by-default)
  - [编译器](#编译器)
    - [-C jump-tables=bool 稳定化](#-c-jump-tablesbool-稳定化)
  - [平台支持](#平台支持)
    - [riscv64a23-unknown-linux-gnu Tier 2](#riscv64a23-unknown-linux-gnu-tier-2)
    - [musl 1.2.5](#musl-125)
  - [标准库](#标准库)
    - [Copy 不再使用 specialization](#copy-不再使用-specialization)
    - [全局分配器 thread\_local 支持](#全局分配器-thread_local-支持)
    - [BTree::append 行为变更](#btreeappend-行为变更)
    - [vec::IntoIter 不再要求 T: RefUnwindSafe](#vecintoiter-不再要求-t-refunwindsafe)
    - [稳定化 API](#稳定化-api)
  - [Cargo](#cargo)
    - [CARGO\_CFG\_DEBUG\_ASSERTIONS](#cargo_cfg_debug_assertions)
    - [cargo tree --format 长格式](#cargo-tree---format-长格式)
    - [cargo clean --workspace](#cargo-clean---workspace)
  - [Rustdoc](#rustdoc)
    - [移除 #!\[doc(document\_private\_items)\]](#移除-docdocument_private_items)
    - [宏搜索过滤](#宏搜索过滤)
    - [import 搜索过滤](#import-搜索过滤)
    - [文档属性校验](#文档属性校验)
  - [相关文档](#相关文档)

---

## 语言特性

### s390x vector 特性与 is_s390x_feature_detected

**Rust 1.93** 稳定了多个 s390x `vector` 相关 target features 及 `is_s390x_feature_detected!` 宏。

**适用场景**: s390x 架构 SIMD 编程。

```rust
// 仅 s390x 架构可用
#[cfg(target_arch = "s390x")]
fn check_vector_support() {
    if std::arch::is_s390x_feature_detected!("vx") {
        // 使用向量扩展
    }
}
```

**参考**: [PR #145656](https://github.com/rust-lang/rust/pull/145656)

---

### C-style variadic for system ABI

**Rust 1.93** 稳定了 `system` ABI 的 C 风格可变参数函数声明。

```rust
extern "system" {
    fn printf(format: *const u8, ...);
}
```

**参考**: [PR #145954](https://github.com/rust-lang/rust/pull/145954)

---

### cfg 谓词使用关键词报错

**Rust 1.93** 对将某些关键词用作 `cfg` 谓词的情况发出错误。

**参考**: [PR #146978](https://github.com/rust-lang/rust/pull/146978)

---

### asm_cfg（asm! 行上 cfg）

**Rust 1.93** 稳定了 `asm_cfg`，允许在 `asm!` 的单个语句上使用 `cfg` 属性。

详见 [05_rust_1.93_vs_1.92_comparison.md](./05_rust_1.93_vs_1.92_comparison.md#3-cfg-属性在-asm-行上)

**参考**: [PR #147736](https://github.com/rust-lang/rust/pull/147736)

---

### const-eval 指针字节复制

**Rust 1.93** 在常量求值期间支持按字节复制指针。

**参考**: [PR #148259](https://github.com/rust-lang/rust/pull/148259)

---

### LUB coercion 修正

**Rust 1.93** 修正了 LUB（Least Upper Bound）coercion 对函数项类型及不同安全性函数的处理。

**参考**: [PR #148602](https://github.com/rust-lang/rust/pull/148602)

---

### const 含 mutable ref 到 static

**Rust 1.93** 允许 const 项包含对 static 的可变引用（非常 unsafe，但不总是 UB）。

**参考**: [PR #148746](https://github.com/rust-lang/rust/pull/148746)

---

### const_item_interior_mutations lint（warn-by-default）

**Rust 1.93** 新增 warn-by-default lint，对会改动内部可变 const 项的调用发出警告。

**参考**: [PR #148407](https://github.com/rust-lang/rust/pull/148407)

---

### function_casts_as_integer lint（warn-by-default）

**Rust 1.93** 新增 warn-by-default lint，对将函数强制转换为整数的操作发出警告。

**参考**: [PR #141470](https://github.com/rust-lang/rust/pull/141470)

---

## 编译器

### -C jump-tables=bool 稳定化

**Rust 1.93** 稳定了 `-C jump-tables=bool` 选项（原 `-Zno-jump-tables`）。

```bash
rustc -C jump-tables=false main.rs  # 禁用跳转表
```

**参考**: [PR #145974](https://github.com/rust-lang/rust/pull/145974)

---

## 平台支持

### riscv64a23-unknown-linux-gnu Tier 2

**Rust 1.93** 将 `riscv64a23-unknown-linux-gnu` 提升为 Tier 2（无 host tools）。

**参考**: [PR #148435](https://github.com/rust-lang/rust/pull/148435)、[平台支持页](https://doc.rust-lang.org/rustc/platform-support.html)

---

### musl 1.2.5

详见 [05_rust_1.93_vs_1.92_comparison.md](./05_rust_1.93_vs_1.92_comparison.md#1-musl-125-更新)

---

## 标准库

### Copy 不再使用 specialization

**Rust 1.93** 在 Copy trait 上停止内部使用 specialization（因在含生命周期依赖的 Copy 实现下不安全）。部分标准库 API 可能改为调用 `Clone::clone` 而非按位复制，**可能导致性能回归**。

**参考**: [PR #135634](https://github.com/rust-lang/rust/pull/135634)

---

### 全局分配器 thread_local 支持

详见 [05_rust_1.93_vs_1.92_comparison.md](./05_rust_1.93_vs_1.92_comparison.md#2-全局分配器线程本地存储支持)

---

### BTree::append 行为变更

**Rust 1.93** 修改 `BTree::append` 行为：当追加的条目已存在时，不再更新现有键。

**参考**: [PR #145628](https://github.com/rust-lang/rust/pull/145628)

---

### vec::IntoIter 不再要求 T: RefUnwindSafe

**Rust 1.93** 放宽 `vec::IntoIter<T>: UnwindSafe` 的约束，不再要求 `T: RefUnwindSafe`。

**参考**: [PR #145665](https://github.com/rust-lang/rust/pull/145665)

---

### 稳定化 API

详见 [05_rust_1.93_vs_1.92_comparison.md](./05_rust_1.93_vs_1.92_comparison.md#标准库更新)

---

## Cargo

### CARGO_CFG_DEBUG_ASSERTIONS

**Cargo 1.93** 在 build scripts 中根据 profile 启用 `CARGO_CFG_DEBUG_ASSERTIONS`。

**参考**: [PR #16160](https://github.com/rust-lang/cargo/pull/16160)

---

### cargo tree --format 长格式

**Cargo 1.93** 在 `cargo tree` 中支持 `--format` 变量的长格式。

**参考**: [PR #16204](https://github.com/rust-lang/cargo/pull/16204)

---

### cargo clean --workspace

**Cargo 1.93** 为 `cargo clean` 添加 `--workspace` 选项。

```bash
cargo clean --workspace
```

**参考**: [PR #16263](https://github.com/rust-lang/cargo/pull/16263)

---

## Rustdoc

### 移除 #![doc(document_private_items)]

**Rust 1.93** 移除了 `#![doc(document_private_items)]` 属性。

**参考**: [PR #146495](https://github.com/rust-lang/rust/pull/146495)

---

### 宏搜索过滤

**Rust 1.93** 在 "macros" 搜索过滤中包含 attribute 和 derive 宏。

**参考**: [PR #148176](https://github.com/rust-lang/rust/pull/148176)

---

### import 搜索过滤

**Rust 1.93** 在 `import` 搜索过滤中包含 extern crates。

**参考**: [PR #148301](https://github.com/rust-lang/rust/pull/148301)

---

### 文档属性校验

**Rust 1.93** 对 crate 级文档属性进行校验。若 `html_favicon_url`、`html_logo_url`、`html_playground_url`、`issue_tracker_base_url` 或 `html_no_source` 有缺失、意外值或类型错误，将发出 deny-by-default lint `rustdoc::invalid_doc_attributes`。

**参考**: [PR #149197](https://github.com/rust-lang/rust/pull/149197)

---

## 相关文档

- [Rust 1.93 vs 1.92 对比](./05_rust_1.93_vs_1.92_comparison.md)
- [Rust 1.93 兼容性注意事项](./06_rust_1.93_compatibility_notes.md)
- [Rust 1.93.0 Release Notes](https://blog.rust-lang.org/2026/01/22/Rust-1.93.0/)
- [releases.rs 1.93.0](https://releases.rs/docs/1.93.0/)

---

**最后对照 releases.rs**: 2026-02-14
