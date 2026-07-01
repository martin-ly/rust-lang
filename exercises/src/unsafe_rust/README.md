# Unsafe Rust 练习模块 / Unsafe Rust Exercise Module

> **位置**: `exercises/src/unsafe_rust/mod.rs`  
> **测试**: `exercises/tests/l3_unsafe_rust.rs`  
> **Rust 版本**: 1.96.0+ (Edition 2024)

---

## 模块概览 / Module Overview

本模块包含 7 道 hands-on 练习，帮助你逐步掌握 Rust 中 `unsafe` 代码的
编写与封装。每道练习都以**安全封装**为目标：内部可以使用 `unsafe`，
但对外暴露的 API 应当是 safe 的，并且所有不变量都要通过文档、断言或
类型系统来保证。

This module contains 7 hands-on exercises to help you progressively master
writing and wrapping `unsafe` Rust code. Each exercise aims for a **safe
abstraction**: the internals may use `unsafe`, but the exposed API should be
safe, with all invariants guaranteed via documentation, assertions, or the
type system.

| 编号 / ID | 函数 / Function | 主题 / Topic |
| :--- | :--- | :--- |
| 1 | `read_and_double` | 原始指针基础 (`*const T`, `*mut T`) |
| 2 | `increment_raw_pointer` | `unsafe fn` 与 `unsafe` 块 |
| 3 | `clone_via_raw_parts` / `zero_prefix` | `std::slice::from_raw_parts` / `from_raw_parts_mut` |
| 4 | `init_array_from_fn` | `MaybeUninit` 与未初始化内存 |
| 5 | `increment_shared_counter` | `UnsafeCell` 内部可变性 |
| 6 | `call_ffi_add_one` | FFI / `extern "C"` 调用桩（无真实 C 依赖） |
| 7 | `safe_split_at_mut` | 安全抽象封装 |

---

## 学习目标 / Learning Objectives

完成本模块后，你应该能够：

1. 正确创建、偏移和解引用 `*const T` 与 `*mut T`。
2. 区分 `unsafe fn`（调用者负责前置条件）与 `unsafe {}` 块（块内代码
   需由开发者手动保证安全）。
3. 使用 `std::slice::from_raw_parts` / `from_raw_parts_mut` 在 safe 函数
   中重建切片，并验证所有前提条件。
4. 使用 `MaybeUninit<T>` 分配未初始化内存，正确初始化，并处理 panic
   安全性（drop 守卫）。
5. 使用 `UnsafeCell<T>` 实现安全的内部可变性抽象。
6. 声明和调用 `extern "C"` 函数，理解 FFI 边界的安全封装原则。
7. 将一段 `unsafe` 代码封装成 safe API，并通过类型/断言/文档维护
   不变量。

---

## 安全不变量检查清单 / Safety Invariants Checklist

在提交或运行测试前，请对照以下清单检查你的实现：

- [ ] **指针有效性**: 所有解引用的原始指针都保证非空、对齐且指向
      有效内存。
- [ ] **生命周期**: 通过原始指针创建的引用不超出原数据的生命周期。
- [ ] **不重叠**: 使用 `from_raw_parts_mut` 构造多个可变切片时，确保
      它们不重叠。
- [ ] **长度检查**: 在调用 `from_raw_parts` / `from_raw_parts_mut` 前，
      已验证指针与长度匹配，不会越界。
- [ ] **初始化**: 对 `MaybeUninit<T>` 调用 `assume_init` 或等效转换前，
      所有元素都已被正确写入。
- [ ] **Drop 安全**: 初始化 `MaybeUninit` 的过程中若可能 panic，已初始化的
      元素会被正确 drop（使用 drop 守卫）。
- [ ] **内部可变性**: 使用 `UnsafeCell` 时，调用者需保证不存在数据竞争
      或违反别名规则的访问。
- [ ] **FFI 边界**: 所有 `unsafe` 操作限制在 FFI 边界层；对外暴露的函数
      是 safe 的，且参数类型（如 `&CStr`）本身携带必要的不变量。
- [ ] **最小 unsafe 范围**: `unsafe` 块尽可能小，只包含真正需要信任的
      操作。

---

## 运行方式 / How to Run

```bash
# 运行本模块所有集成测试
cd e:/_src/rust-lang
cargo test -p exercises --test l3_unsafe_rust

# 仅运行 unsafe_rust 相关单元测试
cargo test -p exercises unsafe_rust::

# 使用 Miri 做更深入的不变量检查（需要 nightly）
rustup run nightly cargo miri test -p exercises --test l3_unsafe_rust
```
---

## 扩展阅读 / Further Reading

- [The Rust Programming Language — Unsafe Rust](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html)
- [Rust Reference — Unsafe Operations](https://doc.rust-lang.org/reference/unsafe-op-in-unsafe-fn.html)
- [Rustonomicon](https://doc.rust-lang.org/nomicon/)
- [`std::ptr`](https://doc.rust-lang.org/std/ptr/)
- [`std::mem::MaybeUninit`](https://doc.rust-lang.org/std/mem/union.MaybeUninit.html)
- [`std::cell::UnsafeCell`](https://doc.rust-lang.org/std/cell/struct.UnsafeCell.html)
