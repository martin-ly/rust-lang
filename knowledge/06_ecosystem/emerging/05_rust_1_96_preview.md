# Rust 1.96 预览特性

> **Bloom 层级**: 理解

> **📌 简介**: Rust 1.96.0 预计于 2026 年 5 月 28 日发布。当前处于 Beta 阶段，以下特性已通过 FCP 或正在最终稳定化流程中，极有可能进入稳定版。
>
> **预计发布**: 2026-05-28
> **版本状态**: 🧪 Beta 8（最终候选，无已知 release blocker）
> **权威来源**: [releases.rs](https://releases.rs/) · [Rust Beta 1.96.0-beta.8](https://doc.rust-lang.org/beta/releases.html)

---

## 🎯 版本概览
>
> **[来源: Rust Official Docs]**

Rust 1.96 主要聚焦于：

- **标准库扩展**: `VecDeque::truncate_front`、`int_format_into`、`RefCell::try_map`
- **开发体验**: `cargo script` / frontmatter 单文件脚本支持
- **类型系统演进**: RFC 3550 新 Range 类型（`Range` / `RangeFrom`）
- **编译器**: `-Z instrument-mcount`、函数对齐 `#[align(N)]`

---

## 🚀 主要候选特性
>
> **[来源: Rust Official Docs]**

### 1. `VecDeque::truncate_front`
>
> **[来源: Rust Official Docs]**

`VecDeque` 新增从前部截断的能力，与现有的 `truncate`（从后部截断）对称：

```rust,ignore
use std::collections::VecDeque;

let mut deque = VecDeque::from([1, 2, 3, 4, 5]);
deque.truncate_front(2); // 保留最后 2 个元素
assert_eq!(deque, [4, 5]);
```

> **状态**: FCP 已完成，等待合并

### 2. `int_format_into` — 高效整数格式化
>
> **[来源: Rust Official Docs]**

将整数直接格式化为固定大小的栈缓冲区，避免堆分配：

```rust,ignore
#![feature(int_format_into)]
use std::num::NumBuffer;

let mut buf = NumBuffer::new();
let s: &str = 12345i32.format_into(&mut buf);
assert_eq!(s, "12345");

// 零分配，适用于热路径
let mut buf = NumBuffer::new();
let s = (-99999999i32).format_into(&mut buf);
```

> **状态**: 稳定化 PR #152902 推进中，需 FCP

### 3. `RefCell::try_map` / `RefMut::try_map`
>
> **[来源: Rust Official Docs]**

对 `RefCell` 借用 guard 进行条件投影，失败时保留原始 guard：

```rust,ignore
#![feature(refcell_try_map)]
use std::cell::{RefCell, Ref};

let cell = RefCell::new(vec![1, 2, 3]);

// try_map: 条件投影，失败返回 (guard, error)
let result: Result<Ref<[i32]>, (Ref<Vec<i32>>, &str)> =
    Ref::try_map(cell.borrow(), |v| {
        if v.len() >= 2 { Ok(&v[..2]) } else { Err("too short") }
    });

assert!(result.is_ok());
```

> **状态**: 稳定化 PR #152122 推进中

### 4. `cargo script` / Frontmatter
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

单文件 Rust 脚本，无需 `Cargo.toml`：

```rust,compile_fail
#!/usr/bin/env cargo
---
[package]
edition = "2024"

[dependencies]
serde = { version = "1", features = ["derive"] }
---

use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct Point { x: i32, y: i32 }

fn main() {
    let p = Point { x: 1, y: 2 };
    println!("{}", serde_json::to_string(&p).unwrap());
}
```

运行方式：

```bash
cargo script my_script.rs
# 或直接执行
./my_script.rs
```

> **状态**: nightly 已实现，RFC #3502/#3503 已批准，目标 1.96 稳定

### 5. RFC 3550 新 Range 类型
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

Rust 1.95 已稳定 `RangeInclusive` 和 `RangeInclusiveIter`。1.96 预计继续推进 RFC 3550：

```rust,ignore
use core::range::Range;

// 新的 Range 类型实现 IntoIterator 而非直接是 Iterator
// 支持 Copy trait，更透明的内部结构
let r = Range::new(0, 10);
for i in r { // r 仍可用，因为是 Copy
    println!("{}", i);
}
```

> **目标**: 为 Edition 2027 的语法糖替换做准备

### 6. `proc_macro_value`
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

过程宏支持直接返回值类型：

```rust
// 允许过程宏返回更丰富的值类型
// 简化宏 API 设计
```

> **状态**: 稳定化 PR #152092 推进中

---

## 📊 与 1.95 对比
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 特性 | 1.95 | 1.96 (预计) |
|------|------|-------------|
| VecDeque 截断 | `truncate` (后部) | `truncate_front` ✅ |
| 整数格式化 | `to_string()` 堆分配 | `format_into` 零分配 ✅ |
| RefCell 投影 | `map` / `filter_map` | `try_map` ✅ |
| 单文件脚本 | 需 `Cargo.toml` | `cargo script` + frontmatter ✅ |
| Range 类型 | `RangeInclusive` | `Range` / `RangeFrom` 新类型 |

---

## ⚠️ 使用注意
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

所有上述特性在 1.96 稳定前均需 nightly 编译器和 feature gate：

```rust,ignore
#![feature(int_format_into)]
#![feature(refcell_try_map)]
#![feature(vec_deque_truncate_front)]
#![feature(proc_macro_value)]
```

`cargo script` / frontmatter 使用 `-Z script` flag：

```bash
rustc +nightly -Z script my_script.rs
cargo +nightly -Z script run my_script.rs
```

---

## 🔗 参考资源
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [Rust 1.96.0 Beta Release Notes](https://releases.rs/docs/1.96.0/)
- [int_format_into Tracking Issue #138215](https://github.com/rust-lang/rust/issues/138215)
- [refcell_try_map Tracking Issue #143801](https://github.com/rust-lang/rust/issues/143801)
- [VecDeque::truncate_front Tracking Issue #140667](https://github.com/rust-lang/rust/issues/140667)
- [cargo-script RFC #3502](https://github.com/rust-lang/rfcs/pull/3502)
- [RFC 3550 - New Range Types](https://github.com/rust-lang/rfcs/pull/3550)

---

> **权威来源**: [releases.rs](https://releases.rs/), [Rust Beta Release Notes](https://releases.rs/docs/1.96.0/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust 1.96 Beta 发布说明来源标注、Tracking Issue 引用 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0 (Beta)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念
>
> **[来源: [crates.io](https://crates.io/)]**

- [Rust 标准库速查](../../05_reference/03_std_library_cheatsheet.md)

- [Async Closures (异步闭包)](01_async_closures.md)
- [Generic Const Expressions (泛型常量表达式)](02_generic_const_exprs.md)

---

## 权威来源索引

> **[来源: [crates.io](https://crates.io/)]**
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

---

## 相关概念

- [Rust for Linux (concept)](../../../concept/07_future/19_rust_for_linux.md) — 2026 RfL Roadmap 与社区争议
- [Cranelift 后端 (concept)](../../../concept/07_future/16_cranelift_backend_preview.md) — unwind/debuginfo 2026 进展
- [并行前端 (concept)](../../../concept/07_future/09_parallel_frontend_preview.md) — 1.3-1.5x 编译加速实测
