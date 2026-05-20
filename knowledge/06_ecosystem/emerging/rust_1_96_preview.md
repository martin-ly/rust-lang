# Rust 1.96 预览特性

> **Bloom 层级**: 理解

> **📌 简介**: Rust 1.96.0 预计于 2026 年 5 月 28 日发布。当前处于 Beta 阶段，以下特性已通过 FCP 或正在最终稳定化流程中，极有可能进入稳定版。
>
> **预计发布**: 2026-05-28
> **版本状态**: 🧪 Beta
> **权威来源**: [releases.rs](https://releases.rs/)

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

```rust
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

```rust
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

```rust
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

单文件 Rust 脚本，无需 `Cargo.toml`：

```rust
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

Rust 1.95 已稳定 `RangeInclusive` 和 `RangeInclusiveIter`。1.96 预计继续推进 RFC 3550：

```rust
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

过程宏支持直接返回值类型：

```rust
// 允许过程宏返回更丰富的值类型
// 简化宏 API 设计
```

> **状态**: 稳定化 PR #152092 推进中

---

## 📊 与 1.95 对比

| 特性 | 1.95 | 1.96 (预计) |
|------|------|-------------|
| VecDeque 截断 | `truncate` (后部) | `truncate_front` ✅ |
| 整数格式化 | `to_string()` 堆分配 | `format_into` 零分配 ✅ |
| RefCell 投影 | `map` / `filter_map` | `try_map` ✅ |
| 单文件脚本 | 需 `Cargo.toml` | `cargo script` + frontmatter ✅ |
| Range 类型 | `RangeInclusive` | `Range` / `RangeFrom` 新类型 |

---

## ⚠️ 使用注意

所有上述特性在 1.96 稳定前均需 nightly 编译器和 feature gate：

```rust
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
