# Rust 1.98 Nightly 前瞻速查表

> **分级**: [A]
> **Bloom 层级**: L3 (应用)

> **版本**: Rust 1.98 nightly (d1fc603d1 2026-05-26)
> **更新日期**: 2026-05-29
> **适用版本**: nightly only

> **⚠️ 重要**: 本速查表所有特性均为 nightly-only，需要 `#![feature(...)]` 显式启用。
> 预计稳定时间：部分特性可能在 Rust 1.98/1.99 中稳定，部分可能更晚。

---

## 目录

- [Rust 1.98 Nightly 前瞻速查表](#rust-198-nightly-前瞻速查表)
  - [目录](#目录)
  - [语言特性](#语言特性)
    - [`gen` 块 — 原生生成器](#gen-块--原生生成器)
    - [`for await` — 异步迭代语法糖](#for-await--异步迭代语法糖)
    - [`derive(CoercePointee)` — 智能指针自动推导](#derivecoercepointee--智能指针自动推导)
    - [`never_type` 推进稳定化](#never_type-推进稳定化)
    - [函数对齐 `#[rustc_align]`](#函数对齐-rustc_align)
    - [调试断点 `breakpoint`](#调试断点-breakpoint)
  - [核心标准库 API (进行中稳定化)](#核心标准库-api-进行中稳定化)
  - [快速参考示例](#快速参考示例)
    - [惰性斐波那契序列](#惰性斐波那契序列)
    - [异步流求和](#异步流求和)
    - [自定义智能指针](#自定义智能指针)
  - [Feature Gate 清单](#feature-gate-清单)
  - [相关链接](#相关链接)

---

## 语言特性

> **[来源: Rust Nightly Documentation](https://doc.rust-lang.org/nightly/std/ops/trait.Iterator.html)**
> **[来源: RFC 3513 — gen blocks](https://rust-lang.github.io/rfcs/3513-gen-blocks.html)**

### `gen` 块 — 原生生成器

`gen { yield ... }` 提供了一种直观的方式构造惰性迭代器，无需显式实现 `Iterator` trait 或使用 `std::iter::from_fn`。

```rust
#![feature(gen_blocks, yield_expr)]

fn fibonacci() -> impl Iterator<Item = u64> {
    gen {
        let (mut a, mut b) = (0, 1);
        loop {
            yield a;
            (a, b) = (b, a + b);
        }
    }
}

// 使用
for x in fibonacci().take(10) {
    println!("{}", x);
}
```

**关键约束**：

- `gen` 块默认按引用捕获变量；需要 `gen move` 获取所有权
- yield 时不能持有对捕获变量的借用（编译器会检查）
- 目前不支持在 `gen` 块内直接递归 yield

---

### `for await` — 异步迭代语法糖

`for await x in stream` 是 `while let Some(x) = stream.next().await` 的语法糖，
配合 `AsyncIterator` trait 使用。

```rust
#![feature(async_iterator, async_for_loop)]

use std::async_iter::AsyncIterator;
use std::pin::Pin;
use std::task::{Context, Poll};

struct CountStream { current: i32, end: i32 }

impl AsyncIterator for CountStream {
    type Item = i32;
    fn poll_next(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Option<i32>> {
        let this = self.get_mut();
        if this.current < this.end {
            let v = this.current;
            this.current += 1;
            Poll::Ready(Some(v))
        } else {
            Poll::Ready(None)
        }
    }
}

async fn sum_stream() -> i32 {
    let mut sum = 0;
    for await x in CountStream { current: 0, end: 5 } {
        sum += x;
    }
    sum // 10
}
```

---

### `derive(CoercePointee)` — 智能指针自动推导

RFC 3621 的实现。通过 `#[derive(CoercePointee)]` 自动生成 `CoerceUnsized` 实现，
使自定义智能指针支持 `T` → `dyn Trait` 的自动强制转换。

```rust
#![feature(derive_coerce_pointee)]

use std::marker::CoercePointee;
use std::ops::Deref;

#[derive(CoercePointee)]
#[repr(transparent)]
struct MyBox<'a, #[pointee] T: ?Sized>(&'a T);

impl<'a, T: ?Sized> Deref for MyBox<'a, T> {
    type Target = T;
    fn deref(&self) -> &T { self.0 }
}

// 自动支持 CoerceUnsized，无需手动实现
```

**注意**：`#[pointee]` 属性必须标注在泛型参数上（不能用在字段上）。

---

### `never_type` 推进稳定化

`!` (never type) 的稳定化 PR (#155499) 正在进行中。nightly 1.98 中：

- `Result<T, !>` 表示永不失败的操作
- 发散函数 `-> !` 的类型推导更完善
- `match` 穷尽性检查已支持 never type 分支省略

```rust
#![feature(never_type)]

fn infallible() -> Result<i32, !> {
    Ok(42)
}

fn exhaustive_match(r: Result<i32, !>) -> i32 {
    match r {
        Ok(v) => v,
        // 无需 Err 分支，编译器知晓 ! 不可实例化
    }
}
```

---

### 函数对齐 `#[rustc_align]`

控制函数在内存中的起始地址对齐，对 I-cache 优化和 SIMD 入口对齐有意义。

```rust
#![feature(fn_align)]

#[rustc_align(64)]
pub fn cache_aligned_entry() -> i32 { 42 }

#[rustc_align(16)]
pub fn simd_aligned_entry() -> i32 { 0 }
```

**注意**：当前 nightly 使用 `#[rustc_align(N)]` 而非 `#[repr(align(N))]`。

---

### 调试断点 `breakpoint`

`core::intrinsics::breakpoint()` 生成架构相关的断点指令，用于调试器 hook。

```rust
#![feature(core_intrinsics)]

pub fn debug_pause() {
    unsafe { core::intrinsics::breakpoint() };
}
```

**⚠️ 警告**：无调试器 attached 时，断点指令可能触发信号/异常导致程序终止。

---

## 核心标准库 API (进行中稳定化)

> **[来源: Rust Standard Library — Unstable Features](https://doc.rust-lang.org/nightly/std/)**
> **[来源: Rust Release Tracking](https://releases.rs/)**

以下 API 的稳定化 PR 处于 FCP/PFCP 阶段，可能在 1.98/1.99 进入 stable：

| PR | 特性 | 状态 |
|---|---|---|
| #156840 | `PathBuf::into_string` | waiting-on-review |
| #156629 | `core::range::{legacy, RangeFull, RangeTo}` | FCP |
| #156222 | `Result::map_or_default` / `Option::map_or_default` | waiting-on-review |
| #155499 | `never_type` 稳定化 | blocked |
| #154170 | `fN::BITS` | waiting-on-crater |
| #153261 | `ptr_alignment_type` as `alignment_type` | PFCP |
| #151379 | `VecDeque::retain_back` / `truncate_front` | FCP finished |
| #148605 | `supertrait_item_shadowing` | PFCP |
| #148051 | `frontmatter` | FCP finished |
| #139673 | `derive(CoercePointee)` | **FCP finished** 🔥 |

---

## 快速参考示例

> **[来源: Rust Nightly Documentation](https://doc.rust-lang.org/nightly/)**

### 惰性斐波那契序列

```rust
#![feature(gen_blocks, yield_expr)]

fn fibonacci() -> impl Iterator<Item = u64> {
    gen move {
        let (mut a, mut b) = (0, 1);
        loop {
            yield a;
            (a, b) = (b, a + b);
        }
    }
}

assert_eq!(fibonacci().take(6).collect::<Vec<_>>(),
           vec![0, 1, 1, 2, 3, 5]);
```

### 异步流求和

```rust
#![feature(async_iterator, async_for_loop)]

async fn sum_async<I: AsyncIterator<Item = i32>>(iter: I) -> i32 {
    let mut sum = 0;
    for await x in iter {
        sum += x;
    }
    sum
}
```

### 自定义智能指针

```rust
#![feature(derive_coerce_pointee)]

use std::marker::CoercePointee;
use std::ops::Deref;

#[derive(CoercePointee)]
#[repr(transparent)]
struct SmartPtr<'a, #[pointee] T: ?Sized>(&'a T);

impl<'a, T: ?Sized> Deref for SmartPtr<'a, T> {
    type Target = T;
    fn deref(&self) -> &T { self.0 }
}
```

---

## Feature Gate 清单

> **[来源: The Unstable Book](https://doc.rust-lang.org/nightly/unstable-book/index.html)**

```rust
// gen 块
#![feature(gen_blocks, yield_expr)]

// 异步迭代
#![feature(async_iterator, async_for_loop)]

// 智能指针 derive
#![feature(derive_coerce_pointee)]

// never type
#![feature(never_type)]

// 函数对齐
#![feature(fn_align)]

// 调试断点
#![feature(core_intrinsics)]
#![allow(internal_features)]
```

---

## 相关链接

- [Rust 1.97 特性速查表](./02_rust_197_features_cheatsheet.md)
- [Rust 1.96 特性速查表](./02_rust_196_features_cheatsheet.md)
- [Rust 2024 Edition 迁移指南](../../05_guides/06_rust_2024_edition_migration_guide.md)
- [releases.rs — 稳定化进度跟踪](https://releases.rs/)
- [Rust 版本跟踪](../../../concept/07_future/05_rust_version_tracking.md)
- [gen blocks 前瞻](../../../concept/07_future/15_gen_blocks_preview.md)
- [derive(CoercePointee) 前瞻](../../../concept/07_future/10_derive_coerce_pointee_preview.md)
