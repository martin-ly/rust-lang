# Rust 1.95.0 稳定特性

> **EN**: Rust 1.95.0 Stabilized Features
> **Summary**: Rust 1.95.0（2026-04-16 stable）引入的关键语言与库特性：`cfg_select!` 宏（Macro）、`if let` guards、路径段关键字重命名导入、`core::range` 模块（Module）、原子 `update` / `try_update`、集合可变引用（Mutable Reference）插入、`as_ref_unchecked` / `as_mut_unchecked`、`Layout` 新 API、`cold_path` 提示、布尔 `TryFrom<{integer}>`、`MaybeUninit` 与 `Cell` 数组互转，以及 PowerPC/PowerPC64 内联汇编（Inline Assembly）稳定化。
>
> **受众**: [进阶] / [专家]
> **Bloom 层级**: L2-L3
> **内容分级**: [参考级]
> **权威来源**: 本文件为 `concept/` 权威页。
> **Rust 版本**: **1.95.0 stable**
> **最后更新**: 2026-07-01
> **状态**: ✅ 已对齐 Rust 1.95.0 stable
>
> **权威来源**: · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
>
> - Announcing Rust 1.95.0
> - [releases.rs — 1.95.0](https://releases.rs/docs/1.95.0/)

---

> **前置概念**:
>
> [Rust 版本跟踪](05_rust_version_tracking.md) ·
> [Control Flow](../../01_foundation/04_control_flow/07_control_flow.md) ·
> [Atomic](../../03_advanced/00_concurrency/11_atomics_and_memory_ordering.md) ·
> [Unsafe](../../03_advanced/02_unsafe/03_unsafe.md)
>
> **后置概念**:
>
> [Rust 1.96 稳定特性](rust_1_96_stabilized.md) ·
> [Rust 1.97.0 前沿特性预览（Beta）](rust_1_97_preview.md) ·
> [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md) ·
> [Security Practices](../../06_ecosystem/07_security_and_cryptography/19_security_practices.md)
>

---

## 1. 语言层

### 1.1 `cfg_select!` 宏

稳定版本：**1.95.0**

编译期 `cfg` 条件选择，替代 `cfg-if` crate，可在函数级或表达式级使用。

```rust
cfg_select! {
    unix => {
        fn os_specific() -> &'static str { "Unix" }
    }
    windows => {
        fn os_specific() -> &'static str { "Windows" }
    }
    _ => {
        fn os_specific() -> &'static str { "Other" }
    }
}

let arch_str = cfg_select! {
    target_arch = "x86_64" => "x86_64",
    target_arch = "aarch64" => "ARM64",
    _ => "unknown",
};
```

### 1.2 `if let` guards on match arms

稳定版本：**1.95.0**

在 `match` arm 守卫中使用 `if let`，对模式进行进一步细化。**guard 不计入穷尽性检查**。

```rust
match value {
    Some(x) if let Ok(y) = parse(x) => println!("{}, {}", x, y),
    Some(_) => println!("parse failed"),
    None => println!("no value"),
}
```

### 1.3 路径段关键字重命名导入

稳定版本：**1.95.0**

```rust
use std::keyword as kw;  // 重命名关键字路径段
```

### 1.4 PowerPC/PowerPC64 内联汇编稳定化

稳定版本：**1.95.0**

```rust
#[cfg(any(target_arch = "powerpc", target_arch = "powerpc64"))]
unsafe {
    asm!("nop", options(nomem, nostack));
}
```

---

## 2. 标准库层

### 2.1 `core::range` 模块

稳定版本：**1.95.0**

`core::range` 提供与 `std::ops` 对应的范围类型，但可在 `no_std` 环境中使用。

| 新类型 | 说明 |
|---|---|
| `core::range::RangeInclusive` | 包含性范围类型 |
| `core::range::RangeInclusiveIter` | 专属迭代器（Iterator）类型 |

```rust
use core::range::RangeInclusive;

let range = RangeInclusive::new(1, 5);
for i in range {
    print!("{} ", i); // 1 2 3 4 5
}
```

### 2.2 原子操作 — `update` / `try_update`

稳定版本：**1.95.0**

封装 CAS 循环的原子更新，支持 `AtomicBool`、整数类型、`AtomicPtr<T>`。

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

let counter = AtomicUsize::new(5);

// try_update: 尝试更新一次，返回 Result
let result = counter.try_update(Ordering::Relaxed, Ordering::Relaxed, |current| {
    if current < 10 { Some(current + 1) } else { None }
});

// update: 重试直到成功（spin loop）
counter.update(Ordering::Relaxed, Ordering::Relaxed, |current| current + 1);
```

### 2.3 集合 — 获取可变引用的插入操作

稳定版本：**1.95.0**

`Vec::push_mut` / `insert_mut`、`VecDeque::push_front_mut` / `push_back_mut` / `insert_mut`、`LinkedList::push_front_mut` / `push_back_mut` 返回新插入元素的可变引用（Mutable Reference）。

```rust
use std::collections::{VecDeque, LinkedList};

let mut v = vec![1, 2];
let elem: &mut i32 = v.push_mut(3);
*elem += 10;
assert_eq!(v, [1, 2, 13]);

let mut dq = VecDeque::new();
let front = dq.push_front_mut(1);
*front *= 2;
```

### 2.4 裸指针 — 不安全转引用

稳定版本：**1.95.0**

`ptr::as_ref_unchecked` / `ptr::as_mut_unchecked` 提供无需 `unsafe` 块调用的转换（函数本身仍标记为 `unsafe`）。

```rust
let ptr: *const i32 = &42;
let r: &i32 = unsafe { ptr.as_ref_unchecked() };

let mut_ptr: *mut String = &mut String::from("hi");
let m: &mut String = unsafe { mut_ptr.as_mut_unchecked() };
```

### 2.5 布局计算 — `Layout` 新 API

稳定版本：**1.95.0**

```rust
use std::alloc::Layout;

let layout = Layout::new::<i32>();
let dangling: *mut u8 = layout.dangling_ptr();
let repeated = layout.repeat(10).unwrap().0;
let packed = layout.repeat_packed(10);
let extended = layout.extend_packed(Layout::new::<u8>()).unwrap().0;
```

### 2.6 提示 — `cold_path`

稳定版本：**1.95.0**

分支预测标注，提示编译器某分支为冷路径。

```rust
use std::hint::cold_path;

fn handle_error(e: Option<&str>) {
    if let Some(msg) = e {
        cold_path();
        eprintln!("error: {}", msg);
    }
}
```

### 2.7 布尔转换 — `TryFrom<{integer}>`

稳定版本：**1.95.0**

```rust
let b: bool = bool::try_from(1u8).unwrap(); // true
let b0: bool = bool::try_from(0u8).unwrap(); // false
let err = bool::try_from(2u8); // Err(()) — 仅 0 和 1 有效
```

### 2.8 `MaybeUninit` 数组互转

稳定版本：**1.95.0**

```rust
use std::mem::MaybeUninit;

let arr: [MaybeUninit<i32>; 3] = [MaybeUninit::new(1), MaybeUninit::new(2), MaybeUninit::new(3)];
let uninit_arr: MaybeUninit<[i32; 3]> = MaybeUninit::from(arr);
let back: [MaybeUninit<i32>; 3] = uninit_arr.into();
```

### 2.9 `Cell` 数组引用

稳定版本：**1.95.0**

```rust
use std::cell::Cell;

let cell_arr: Cell<[i32; 3]> = Cell::new([1, 2, 3]);
let ref_arr: &[Cell<i32>; 3] = cell_arr.as_ref();
let ref_slice: &[Cell<i32>] = cell_arr.as_ref();
```

---

## 3. 编译器与平台

### 3.1 `--remap-path-scope` 稳定化

稳定版本：**1.95.0**

控制二进制中路径重映射的范围：

```bash
rustc --remap-path-scope=macro,sysroot -Z remap-path-prefix=/home/user=/project
```

### 3.2 平台支持提升

| 目标 | 新级别 |
|------|--------|
| `powerpc64-unknown-linux-musl` | Tier 2 with host tools |
| `aarch64-apple-tvos` | Tier 2 |
| `aarch64-apple-tvos-sim` | Tier 2 |
| `aarch64-apple-watchos` | Tier 2 |
| `aarch64-apple-watchos-sim` | Tier 2 |
| `aarch64-apple-visionos` | Tier 2 |
| `aarch64-apple-visionos-sim` | Tier 2 |

### 3.3 重要兼容性变更

- **JSON target specs destabilized**：stable 通道不再支持自定义 target JSON，需 nightly `-Z unstable-options`。
- **`#[non_exhaustive]` enum matching**：现在读取 discriminant，可能影响闭包（Closures）捕获分析。
- **`Eq::assert_receiver_is_total_eq`**：已废弃，手动实现会触发未来兼容性警告。

---

## 4. Const 上下文新稳定 API

稳定版本：**1.95.0**

| API | 模块（Module） |
|-----|------|
| `fmt::from_fn` | `std::fmt` |
| `ControlFlow::is_break` | `core::ops::ControlFlow` |
| `ControlFlow::is_continue` | `core::ops::ControlFlow` |

```rust
const fn check_control(cf: ControlFlow<i32, ()>) -> bool {
    cf.is_break()
}
```

---

## 5. 与 Rust 2024 Edition 的关联

Rust 1.95.0 发布时，Rust 2024 Edition 已稳定 3 个月（自 1.85.0）。1.95.0 中的 `if let` guards 是对 2024 Edition `let chains` 的自然延伸：

| 特性 | 稳定版本 | 适用场景 |
|------|----------|----------|
| `let chains` | 1.88.0 (2024 Edition) | `if` / `while` 条件 |
| `if let` guards | 1.95.0 | `match` arm 守卫 |
| `cfg_select!` | 1.95.0 | 编译期条件选择 |

---

## 6. 练习与验证

- 速查：`docs/02_reference/quick_reference/02_rust_195_features_cheatsheet.md`
- 工具链镜头：`docs/06_toolchain/06_14_rust_1_95_nightly_preview.md`

---

> **权威来源**: Rust 1.95.0 Release Notes, [releases.rs 1.95.0](https://releases.rs/docs/1.95.0/)

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/futures — 生态权威 API 文档](https://docs.rs/futures) · [docs.rs/hyper — 生态权威 API 文档](https://docs.rs/hyper)
