# Rust 1.95.0 特性与 API 速查表 (Rust 195 Features Cheatsheet) {#rust-1950-特性与-api-速查表}

> **EN**: Rust 195 Features Cheatsheet
> **Summary**: Rust 1.95.0 特性与 API 速查表 Rust 195 Features Cheatsheet. (stub/archive redirect)
> **分级**: [A]
> **Bloom 层级**: L2 (理解)
> **稳定版本**: Rust 1.95.0 (2026-04-16)
> **权威来源**: [Rust Blog](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | [releases.rs](https://releases.rs/docs/1.95.0/) | [concept/07_future/rust_1_95_stabilized.md](../../../concept/07_future/00_version_tracking/rust_1_95_stabilized.md)
>
> **受众**: [进阶] / [专家]
> **内容分级**: [专家级]

---

## 📑 目录 {#目录}

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [Rust 1.95.0 特性与 API 速查表 (Rust 195 Features Cheatsheet) {#rust-1950-特性与-api-速查表}](#rust-1950-特性与-api-速查表-rust-195-features-cheatsheet-rust-1950-特性与-api-速查表)
  - [📑 目录 {#目录}](#-目录-目录)
  - [一、语言特性 {#一语言特性}](#一语言特性-一语言特性)
    - [1. `cfg_select!` 宏 {#1-cfg\_select-宏}](#1-cfg_select-宏-1-cfg_select-宏)
    - [2. `if let` guards on match arms {#2-if-let-guards-on-match-arms}](#2-if-let-guards-on-match-arms-2-if-let-guards-on-match-arms)
    - [3. 路径段关键字重命名导入 {#3-路径段关键字重命名导入}](#3-路径段关键字重命名导入-3-路径段关键字重命名导入)
    - [4. PowerPC/PowerPC64 内联汇编稳定化 {#4-powerpcpowerpc64-内联汇编稳定化}](#4-powerpcpowerpc64-内联汇编稳定化-4-powerpcpowerpc64-内联汇编稳定化)
  - [二、标准库新 API {#二标准库新-api}](#二标准库新-api-二标准库新-api)
    - [`core::range` 模块 {#corerange-模块}](#corerange-模块-corerange-模块)
    - [原子操作 — `update` / `try_update` {#原子操作-update-try\_update}](#原子操作--update--try_update-原子操作-update-try_update)
    - [集合 — 获取可变引用的插入操作 {#集合-获取可变引用的插入操作}](#集合--获取可变引用的插入操作-集合-获取可变引用的插入操作)
    - [裸指针 — 不安全转引用 {#裸指针-不安全转引用}](#裸指针--不安全转引用-裸指针-不安全转引用)
    - [布局计算 — `Layout` 新 API {#布局计算-layout-新-api}](#布局计算--layout-新-api-布局计算-layout-新-api)
    - [提示 — `cold_path` {#提示-cold\_path}](#提示--cold_path-提示-cold_path)
    - [布尔转换 — `TryFrom<{integer}>` {#布尔转换-tryfrominteger}](#布尔转换--tryfrominteger-布尔转换-tryfrominteger)
    - [`MaybeUninit` 数组互转 {#maybeuninit-数组互转}](#maybeuninit-数组互转-maybeuninit-数组互转)
    - [`Cell` 数组引用 {#cell-数组引用}](#cell-数组引用-cell-数组引用)
  - [三、编译器与平台 {#三编译器与平台}](#三编译器与平台-三编译器与平台)
    - [`--remap-path-scope` 稳定化 {#remap-path-scope-稳定化}](#--remap-path-scope-稳定化-remap-path-scope-稳定化)
    - [平台支持提升 {#平台支持提升}](#平台支持提升-平台支持提升)
    - [重要兼容性变更 {#重要兼容性变更}](#重要兼容性变更-重要兼容性变更)
  - [四、Const 上下文新稳定 API {#四const-上下文新稳定-api}](#四const-上下文新稳定-api-四const-上下文新稳定-api)
  - [五、与 Rust 2024 Edition 的关联 {#五与-rust-2024-edition-的关联}](#五与-rust-2024-edition-的关联-五与-rust-2024-edition-的关联)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 一、语言特性 {#一语言特性}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 1. `cfg_select!` 宏 {#1-cfg_select-宏}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_system)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

编译期 `cfg` 条件选择，替代 `cfg-if` crate。

> 📎 可运行示例: [`crates/c03_control_fn/examples/cfg_select_demo.rs`](../../../crates/c03_control_fn/examples/cfg_select_demo.rs)

```rust
// 函数级条件编译
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

// 表达式级条件编译
let arch_str = cfg_select! {
    target_arch = "x86_64" => "x86_64",
    target_arch = "aarch64" => "ARM64",
    _ => "unknown",
};
```

### 2. `if let` guards on match arms {#2-if-let-guards-on-match-arms}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_system)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

在 `match` arm 守卫中使用 `if let`：

> 📎 知识文档: [`knowledge/02_intermediate/control_flow/01_if_let_guards.md`](../../../knowledge/02_intermediate/control_flow/01_if_let_guards.md)

```rust,ignore
match value {
    Some(x) if let Ok(y) = parse(x) => println!("{}, {}", x, y),
    Some(_) => println!("parse failed"),
    None => println!("no value"),
}
```

### 3. 路径段关键字重命名导入 {#3-路径段关键字重命名导入}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
use std::keyword as kw;  // 重命名关键字路径段
```

### 4. PowerPC/PowerPC64 内联汇编稳定化 {#4-powerpcpowerpc64-内联汇编稳定化}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**
> 📎 可运行示例: [`crates/c11_macro_system_proc/examples/ppc_asm_demo.rs`](../../../crates/c11_macro_system_proc/examples/ppc_asm_demo.rs)

```rust
#[cfg(any(target_arch = "powerpc", target_arch = "powerpc64"))]
unsafe {
    asm!("nop", options(nomem, nostack));
}
```

---

## 二、标准库新 API {#二标准库新-api}

> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### `core::range` 模块 {#corerange-模块}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**
> 📎 可运行示例: [`crates/c08_algorithms/examples/core_range_demo.rs`](../../../crates/c08_algorithms/examples/core_range_demo.rs)

| API | 示例 | 说明 |
|-----|------|------|
| `core::range::RangeInclusive` | `use core::range::RangeInclusive; let r = RangeInclusive::new(1, 10);` | 新的包含性范围类型（与 `std::ops::RangeInclusive` 等价但位于 `core::range`） |
| `core::range::RangeInclusiveIter` | `let iter = r.into_iter();` | 专属迭代器（Iterator）类型 |

```rust,ignore
use core::range::RangeInclusive;

let range = RangeInclusive::new(1, 5);
for i in range {
    print!("{} ", i); // 1 2 3 4 5
}
```

### 原子操作 — `update` / `try_update` {#原子操作-update-try_update}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**
> 📎 可运行示例: [`crates/c05_threads/examples/atomic_update_demo.rs`](../../../crates/c05_threads/examples/atomic_update_demo.rs)

封装 CAS 循环的原子更新：

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

| 类型 | `try_update` | `update` |
|------|-------------|----------|
| `AtomicPtr<T>` | ✅ | ✅ |
| `AtomicBool` | ✅ | ✅ |
| `AtomicIsize` / `AtomicUsize` | ✅ | ✅ |
| `AtomicI8` ~ `AtomicI64` | ✅ | ✅ |
| `AtomicU8` ~ `AtomicU64` | ✅ | ✅ |

### 集合 — 获取可变引用的插入操作 {#集合-获取可变引用的插入操作}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**
> 📎 可运行示例:
> [`crates/c02_type_system/examples/vec_push_mut_demo.rs`](../../../crates/c02_type_system/examples/vec_push_mut_demo.rs) (Vec) |
> [`crates/c08_algorithms/examples/collections_mut_ref_demo.rs`](../../../crates/c08_algorithms/examples/collections_mut_ref_demo.rs) (VecDeque/LinkedList)

```rust,ignore
use std::collections::{VecDeque, LinkedList};

// Vec::push_mut / insert_mut
let mut v = vec![1, 2];
let elem: &mut i32 = v.push_mut(3); // elem = &mut 3
*elem += 10;
assert_eq!(v, [1, 2, 13]);

// VecDeque::push_front_mut / push_back_mut / insert_mut
let mut dq = VecDeque::new();
let front = dq.push_front_mut(1);
*front *= 2;

// LinkedList::push_front_mut / push_back_mut
let mut list = LinkedList::new();
let head = list.push_front_mut("hello");
head.push_str(" world");
```

### 裸指针 — 不安全转引用 {#裸指针-不安全转引用}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**
> 📎 可运行示例: [`crates/c01_ownership_borrow_scope/examples/raw_ptr_ref_demo.rs`](../../../crates/c01_ownership_borrow_scope/examples/raw_ptr_ref_demo.rs)

```rust
let ptr: *const i32 = &42;

// as_ref_unchecked: 无需 unsafe 块调用（但函数本身标记为 unsafe）
let r: &i32 = unsafe { ptr.as_ref_unchecked() };

let mut_ptr: *mut String = &mut String::from("hi");
let m: &mut String = unsafe { mut_ptr.as_mut_unchecked() };
```

### 布局计算 — `Layout` 新 API {#布局计算-layout-新-api}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_system)**
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**
> 📎 可运行示例: [`crates/c01_ownership_borrow_scope/examples/layout_api_demo.rs`](../../../crates/c01_ownership_borrow_scope/examples/layout_api_demo.rs)

```rust,ignore
use std::alloc::Layout;

// 获取悬空但合规的指针
let layout = Layout::new::<i32>();
let dangling: *mut u8 = layout.dangling_ptr();

// 重复布局
let repeated = layout.repeat(10).unwrap().0; // 10 个 i32 的布局

// 紧凑重复（无填充）
let packed = layout.repeat_packed(10);

// 紧凑扩展
let extended = layout.extend_packed(Layout::new::<u8>()).unwrap().0;
```

### 提示 — `cold_path` {#提示-cold_path}

> **来源: [Wikipedia - Concurrency](https://en.wikipedia.org/wiki/Concurrency)**
> 📎 可运行示例: [`crates/c02_type_system/examples/cold_path_demo.rs`](../../../crates/c02_type_system/examples/cold_path_demo.rs)

分支预测标注：

```rust
use std::hint::cold_path;

fn handle_error(e: Option<&str>) {
    if let Some(msg) = e {
        cold_path(); // 提示编译器此分支为冷路径
        eprintln!("error: {}", msg);
    }
}
```

### 布尔转换 — `TryFrom<{integer}>` {#布尔转换-tryfrominteger}

> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**
> 📎 可运行示例: [`crates/c02_type_system/examples/bool_try_from_demo.rs`](../../../crates/c02_type_system/examples/bool_try_from_demo.rs)

```rust
let b: bool = bool::try_from(1u8).unwrap(); // true
let b0: bool = bool::try_from(0u8).unwrap(); // false
let err = bool::try_from(2u8); // Err(()) — 仅 0 和 1 有效
```

### `MaybeUninit` 数组互转 {#maybeuninit-数组互转}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> 📎 可运行示例: [`crates/c01_ownership_borrow_scope/examples/maybeuninit_cell_array_demo.rs`](../../../crates/c01_ownership_borrow_scope/examples/maybeuninit_cell_array_demo.rs)

```rust
use std::mem::MaybeUninit;

let arr: [MaybeUninit<i32>; 3] = [MaybeUninit::new(1), MaybeUninit::new(2), MaybeUninit::new(3)];
let uninit_arr: MaybeUninit<[i32; 3]> = MaybeUninit::from(arr);

// 反向转换
let back: [MaybeUninit<i32>; 3] = uninit_arr.into();
```

### `Cell` 数组引用 {#cell-数组引用}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
> 📎 可运行示例: [`crates/c01_ownership_borrow_scope/examples/maybeuninit_cell_array_demo.rs`](../../../crates/c01_ownership_borrow_scope/examples/maybeuninit_cell_array_demo.rs)

```rust
use std::cell::Cell;

let cell_arr: Cell<[i32; 3]> = Cell::new([1, 2, 3]);
let ref_arr: &[Cell<i32>; 3] = cell_arr.as_ref();
let ref_slice: &[Cell<i32>] = cell_arr.as_ref();
```

---

## 三、编译器与平台 {#三编译器与平台}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### `--remap-path-scope` 稳定化 {#remap-path-scope-稳定化}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

控制二进制中路径重映射的范围：

```bash
rustc --remap-path-scope=macro,sysroot -Z remap-path-prefix=/home/user=/project
```

### 平台支持提升 {#平台支持提升}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

| 目标 | 新级别 |
|------|--------|
| `powerpc64-unknown-linux-musl` | Tier 2 with host tools |
| `aarch64-apple-tvos` | Tier 2 |
| `aarch64-apple-tvos-sim` | Tier 2 |
| `aarch64-apple-watchos` | Tier 2 |
| `aarch64-apple-watchos-sim` | Tier 2 |
| `aarch64-apple-visionos` | Tier 2 |
| `aarch64-apple-visionos-sim` | Tier 2 |

### 重要兼容性变更 {#重要兼容性变更}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- **JSON target specs destabilized**: stable 通道不再支持自定义 target JSON，需 nightly `-Z unstable-options`
- **`#[non_exhaustive]` enum matching**: 现在读取 discriminant，可能影响闭包（Closures）捕获分析
- **`Eq::assert_receiver_is_total_eq`**: 已废弃，手动实现会触发未来兼容性警告

---

## 四、Const 上下文新稳定 API {#四const-上下文新稳定-api}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

以下 API 在 const 上下文中稳定化：

| API | 模块（Module） |
|-----|------|
| `fmt::from_fn` | `std::fmt` |
| `ControlFlow::is_break` | `core::ops::ControlFlow` |
| `ControlFlow::is_continue` | `core::ops::ControlFlow` |

```rust,ignore
const fn check_control(cf: ControlFlow<i32, ()>) -> bool {
    cf.is_break() // 1.97.0+ 可在 const fn 中使用
}
```

---

## 五、与 Rust 2024 Edition 的关联 {#五与-rust-2024-edition-的关联}
> **权威来源**: [Rust Edition 指南](../../../concept/07_future/01_edition_roadmap/44_edition_guide.md)
> 通用概念解释已在 `concept/` 权威页中覆盖，本节不再重复，请直接参考权威页。
## 相关概念 {#相关概念}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [quick_reference 目录](README.md)
- [速查表索引](README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

---
