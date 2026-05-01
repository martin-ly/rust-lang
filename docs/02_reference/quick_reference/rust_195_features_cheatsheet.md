# Rust 1.95.0 特性与 API 速查表

> **稳定版本**: Rust 1.95.0 (2026-04-16)
> **权威来源**: [Rust Blog](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | [releases.rs](https://releases.rs/docs/1.95.0/)

---

## 一、语言特性

### 1. `cfg_select!` 宏

编译期 `cfg` 条件选择，替代 `cfg-if` crate。

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

### 2. `if let` guards on match arms

在 `match` arm 守卫中使用 `if let`：

```rust
match value {
    Some(x) if let Ok(y) = parse(x) => println!("{}, {}", x, y),
    Some(_) => println!("parse failed"),
    None => println!("no value"),
}
```

### 3. 路径段关键字重命名导入

```rust
use std::keyword as kw;  // 重命名关键字路径段
```

### 4. PowerPC/PowerPC64 内联汇编稳定化

```rust
#[cfg(any(target_arch = "powerpc", target_arch = "powerpc64"))]
unsafe {
    asm!("nop", options(nomem, nostack));
}
```

---

## 二、标准库新 API

### `core::range` 模块

| API | 示例 | 说明 |
|-----|------|------|
| `core::range::RangeInclusive` | `use core::range::RangeInclusive; let r = RangeInclusive::new(1, 10);` | 新的包含性范围类型（与 `std::ops::RangeInclusive` 等价但位于 `core::range`） |
| `core::range::RangeInclusiveIter` | `let iter = r.into_iter();` | 专属迭代器类型 |

```rust
use core::range::RangeInclusive;

let range = RangeInclusive::new(1, 5);
for i in range {
    print!("{} ", i); // 1 2 3 4 5
}
```

### 原子操作 — `update` / `try_update`

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

### 集合 — 获取可变引用的插入操作

```rust
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

### 裸指针 — 不安全转引用

```rust
let ptr: *const i32 = &42;

// as_ref_unchecked: 无需 unsafe 块调用（但函数本身标记为 unsafe）
let r: &i32 = unsafe { ptr.as_ref_unchecked() };

let mut_ptr: *mut String = &mut String::from("hi");
let m: &mut String = unsafe { mut_ptr.as_mut_unchecked() };
```

### 布局计算 — `Layout` 新 API

```rust
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

### 提示 — `cold_path`

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

### 布尔转换 — `TryFrom<{integer}>`

```rust
let b: bool = bool::try_from(1u8).unwrap(); // true
let b0: bool = bool::try_from(0u8).unwrap(); // false
let err = bool::try_from(2u8); // Err(()) — 仅 0 和 1 有效
```

### `MaybeUninit` 数组互转

```rust
use std::mem::MaybeUninit;

let arr: [MaybeUninit<i32>; 3] = [MaybeUninit::new(1), MaybeUninit::new(2), MaybeUninit::new(3)];
let uninit_arr: MaybeUninit<[i32; 3]> = MaybeUninit::from(arr);

// 反向转换
let back: [MaybeUninit<i32>; 3] = uninit_arr.into();
```

### `Cell` 数组引用

```rust
use std::cell::Cell;

let cell_arr: Cell<[i32; 3]> = Cell::new([1, 2, 3]);
let ref_arr: &[Cell<i32>; 3] = cell_arr.as_ref();
let ref_slice: &[Cell<i32>] = cell_arr.as_ref();
```

---

## 三、编译器与平台

### `--remap-path-scope` 稳定化

控制二进制中路径重映射的范围：

```bash
rustc --remap-path-scope=macro,sysroot -Z remap-path-prefix=/home/user=/project
```

### 平台支持提升

| 目标 | 新级别 |
|------|--------|
| `powerpc64-unknown-linux-musl` | Tier 2 with host tools |
| `aarch64-apple-tvos` | Tier 2 |
| `aarch64-apple-tvos-sim` | Tier 2 |
| `aarch64-apple-watchos` | Tier 2 |
| `aarch64-apple-watchos-sim` | Tier 2 |
| `aarch64-apple-visionos` | Tier 2 |
| `aarch64-apple-visionos-sim` | Tier 2 |

### 重要兼容性变更

- **JSON target specs destabilized**: stable 通道不再支持自定义 target JSON，需 nightly `-Z unstable-options`
- **`#[non_exhaustive]` enum matching**: 现在读取 discriminant，可能影响闭包捕获分析
- **`Eq::assert_receiver_is_total_eq`**: 已废弃，手动实现会触发未来兼容性警告

---

## 四、Const 上下文新稳定 API

以下 API 在 const 上下文中稳定化：

| API | 模块 |
|-----|------|
| `fmt::from_fn` | `std::fmt` |
| `ControlFlow::is_break` | `core::ops::ControlFlow` |
| `ControlFlow::is_continue` | `core::ops::ControlFlow` |

```rust
const fn check_control(cf: ControlFlow<i32, ()>) -> bool {
    cf.is_break() // 1.95.0+ 可在 const fn 中使用
}
```

---

## 五、与 Rust 2024 Edition 的关联

Rust 1.95.0 发布时，Rust 2024 Edition 已稳定 3 个月（自 1.85.0）。1.95.0 中的 `if let` guards 是对 2024 Edition `let chains` 的自然延伸：

| 特性 | 稳定版本 | 适用场景 |
|------|----------|----------|
| `let chains` | 1.88.0 (2024 Edition) | `if` / `while` 条件 |
| `if let` guards | 1.95.0 | `match` arm 守卫 |
| `cfg_select!` | 1.95.0 | 编译期条件选择 |

建议 **Rust 2024 Edition** 用户优先采用上述特性以获得最佳 ergonomics。

---

> **提示**: 本速查表仅列出 Rust 1.95.0 的**新增**特性与 API。完整的标准库文档请查阅 [doc.rust-lang.org](https://doc.rust-lang.org/std/)。
