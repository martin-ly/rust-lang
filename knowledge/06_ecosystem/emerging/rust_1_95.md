# Rust 1.95 新特性

> **📌 简介**: Rust 1.95.0 于 2026 年 4 月 16 日发布，核心亮点包括 `if let` guards in match、`cfg_select!` 编译时条件宏、PowerPC 内联汇编稳定化，以及大量标准库 API 扩展。这是 Rust 2026 年上半年的重要里程碑版本。
>
> **发布日期**: 2026-04-16
> **版本状态**: ✅ Stable
> **权威来源**: [Rust 1.95 Release Notes](https://releases.rs/docs/1.95.0/)

---

## 🎯 版本概览

Rust 1.95 主要聚焦于：

- **语言特性**: `if let` guards 进入 match 表达式，`cfg_select!` 编译时条件选择
- **平台扩展**: PowerPC/PowerPC64 内联汇编稳定化，多个 Apple 平台晋升 Tier 2
- **API 扩展**: `MaybeUninit` 数组转换、`Atomic*::update`、原始指针安全转换、`core::hint::cold_path`
- **工具改进**: rustdoc 搜索排序优化、路径重映射控制

---

## 🚀 主要新特性

### 1. `if let` Guards in Match Arms

Rust 1.88 稳定了 let chains。1.95 将此能力带入 match 表达式，允许基于模式匹配的条件守卫：

```rust
match value {
    Some(x) if let Ok(y) = compute(x) => {
        // `x` 和 `y` 在此处均可用
        println!("{}, {}", x, y);
    }
    _ => {}
}
```

> **注意**: 编译器目前不会将 `if let` guards 中的模式纳入 match 穷尽性检查，与常规 `if` guards 行为一致。

### 2. `cfg_select!` 编译时条件选择宏

`cfg_select!` 提供类似编译期 `match` 的 `cfg` 条件选择能力，可替代流行的 `cfg-if` crate：

```rust
// 条件代码块选择
cfg_select! {
    unix => {
        fn foo() { /* Unix 特定实现 */ }
    }
    target_pointer_width = "32" => {
        fn foo() { /* 非 Unix 32 位实现 */ }
    }
    _ => {
        fn foo() { /* 回退实现 */ }
    }
}

// 表达式级使用
let os_str = cfg_select! {
    windows => "windows",
    target_os = "macos" => "macos",
    _ => "other",
};
```

### 3. PowerPC/PowerPC64 内联汇编稳定化

```rust
use std::arch::asm;

#[cfg(any(target_arch = "powerpc", target_arch = "powerpc64"))]
fn read_timebase() -> u64 {
    let mut tb: u64;
    unsafe {
        asm!(
            "mftb {0}",
            out(reg) tb,
            options(nomem, nostack, preserves_flags),
        );
    }
    tb
}
```

### 4. `core::hint::cold_path`

标记极少执行的分支路径，优化编译器的分支预测和代码布局：

```rust
use std::hint::cold_path;

fn parse_input(input: &str) -> Result<i32, ParseError> {
    if input.is_empty() {
        cold_path();
        return Err(ParseError::Empty);
    }
    input.parse().map_err(|_| {
        cold_path();
        ParseError::Invalid
    })
}
```

### 5. `MaybeUninit` 数组双向转换

```rust
use std::mem::MaybeUninit;

// [MaybeUninit<T>; N] ↔ MaybeUninit<[T; N]>
let arr: [MaybeUninit<i32>; 4] = [
    MaybeUninit::new(1),
    MaybeUninit::new(2),
    MaybeUninit::new(3),
    MaybeUninit::new(4),
];
let uninit_array: MaybeUninit<[i32; 4]> = MaybeUninit::from(arr);

// 反向转换
let arr_back: [MaybeUninit<i32>; 4] = uninit_array.into();
```

### 6. 原子类型 `update` / `try_update`

```rust
use std::sync::atomic::{AtomicU32, Ordering};

let counter = AtomicU32::new(5);

// 原子更新：读取、计算、CAS 循环封装
let prev = counter.update(Ordering::Relaxed, |x| x * 2);
assert_eq!(prev, 5);
assert_eq!(counter.load(Ordering::Relaxed), 10);

// 条件更新：仅在谓词返回 Some 时执行
counter.try_update(Ordering::Relaxed, |x| {
    if x > 8 { Some(x - 3) } else { None }
});
```

### 7. 原始指针安全转换

```rust
let ptr: *const u8 = &42u8;

// SAFETY: 指针已知有效
let ref_u8: &u8 = unsafe { ptr.as_ref_unchecked() };

let mut_ptr: *mut String = &mut String::from("hello");
let ref_mut: &mut String = unsafe { mut_ptr.as_mut_unchecked() };
```

### 8. `bool: TryFrom<{integer}>`

```rust
// 显式转换整数到 bool
let flag: bool = 1i32.try_into()?; // Ok(true)
let flag: bool = 0i32.try_into()?; // Ok(false)
let flag: bool = 2i32.try_into()?; // Err(BoolError)
```

### 9. `core::range` 模块与 `RangeInclusive` 类型

```rust
use core::range::RangeInclusive;

let r = RangeInclusive::new(1, 10);
assert_eq!(r.start(), &1);
assert_eq!(r.end(), &10);
assert!(r.contains(&5));
```

### 10. `Cell<[T]>` 与 `Cell<[T; N]>` 的数组视图

```rust
use std::cell::Cell;

let cell_array: Cell<[i32; 3]> = Cell::new([1, 2, 3]);
let cell_slice: &[Cell<i32>] = cell_array.as_ref();

cell_slice[0].set(100);
assert_eq!(cell_array.get()[0], 100);
```

---

## 📊 与 1.94 对比

| 特性 | 1.94 | 1.95 |
|------|------|------|
| match guards | `if` 条件 | `if let` 模式匹配条件 ✅ |
| 编译时条件选择 | `cfg-if` crate | `cfg_select!` 宏 ✅ |
| PowerPC 内联汇编 | 不稳定 | ✅ 稳定 |
| `MaybeUninit` 数组转换 | 手动 unsafe | ✅ 标准库提供 |
| 原子更新 | CAS 手动循环 | `update`/`try_update` ✅ |
| `bool` 从整数转换 | `value != 0` | `TryFrom` ✅ |
| `cold_path` | `#[cold]` 属性 | `core::hint::cold_path` ✅ |

---

## 🔄 迁移指南

### 从 `cfg-if` 迁移到 `cfg_select!`

```rust
// 之前 (cfg-if crate)
use cfg_if::cfg_if;
cfg_if! {
    if #[cfg(unix)] {
        fn os_specific() {}
    } else {
        fn os_specific() {}
    }
}

// 之后 (Rust 1.95 内置)
cfg_select! {
    unix => { fn os_specific() {} }
    _ => { fn os_specific() {} }
}
```

### 原子操作简化

```rust
// 之前: 手动 CAS 循环
loop {
    let current = atomic.load(Ordering::Relaxed);
    let new = current * 2;
    if atomic.compare_exchange_weak(
        current, new, Ordering::Relaxed, Ordering::Relaxed
    ).is_ok() { break; }
}

// 之后: update 方法
atomic.update(Ordering::Relaxed, |x| x * 2);
```

---

## ⚠️ 兼容性注意

1. **JSON target specs 已去稳定化**: 自定义目标规范现在需要 `-Z unstable-options`
2. **`$crate` 导入更严格**: `use $crate::{self};` 不再允许
3. **`Eq::assert_receiver_is_total_eq` 已废弃**: 手动实现会触发未来兼容性警告
4. **数组强制转换推断变化**: 可能减少类型推断约束，某些代码需要显式类型标注

---

## 🔗 参考资源

- [Rust 1.95.0 Release Notes](https://releases.rs/docs/1.95.0/)
- [Rust Blog - Announcing 1.95.0](https://blog.rust-lang.org/releases/latest/)
- [cfg_select! Tracking Issue](https://github.com/rust-lang/rust/issues/)

---

**文档版本**: 1.0
**对应 Rust 版本**: 1.95.0
**最后更新**: 2026-05-09
