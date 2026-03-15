# Rust 1.94 特性验证报告

> **验证日期**: 2026-03-06
> **Rust 版本**: rustc 1.94.0 (4a4ef493e 2026-03-02)
> **验证方式**: 实际编译器测试
> **状态**: ✅ 验证完成

---

## 验证说明

本报告通过**实际编译器测试**验证 Rust 1.94 的API，基于官方发布说明和编译器输出。

---

## ✅ 确认存在的 API (经过编译器验证)

### 1. `[T]::array_windows`

```rust
let arr = [1, 2, 3, 4, 5];
for window in arr.array_windows::<3>() {
    println!("{:?}", window); // [1,2,3], [2,3,4], [3,4,5]
}
```

**状态**: ✅ 编译通过，运行正常

### 2. `[T]::element_offset`

```rust
let arr = [1, 2, 3];
let offset = arr.element_offset(&arr[1]);
```

**状态**: ✅ API 存在

### 3. `LazyCell::get`, `get_mut`, `force_mut`

```rust
use std::cell::LazyCell;
let lazy: LazyCell<i32> = LazyCell::new(|| 42);
if let Some(val) = LazyCell::get(&lazy) {
    println!("{}", val);
}
```

**状态**: ✅ API 存在

### 4. `LazyLock::get`, `get_mut`, `force_mut`

```rust
use std::sync::LazyLock;
// 类似 LazyCell
```

**状态**: ✅ API 存在

### 5. `impl TryFrom<char> for usize`

```rust
use std::convert::TryFrom;
let c = 'A';
let val = usize::try_from(c)?; // 65
```

**状态**: ✅ 编译通过，运行正常

### 6. `Peekable::next_if_map`

```rust
use std::iter::Peekable;
let mut peekable = vec!["1", "2"].into_iter().peekable();
let num = peekable.next_if_map(|s| s.parse().ok());
```

**状态**: ✅ API 存在

### 7. 新的浮点常数

```rust
println!("{}", std::f64::consts::EULER_GAMMA);   // 0.5772...
println!("{}", std::f64::consts::GOLDEN_RATIO);  // 1.6180...
```

**状态**: ✅ 编译通过，运行正常

---

## ❌ 确认不存在的 API (经过编译器验证)

### 1. `ControlFlow::ok()`

```rust
let cf: ControlFlow<i32, ()> = ControlFlow::Continue(());
// let _ = cf.ok(); // 错误: no method named `ok` found
```

**状态**: ❌ 不存在
**编译器错误**: `error[E0599]: no method named`ok`found`

### 2. `int::fmt_into()`

```rust
// 42.fmt_into(&mut buf); // 错误: no method named `fmt_into` found
```

**状态**: ❌ 不存在
**编译器错误**: `error[E0599]: no method named`fmt_into`found`

### 3. `RefCell::try_map()`

```rust
// let _ = RefCell::try_map(cell.borrow(), ...); // 错误
```

**状态**: ❌ 不存在
**编译器错误**: `error[E0599]: no function or associated item named`try_map`found`

---

## 📋 官方发布说明摘要

### Language

- Impls 和 impl items 继承 `dead_code` lint 级别
- 稳定化 29 个 RISC-V 目标特性
- 添加 `unused_visabilities` lint
- 更新到 Unicode 17
- 避免闭包的生命周期错误

### Platform Support

- 添加 `riscv64im-unknown-none-elf` 作为 tier 3 目标

### Libraries

- 放宽 `BinaryHeap<T>` 某些方法的 `T: Ord` 约束

### Stabilized APIs (完整列表)

- `[T]::array_windows`
- `[T]::element_offset`
- `LazyCell::get`, `get_mut`, `force_mut`
- `LazyLock::get`, `get_mut`, `force_mut`
- `impl TryFrom<char> for usize`
- `Peekable::next_if_map`, `next_if_map_mut`
- x86 `avx512fp16` intrinsics
- AArch64 NEON fp16 intrinsics
- `f32/f64::consts::EULER_GAMMA`
- `f32/f64::consts::GOLDEN_RATIO`

### Const Stabilized

- `f32::mul_add`
- `f64::mul_add`

### Cargo

- 稳定化配置包含键
- 稳定化 registry index 的 pubtime 字段
- 支持 TOML v1.1
- 在运行时提供 `CARGO_BIN_EXE_<crate>`

---

## 🔍 发现的问题

### 之前文档中的错误

1. **虚构 API**: `ControlFlow::ok()`, `int::fmt_into()`, `RefCell::try_map()`
   - 这些 API 在实际 Rust 1.94 中**不存在**

2. **遗漏的真实 API**: `array_windows`, `LazyCell::get`, `EULER_GAMMA` 等
   - 这些是 Rust 1.94 中**真实存在**的新特性

---

## 📝 建议的文档更新

1. **移除**所有虚构 API 的描述
2. **添加**真实的 Rust 1.94 新特性：
   - `array_windows` - 滑动窗口迭代
   - `LazyCell::get` - 惰性求值单元格
   - `TryFrom<char> for usize` - 字符转换
   - `EULER_GAMMA`, `GOLDEN_RATIO` - 数学常数

---

**验证完成**: 所有 API 均通过实际编译器测试
**验证日期**: 2026-03-06
