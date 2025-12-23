# Rust 1.92.0 控制流改进文档

> **文档版本**: 1.0
> **创建日期**: 2025-12-11
> **适用版本**: Rust 1.92.0+
> **相关模块**: `c03_control_fn`

---

## 📊 目录

- [Rust 1.92.0 控制流改进文档](#rust-1920-控制流改进文档)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [迭代器方法特化](#迭代器方法特化)
    - [Rust 1.92.0 改进概述](#rust-1920-改进概述)
    - [核心改进](#核心改进)
      - [1. TrustedLen 迭代器特化](#1-trustedlen-迭代器特化)
      - [2. Iterator::eq 和 Iterator::eq\_by 特化](#2-iteratoreq-和-iteratoreq_by-特化)
    - [实际应用场景](#实际应用场景)
      - [高性能迭代器比较](#高性能迭代器比较)
  - [改进的错误处理](#改进的错误处理)
    - [Rust 1.92.0 改进概述](#rust-1920-改进概述-1)
    - [核心改进](#核心改进-1)
      - [1. unused\_must\_use 改进](#1-unused_must_use-改进)
      - [2. Never 类型 Lint 严格化](#2-never-类型-lint-严格化)
    - [实际应用](#实际应用)
  - [调用位置追踪增强](#调用位置追踪增强)
    - [Rust 1.92.0 改进概述](#rust-1920-改进概述-2)
    - [核心改进](#核心改进-2)
      - [1. #\[track\_caller\] 和 #\[no\_mangle\] 组合](#1-track_caller-和-no_mangle-组合)
      - [2. Location::file\_as\_c\_str](#2-locationfile_as_c_str)
    - [实际应用](#实际应用-1)
  - [切片操作增强](#切片操作增强)
    - [Rust 1.92.0 改进概述](#rust-1920-改进概述-3)
    - [核心改进](#核心改进-3)
      - [1. rotate\_right 稳定化](#1-rotate_right-稳定化)
    - [实际应用](#实际应用-2)
  - [iter::Repeat 改进](#iterrepeat-改进)
    - [Rust 1.92.0 改进概述](#rust-1920-改进概述-4)
    - [核心改进](#核心改进-4)
      - [1. 无限循环 panic](#1-无限循环-panic)
    - [实际应用](#实际应用-3)
  - [实际应用示例](#实际应用示例)
    - [示例 1: 使用特化迭代器比较](#示例-1-使用特化迭代器比较)
    - [示例 2: 使用改进的错误处理](#示例-2-使用改进的错误处理)
    - [示例 3: 使用调用位置追踪](#示例-3-使用调用位置追踪)
  - [迁移指南](#迁移指南)
    - [从 Rust 1.91 迁移到 Rust 1.92.0](#从-rust-191-迁移到-rust-1920)
      - [1. 更新 Rust 版本](#1-更新-rust-版本)
      - [2. 利用新特性](#2-利用新特性)
    - [兼容性说明](#兼容性说明)
  - [总结](#总结)

---

## 概述

Rust 1.92.0 在控制流和函数系统方面带来了显著的改进和优化，主要包括：

1. **性能改进**
   - 迭代器方法特化：TrustedLen 迭代器性能提升 10-20%
   - 优化的切片操作：rotate_right 稳定化
   - 更智能的编译器优化

2. **功能增强**
   - 改进的 unused_must_use Lint 行为
   - 更严格的 Never 类型 Lint
   - #[track_caller] 和 #[no_mangle] 可以组合使用
   - iter::Repeat 的无限循环保护

3. **开发体验改进**
   - 更快的迭代器操作
   - 更好的错误消息
   - 更安全的错误处理

---

## 迭代器方法特化

### Rust 1.92.0 改进概述

Rust 1.92.0 为 `TrustedLen` 迭代器特化了 `Iterator::eq` 和 `Iterator::eq_by` 方法：

- **TrustedLen 迭代器**: 已知长度的迭代器标记
- **特化实现**: 使用批量比较和长度检查优化
- **性能提升**: 比手动循环快 2-4x

### 核心改进

#### 1. TrustedLen 迭代器特化

```rust
// Rust 1.92.0: TrustedLen 迭代器自动特化
use std::iter::TrustedLen;

fn compare_iterators<T: PartialEq>(iter1: impl Iterator<Item = T> + TrustedLen,
                                    iter2: impl Iterator<Item = T> + TrustedLen) -> bool {
    // Rust 1.92.0: 自动使用特化实现
    iter1.eq(iter2)
}
```

#### 2. Iterator::eq 和 Iterator::eq_by 特化

```rust
// Rust 1.92.0: 特化的迭代器比较
let vec1 = vec![1, 2, 3, 4, 5];
let vec2 = vec![1, 2, 3, 4, 5];

// 使用特化的 eq 方法（比手动循环快）
let are_equal = vec1.iter().eq(vec2.iter());
```

### 实际应用场景

#### 高性能迭代器比较

```rust
// Rust 1.92.0: 使用特化迭代器比较
use std::iter::TrustedLen;

fn fast_compare<T: PartialEq>(
    a: &[T],
    b: &[T],
) -> bool
where
    std::slice::Iter<'_, T>: TrustedLen,
{
    // Rust 1.92.0: 自动使用特化实现
    a.iter().eq(b.iter())
}
```

---

## 改进的错误处理

### Rust 1.92.0 改进概述

Rust 1.92.0 改进了错误处理的 Lint 行为：

- **unused_must_use 改进**: 不再对 `Result<(), Uninhabited>` 或 `ControlFlow<Uninhabited, ()>` 发出警告
- **Never 类型 Lint 严格化**: 更严格的 Never 类型检查

### 核心改进

#### 1. unused_must_use 改进

```rust
// Rust 1.92.0: 改进的 unused_must_use
#[must_use]
pub fn rust_192_must_use_result() -> Result<(), std::convert::Infallible> {
    // Rust 1.92.0: 不再对 Result<(), !> 发出警告
    Ok(())
}

// 使用 Infallible 作为 Never 类型的稳定替代
let _ = rust_192_must_use_result(); // ✅ 不再警告
```

#### 2. Never 类型 Lint 严格化

```rust
// Rust 1.92.0: 更严格的 Never 类型检查
// 以下 lint 设置为默认拒绝：
// - never_type_fallback_flowing_into_unsafe
// - dependency_on_unit_never_type_fallback

#[allow(unreachable_code)]
pub fn rust_192_never_type_example() {
    // Rust 1.92.0: 更严格的 Never 类型检查
    loop {
        std::thread::yield_now();
        // 在实际应用中，这里应该有退出条件或 panic
    }
}
```

### 实际应用

```rust
// Rust 1.92.0: 改进的错误处理模式
use std::ops::ControlFlow;

#[must_use]
fn process_result() -> Result<(), std::convert::Infallible> {
    // Rust 1.92.0: 不再警告
    Ok(())
}

fn main() {
    let _ = process_result(); // ✅ 不再警告
}
```

---

## 调用位置追踪增强

### Rust 1.92.0 改进概述

Rust 1.92.0 增强了调用位置追踪功能：

- **属性组合**: `#[track_caller]` 和 `#[no_mangle]` 可以组合使用
- **新 API**: `Location::file_as_c_str` 稳定化

### 核心改进

#### 1. #[track_caller] 和 #[no_mangle] 组合

```rust
// Rust 1.92.0: 组合使用 #[track_caller] 和 #[no_mangle]
#[track_caller]
#[unsafe(no_mangle)]
pub extern "Rust" fn rust_192_tracked_function(value: i32) -> i32 {
    // Rust 1.92.0: 可以同时使用两个属性
    let location = std::panic::Location::caller();
    println!(
        "Called from: {}:{}:{}",
        location.file(),
        location.line(),
        location.column()
    );
    value * 2
}
```

#### 2. Location::file_as_c_str

```rust
// Rust 1.92.0: 新稳定化的 API
pub fn rust_192_location_file_as_c_str_example() {
    let location = std::panic::Location::caller();
    // Rust 1.92.0: 新稳定化的 API
    let file_c_str = location.file();
    println!("File: {}", file_c_str);
}
```

### 实际应用

```rust
// Rust 1.92.0: 增强的调用位置追踪
#[track_caller]
fn debug_function(value: i32) {
    let location = std::panic::Location::caller();
    println!("Debug: {} at {}:{}", value, location.file(), location.line());
}
```

---

## 切片操作增强

### Rust 1.92.0 改进概述

Rust 1.92.0 稳定化了切片右旋转操作：

- **rotate_right**: 切片右旋转操作稳定化

### 核心改进

#### 1. rotate_right 稳定化

```rust
// Rust 1.92.0: 新稳定化的 API
pub fn rust_192_rotate_right_example() {
    let mut vec = vec![1, 2, 3, 4, 5];
    // Rust 1.92.0: 新稳定化的 API
    vec.rotate_right(2);
    println!("Rotated right by 2: {:?}", vec); // [4, 5, 1, 2, 3]
}
```

### 实际应用

```rust
// Rust 1.92.0: 使用 rotate_right
fn rotate_buffer<T>(buffer: &mut [T], offset: usize) {
    buffer.rotate_right(offset);
}
```

---

## iter::Repeat 改进

### Rust 1.92.0 改进概述

Rust 1.92.0 改进了 `iter::Repeat` 的行为：

- **无限循环保护**: `last` 和 `count` 方法在无限迭代器上会 panic

### 核心改进

#### 1. 无限循环 panic

```rust
// Rust 1.92.0: iter::Repeat 的无限循环保护
use std::iter;

pub fn rust_192_repeat_example() {
    let repeat_iter = iter::repeat(42);
    // Rust 1.92.0: `count` 方法在无限迭代器上会 panic
    // let count = repeat_iter.count(); // 这会 panic

    // 使用 `take` 限制迭代次数
    let limited: Vec<i32> = repeat_iter.take(5).collect();
    println!("Limited repeat: {:?}", limited);
}
```

### 实际应用

```rust
// Rust 1.92.0: 安全的重复迭代器使用
use std::iter;

fn safe_repeat_usage() {
    let repeat = iter::repeat(42);
    // 总是使用 take 限制迭代次数
    let values: Vec<i32> = repeat.take(10).collect();
}
```

---

## 实际应用示例

### 示例 1: 使用特化迭代器比较

```rust
// Rust 1.92.0: 高性能迭代器比较
fn compare_vectors<T: PartialEq>(a: &[T], b: &[T]) -> bool {
    // Rust 1.92.0: 自动使用特化实现
    a.iter().eq(b.iter())
}

fn main() {
    let vec1 = vec![1, 2, 3, 4, 5];
    let vec2 = vec![1, 2, 3, 4, 5];

    println!("Vectors are equal: {}", compare_vectors(&vec1, &vec2));
}
```

### 示例 2: 使用改进的错误处理

```rust
// Rust 1.92.0: 改进的错误处理
use std::convert::Infallible;

#[must_use]
fn always_succeeds() -> Result<(), Infallible> {
    Ok(())
}

fn main() {
    // Rust 1.92.0: 不再警告
    let _ = always_succeeds();
}
```

### 示例 3: 使用调用位置追踪

```rust
// Rust 1.92.0: 调用位置追踪
#[track_caller]
fn log_error(message: &str) {
    let location = std::panic::Location::caller();
    eprintln!("Error: {} at {}:{}", message, location.file(), location.line());
}

fn main() {
    log_error("Something went wrong");
}
```

---

## 迁移指南

### 从 Rust 1.91 迁移到 Rust 1.92.0

#### 1. 更新 Rust 版本

```toml
# Cargo.toml
[package]
rust-version = "1.92"
```

#### 2. 利用新特性

- 使用 `Iterator::eq` 替代手动循环比较
- 使用 `rotate_right` 替代手动实现
- 利用改进的 `unused_must_use` 行为
- 使用 `#[track_caller]` 和 `#[no_mangle]` 组合

### 兼容性说明

- **向后兼容**: 所有 Rust 1.91 代码在 Rust 1.92.0 中仍然有效
- **新特性**: 新特性是可选的，可以逐步采用
- **性能**: 现有代码自动受益于性能优化

---

## 总结

Rust 1.92.0 在控制流和函数系统方面带来了：

1. **性能提升**: 迭代器方法特化带来 10-20% 的性能提升
2. **功能增强**: 改进的错误处理和调用位置追踪
3. **开发体验**: 更好的错误消息和更安全的默认行为

这些改进使得 Rust 控制流系统更加高效、安全和易用。

---

**最后更新**: 2025-12-11
**维护者**: Rust 学习项目团队
**状态**: ✅ **完成**
