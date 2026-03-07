# Data Layout 与内存布局

> **权威来源**: The Rust Reference (Type Layout), The Rustonomicon (Data Layout)
> **Rust 版本**: 1.94.0
> **难度**: 🔴 高级
> **前置知识**: 基础类型、结构体、Unsafe Rust

---

## 目录

- [Data Layout 与内存布局](#data-layout-与内存布局)
  - [目录](#目录)
  - [1. 内存布局基础](#1-内存布局基础)
    - [1.1 什么是 Data Layout](#11-什么是-data-layout)
    - [1.2 基本类型的布局](#12-基本类型的布局)
  - [2. 对齐 (Alignment)](#2-对齐-alignment)
    - [2.1 对齐规则](#21-对齐规则)
    - [2.2 结构体对齐](#22-结构体对齐)
    - [2.3 为什么需要对齐](#23-为什么需要对齐)
  - [3. 尺寸与布局](#3-尺寸与布局)
    - [3.1 结构体尺寸计算](#31-结构体尺寸计算)
    - [3.2 字段重排优化](#32-字段重排优化)
    - [3.3 布局工具](#33-布局工具)
  - [4. repr 属性](#4-repr-属性)
    - [4.1 `#[repr(Rust)]` (默认)](#41-reprrust-默认)
    - [4.2 `#[repr(C)]` - C 兼容布局](#42-reprc---c-兼容布局)
    - [4.3 `#[repr(packed)]` - 紧凑布局](#43-reprpacked---紧凑布局)
    - [4.4 `#[repr(align(N))]` - 自定义对齐](#44-repralignn---自定义对齐)
    - [4.5 组合使用](#45-组合使用)
  - [5. 零尺寸类型 (ZST)](#5-零尺寸类型-zst)
    - [5.1 什么是 ZST](#51-什么是-zst)
    - [5.2 ZST 的行为](#52-zst-的行为)
    - [5.3 ZST 的用途](#53-zst-的用途)
  - [6. 动态尺寸类型 (DST)](#6-动态尺寸类型-dst)
    - [6.1 什么是 DST](#61-什么是-dst)
    - [6.2 胖指针](#62-胖指针)
    - [6.3 自定义 DST](#63-自定义-dst)
  - [7. 布局优化技巧](#7-布局优化技巧)
    - [7.1 字段排序](#71-字段排序)
    - [7.2 使用枚举代替标记 + 数据](#72-使用枚举代替标记--数据)
    - [7.3 Box 大字段](#73-box-大字段)
  - [8. FFI 布局兼容性](#8-ffi-布局兼容性)
    - [8.1 C 结构体映射](#81-c-结构体映射)
    - [8.2 平台差异](#82-平台差异)
    - [8.3 布局验证](#83-布局验证)
  - [参考](#参考)

---

## 1. 内存布局基础

### 1.1 什么是 Data Layout

Data Layout 定义了类型在内存中的**表示方式**：

- 占用多少字节 (size)
- 字节如何对齐 (alignment)
- 字段如何排列 (field order)
- 填充字节如何分布 (padding)

```rust
struct Example {
    a: u8,   // 1 byte
    b: u32,  // 4 bytes
    c: u16,  // 2 bytes
}

// 实际布局可能不是简单的 1+4+2=7 bytes!
```

### 1.2 基本类型的布局

| 类型 | 大小 | 对齐 | 说明 |
|-----|------|------|------|
| `bool` | 1 | 1 | 0 = false, 1 = true |
| `u8` / `i8` | 1 | 1 | - |
| `u16` / `i16` | 2 | 2 | - |
| `u32` / `i32` | 4 | 4 | - |
| `u64` / `i64` | 8 | 8 | - |
| `f32` | 4 | 4 | IEEE 754 |
| `f64` | 8 | 8 | IEEE 754 |
| `usize` / `isize` | 4/8 | 4/8 | 取决于平台 |
| `char` | 4 | 4 | Unicode 标量值 |
| `()` | 0 | 1 | 零尺寸类型 |

```rust
use std::mem;

assert_eq!(mem::size_of::<u32>(), 4);
assert_eq!(mem::align_of::<u32>(), 4);
```

---

## 2. 对齐 (Alignment)

### 2.1 对齐规则

类型的对齐值必须是**2的幂**，表示该类型的实例必须存储在地址为该值的倍数的内存位置。

```
对齐 1: 可以存储在任何地址 (0, 1, 2, 3, ...)
对齐 2: 必须存储在偶数地址 (0, 2, 4, 6, ...)
对齐 4: 必须存储在 4 的倍数地址 (0, 4, 8, 12, ...)
对齐 8: 必须存储在 8 的倍数地址 (0, 8, 16, 24, ...)
```

### 2.2 结构体对齐

结构体的对齐等于其**最严格对齐字段**的对齐值。

```rust
struct S {
    a: u8,  // align 1
    b: u32, // align 4 (最严格)
}

// S 的对齐 = max(1, 4) = 4
assert_eq!(std::mem::align_of::<S>(), 4);
```

### 2.3 为什么需要对齐

1. **性能**: 未对齐访问可能更慢 (x86) 或导致崩溃 (ARM)
2. **原子性**: 某些原子操作要求对齐
3. **硬件限制**: 某些架构不支持未对齐访问

```rust
// 未对齐访问示例 (可能慢或崩溃)
let arr: [u8; 4] = [0, 0, 0, 0];
let ptr = arr.as_ptr().add(1) as *const u32;  // 地址 1，未对齐到 4
// unsafe { *ptr }  // 可能 UB!
```

---

## 3. 尺寸与布局

### 3.1 结构体尺寸计算

```rust
struct S1 {
    a: u8,   // offset 0, size 1
    b: u32,  // offset 4 (填充 3 bytes), size 4
    c: u16,  // offset 8, size 2
}           // 总大小 = 10，但对齐到 4 = 12

use std::mem;
assert_eq!(mem::size_of::<S1>(), 12);
```

**内存布局**:

```
Offset:  0   1   2   3   4   5   6   7   8   9   10  11
        [a] [pad] [pad] [pad] [   b   ] [   c   ] [pad]
```

### 3.2 字段重排优化

```rust
// 优化前: 12 bytes
struct Bad {
    a: u8,  // 1 + 3 pad
    b: u32, // 4
    c: u16, // 2 + 2 pad
}

// 优化后: 8 bytes
struct Good {
    b: u32, // 4
    c: u16, // 2
    a: u8,  // 1 + 1 pad
}

assert_eq!(mem::size_of::<Bad>(), 12);
assert_eq!(mem::size_of::<Good>(), 8);
```

### 3.3 布局工具

```rust
use std::mem;

struct MyStruct {
    a: u8,
    b: u32,
}

fn main() {
    println!("Size: {}", mem::size_of::<MyStruct>());
    println!("Align: {}", mem::align_of::<MyStruct>());

    // 获取字段偏移
    let s = MyStruct { a: 0, b: 0 };
    let base = &s as *const _ as usize;
    let a_offset = &s.a as *const _ as usize - base;
    let b_offset = &s.b as *const _ as usize - base;

    println!("Offset of a: {}", a_offset);  // 0
    println!("Offset of b: {}", b_offset);  // 4
}
```

---

## 4. repr 属性

### 4.1 `#[repr(Rust)]` (默认)

- 编译器可自由重排字段
- 不保证稳定性
- 优化尺寸和性能

```rust
struct DefaultLayout {
    a: u8,
    b: u32,
}
// 编译器可能重排字段
```

### 4.2 `#[repr(C)]` - C 兼容布局

- 字段按声明顺序排列
- 与 C 结构体布局兼容
- FFI 必需

```rust
#[repr(C)]
struct CLayout {
    a: u8,  // offset 0
    b: u32, // offset 4 (填充 3 bytes)
}

assert_eq!(mem::size_of::<CLayout>(), 8);
```

### 4.3 `#[repr(packed)]` - 紧凑布局

- 无填充字节
- 可能未对齐访问
- 需要 unsafe

```rust
#[repr(packed)]
struct Packed {
    a: u8,
    b: u32,  // 可能未对齐!
}

assert_eq!(mem::size_of::<Packed>(), 5);

// 访问字段需要 unsafe
let p = Packed { a: 0, b: 0 };
let b = unsafe { std::ptr::addr_of!(p.b).read_unaligned() };
```

### 4.4 `#[repr(align(N))]` - 自定义对齐

```rust
#[repr(align(64))]
struct CacheAligned {
    data: [u8; 64],
}

assert_eq!(mem::align_of::<CacheAligned>(), 64);
```

**用途**: SIMD、缓存行对齐、硬件要求

### 4.5 组合使用

```rust
#[repr(C, align(16))]
struct AlignedC {
    x: f32,
    y: f32,
}

// C 布局 + 16 字节对齐
```

---

## 5. 零尺寸类型 (ZST)

### 5.1 什么是 ZST

占用 0 字节的类型，大小为 0，对齐为 1。

```rust
// ZST 示例
struct ZeroSized;           // 单元结构体
enum Void {}                // 空枚举
struct Phantom<T>(std::marker::PhantomData<T>);
```

### 5.2 ZST 的行为

```rust
let a = ZeroSized;
let b = ZeroSized;

// a 和 b 占用相同地址!
assert_eq!(&a as *const _, &b as *const _);

// 可以创建"无限大"的数组
let arr: [ZeroSized; 1_000_000] = [ZeroSized; 1_000_000];
// 实际占用 0 字节
```

### 5.3 ZST 的用途

1. **标记类型**:

```rust
struct Kilograms(f64);  // 类型标记
struct Meters(f64);
```

1. **PhantomData**:

```rust
use std::marker::PhantomData;

struct MyVec<T> {
    ptr: *mut u8,
    marker: PhantomData<T>,  // 告诉编译器 "就像拥有 T"
}
```

1. **状态机类型**:

```rust
struct Connection<S> {
    _state: PhantomData<S>,
}

struct Connected;
struct Disconnected;
```

---

## 6. 动态尺寸类型 (DST)

### 6.1 什么是 DST

大小在编译时未知的类型，必须通过指针访问。

```rust
// DST 类型
str              // 字符串切片
[T]              // 切片
dyn Trait        // trait 对象
```

### 6.2 胖指针

DST 的指针是"胖指针"，包含地址和元数据。

```rust
// 瘦指针 (thin pointer)
let x: &i32 = &42;  // 只有地址

// 胖指针 (fat pointer)
let s: &[i32] = &[1, 2, 3];  // 地址 + 长度
let t: &dyn Debug = &42;      // 地址 + vtable 指针
```

### 6.3 自定义 DST

```rust
// 通过组合创建 DST
struct MySlice<T> {
    header: u32,
    data: [T],  // 最后一项可以是 DST
}

// 使用
let slice: &MySlice<i32> = /* ... */;
```

---

## 7. 布局优化技巧

### 7.1 字段排序

```rust
// 坏的排序 (24 bytes)
struct Bad {
    a: u8,      // 1 + 7
    b: u64,     // 8
    c: u8,      // 1 + 7
    d: u64,     // 8
}

// 好的排序 (24 bytes → 24 bytes，但更好)
struct Good {
    b: u64,     // 8
    d: u64,     // 8
    a: u8,      // 1
    c: u8,      // 1 + 6
}
```

### 7.2 使用枚举代替标记 + 数据

```rust
// 坏的 (16 bytes)
struct Bad {
    is_a: bool,  // 1 + 7
    a_data: u64, // 8
}

// 好的 (16 bytes，但语义更好)
enum Good {
    A(u64),
    B,
}
```

### 7.3 Box 大字段

```rust
// 如果枚举变体大小差异大
enum LargeEnum {
    Small(u8),
    Large([u8; 1000]),
}
// 整个枚举大小 = 最大变体 = ~1000 bytes

// 优化
enum Optimized {
    Small(u8),
    Large(Box<[u8; 1000]>),
}
// 大小 = Box 的大小 (8 bytes) + tag
```

---

## 8. FFI 布局兼容性

### 8.1 C 结构体映射

```c
// C 代码
typedef struct {
    uint8_t a;
    uint32_t b;
    uint16_t c;
} CStruct;
```

```rust
// Rust 映射
#[repr(C)]
pub struct RustStruct {
    pub a: u8,
    pub b: u32,
    pub c: u16,
}

assert_eq!(mem::size_of::<RustStruct>(), 12);
```

### 8.2 平台差异

```rust
// usize/isize 大小因平台而异
// 64-bit: 8 bytes
// 32-bit: 4 bytes

#[repr(C)]
struct PlatformDependent {
    ptr: *const u8,  // 大小可变!
}
```

### 8.3 布局验证

```rust
#[cfg(test)]
mod tests {
    use std::mem;

    #[test]
    fn test_layout() {
        assert_eq!(mem::size_of::<MyStruct>(), 16);
        assert_eq!(mem::align_of::<MyStruct>(), 8);
    }
}
```

---

## 参考

- [The Rust Reference - Type Layout](https://doc.rust-lang.org/reference/type-layout.html)
- [The Rustonomicon - Data Layout](https://doc.rust-lang.org/nomicon/data.html)
- [std::mem](https://doc.rust-lang.org/std/mem/)

---

*文档版本: 1.0.0*
*最后更新: 2026-03-07*
