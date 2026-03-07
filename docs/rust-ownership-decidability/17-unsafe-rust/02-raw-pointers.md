# 原始指针深度解析

> **权威来源**: The Rust Reference, std::ptr 文档
> **Rust 版本**: 1.94.0
> **难度**: 🔴 高级
> **前置知识**: Unsafe Rust 概述

---

## 目录

- [原始指针深度解析](#原始指针深度解析)
  - [目录](#目录)
  - [1. 原始指针基础](#1-原始指针基础)
    - [1.1 定义](#11-定义)
    - [1.2 两种原始指针](#12-两种原始指针)
  - [2. 创建与转换](#2-创建与转换)
    - [2.1 从引用创建](#21-从引用创建)
    - [2.2 与指针的转换](#22-与指针的转换)
    - [2.3 空指针](#23-空指针)
  - [3. 解引用与访问](#3-解引用与访问)
    - [3.1 基本解引用](#31-基本解引用)
    - [3.2 安全包装方法](#32-安全包装方法)
    - [3.3 读取与移动](#33-读取与移动)
  - [4. 指针运算](#4-指针运算)
    - [4.1 偏移](#41-偏移)
    - [4.2 距离计算](#42-距离计算)
    - [4.3 对齐检查](#43-对齐检查)
  - [5. 与引用的对比](#5-与引用的对比)
    - [5.1 语义对比](#51-语义对比)
    - [5.2 何时使用原始指针](#52-何时使用原始指针)
  - [6. 常见模式](#6-常见模式)
    - [6.1 模式 1: 安全包装](#61-模式-1-安全包装)
    - [6.2 模式 2: 可选的 unsafe 优化](#62-模式-2-可选的-unsafe-优化)
    - [6.3 模式 3: 类型双关 (谨慎使用)](#63-模式-3-类型双关-谨慎使用)
  - [7. 陷阱与 UB](#7-陷阱与-ub)
    - [7.1 常见 UB](#71-常见-ub)
    - [7.2 安全使用检查清单](#72-安全使用检查清单)
  - [8. 实战: 实现自定义迭代器](#8-实战-实现自定义迭代器)
  - [参考](#参考)

---

## 1. 原始指针基础

### 1.1 定义

原始指针 (`*const T` 和 `*mut T`) 是 Rust 中最底层的指针类型，它们：

- 可以为空 (`null`)
- 可以悬垂 (dangling)
- 不参与所有权系统
- 不检查生命周期
- 可以别名 (多个指针指向同一地址)

```rust
let x = 5;
let r = &x as *const i32;  // 从引用创建原始指针
```

### 1.2 两种原始指针

| 类型 | 可变 | 用途 |
|-----|------|------|
| `*const T` | 否 | 只读访问、C 兼容性 |
| `*mut T` | 是 | 读写访问、内存修改 |

```rust
let x = 5;
const_ptr: *const i32 = &x;      // 不可变原始指针
mut_ptr: *mut i32 = &mut y;       // 可变原始指针
```

**注意**: `*const T` 可以通过转换变成 `*mut T`，但这通常是不安全的。

---

## 2. 创建与转换

### 2.1 从引用创建

```rust
let mut x = 5;

// 从共享引用创建
let r1: *const i32 = &x;

// 从可变引用创建
let r2: *mut i32 = &mut x;

// 显式转换
let r3 = &x as *const i32;
```

### 2.2 与指针的转换

```rust
// 引用 → 原始指针 (安全)
let x = 5;
let r: *const i32 = &x;

// 原始指针 → 引用 (unsafe)
unsafe {
    let ref_x: &i32 = &*r;  // 解引用后取引用
}

// 使用 as_ref() 方法
unsafe {
    if let Some(ref_x) = r.as_ref() {
        println!("{}", ref_x);
    }
}
```

### 2.3 空指针

```rust
use std::ptr;

// 创建空指针
let p: *const i32 = ptr::null();
let mut_p: *mut i32 = ptr::null_mut();

// 检查是否为空
assert!(p.is_null());
```

---

## 3. 解引用与访问

### 3.1 基本解引用

```rust
let x = 42;
let ptr = &x as *const i32;

unsafe {
    assert_eq!(*ptr, 42);  // 解引用
}
```

### 3.2 安全包装方法

```rust
let mut x = 42;
let ptr = &mut x as *mut i32;

// as_ref() - 安全地获取引用
unsafe {
    if let Some(val) = ptr.as_ref() {
        println!("{}", val);  // 42
    }
}

// as_mut() - 安全地获取可变引用
unsafe {
    if let Some(val) = ptr.as_mut() {
        *val = 100;
    }
}

// read() - 读取值而不移动
unsafe {
    let val = ptr.read();  // 复制值
    println!("{}", val);   // 100
    // ptr 仍然有效
}

// write() - 写入值
unsafe {
    ptr.write(200);
}
```

### 3.3 读取与移动

```rust
let x = String::from("hello");
let ptr = &x as *const String;

// read() - 复制值
unsafe {
    let s = ptr.read();  // s 是 x 的副本
    println!("{}", s);   // "hello"
    println!("{}", x);   // 仍然可用! (因为 String 实现了 Copy? 不，这是 UB!)
}

// ❌ 上面的代码实际上是 UB!
// String 不实现 Copy，read() 后 x 和 s 拥有同一份数据
// 正确做法是使用 ptr::read 后不再使用原值
```

**修正版本**:

```rust
let x = String::from("hello");
let ptr = &x as *const String;

unsafe {
    let s = ptr.read();  // s 拥有数据
    mem::forget(x);      // 防止 x 被 drop
    // 现在只有 s 拥有数据
}
```

---

## 4. 指针运算

### 4.1 偏移

```rust
let arr = [1, 2, 3, 4, 5];
let ptr = arr.as_ptr();

unsafe {
    // offset() - 按元素偏移
    let p2 = ptr.offset(2);
    assert_eq!(*p2, 3);

    // 负偏移
    let p0 = p2.offset(-2);
    assert_eq!(*p0, 1);

    // add() - 正偏移的简写
    let p3 = ptr.add(3);
    assert_eq!(*p3, 4);

    // sub() - 负偏移的简写
    let p1 = ptr.add(3).sub(2);
    assert_eq!(*p1, 2);
}
```

### 4.2 距离计算

```rust
let arr = [1, 2, 3, 4, 5];
let start = arr.as_ptr();
let end = unsafe { start.add(4) };

unsafe {
    let distance = end.offset_from(start);
    assert_eq!(distance, 4);
}
```

### 4.3 对齐检查

```rust
let x = 5u32;
let ptr = &x as *const u32;

assert!(ptr.is_aligned());
assert!(ptr.is_aligned_to(4));  // u32 对齐到 4 字节
```

---

## 5. 与引用的对比

### 5.1 语义对比

| 特性 | `&T` / `&mut T` | `*const T` / `*mut T` |
|-----|----------------|----------------------|
| 有效性 | 编译器保证 | 程序员保证 |
| 空值 | 不允许 | 允许 |
| 悬垂 | 编译器防止 | 可能发生 |
| 别名规则 | 严格 (XOR) | 无限制 |
| 生命周期 | 编译器检查 | 不检查 |
| 解引用 | 安全 | 需要 `unsafe` |
| 指针运算 | 不允许 | 允许 |

### 5.2 何时使用原始指针

**使用原始指针的场景**:

1. **与 C 代码交互 (FFI)**

```rust
extern "C" {
    fn c_function() -> *const c_char;
}
```

1. **构建复杂数据结构**

```rust
// 链表节点
struct Node<T> {
    data: T,
    next: *mut Node<T>,  // 原始指针允许共享所有权
}
```

1. **性能关键代码**

```rust
// 避免边界检查
unsafe {
    *ptr.add(index) = value;
}
```

1. **实现底层抽象**

```rust
// Vec 的内部实现
pub struct Vec<T> {
    ptr: *mut T,
    len: usize,
    cap: usize,
}
```

---

## 6. 常见模式

### 6.1 模式 1: 安全包装

```rust
pub struct SafeSlice<T> {
    ptr: *const T,
    len: usize,
}

impl<T> SafeSlice<T> {
    pub fn new(slice: &[T]) -> Self {
        Self {
            ptr: slice.as_ptr(),
            len: slice.len(),
        }
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len {
            return None;
        }
        unsafe { Some(&*self.ptr.add(index)) }
    }
}
```

### 6.2 模式 2: 可选的 unsafe 优化

```rust
pub fn get_unchecked(&self, index: usize) -> &T {
    debug_assert!(index < self.len);
    unsafe { &*self.ptr.add(index) }
}

// 使用
let slice = SafeSlice::new(&[1, 2, 3]);
println!("{}", slice.get_unchecked(1));  // 2
```

### 6.3 模式 3: 类型双关 (谨慎使用)

```rust
// 查看 f32 的位表示
fn float_to_bits(f: f32) -> u32 {
    unsafe { std::mem::transmute(f) }
}

// 或者使用 union
union FloatBits {
    f: f32,
    u: u32,
}

fn float_to_bits_safe(f: f32) -> u32 {
    unsafe { FloatBits { f }.u }
}
```

---

## 7. 陷阱与 UB

### 7.1 常见 UB

```rust
// ❌ UB 1: 解引用空指针
let ptr: *const i32 = std::ptr::null();
unsafe { *ptr; }

// ❌ UB 2: 解引用未对齐指针
let arr: [u8; 4] = [0, 0, 0, 0];
let ptr = arr.as_ptr().add(1) as *const u32;  // 未对齐到 4
unsafe { *ptr; }  // UB!

// ❌ UB 3: 越界访问
let arr = [1, 2, 3];
let ptr = arr.as_ptr();
unsafe { *ptr.add(100); }  // UB!

// ❌ UB 4: 使用已释放内存
let ptr: *const i32 = {
    let x = 5;
    &x
};
unsafe { *ptr; }  // UB! x 已释放

// ❌ UB 5: 数据竞争
static mut X: i32 = 0;
unsafe {
    X += 1;  // 如果有其他线程同时访问 - UB!
}
```

### 7.2 安全使用检查清单

```rust
unsafe {
    // 解引用前检查:
    // ✓ 指针非空
    assert!(!ptr.is_null());

    // ✓ 指针已对齐 (如果需要)
    assert!(ptr.is_aligned());

    // ✓ 在有效范围内
    assert!(offset < len);

    // ✓ 生命周期有效
    // (这需要程序员的逻辑保证)

    *ptr  // 现在相对安全
}
```

---

## 8. 实战: 实现自定义迭代器

```rust
/// 基于原始指针的数组迭代器
pub struct PtrIter<T> {
    ptr: *const T,
    end: *const T,
}

impl<T> PtrIter<T> {
    pub fn new(slice: &[T]) -> Self {
        let ptr = slice.as_ptr();
        // 注意: 即使 slice 为空，这也是安全的
        let end = unsafe { ptr.add(slice.len()) };
        Self { ptr, end }
    }
}

impl<T> Iterator for PtrIter<T> {
    type Item = &'static T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.ptr == self.end {
            return None;
        }
        unsafe {
            let item = &*self.ptr;
            self.ptr = self.ptr.add(1);
            Some(item)
        }
    }
}

// 使用
let arr = [1, 2, 3, 4, 5];
let iter = PtrIter::new(&arr);
for x in iter {
    println!("{}", x);
}
```

---

## 参考

- [std::ptr](https://doc.rust-lang.org/std/ptr/)
- [The Rustonomicon - Pointers](https://doc.rust-lang.org/nomicon/pointers.html)

---

*文档版本: 1.0.0*
*最后更新: 2026-03-07*
