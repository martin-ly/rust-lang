# Unsafe 函数与 Trait

> **Rust 版本**: 1.94.0
> **难度**: 🔴 高级
> **前置知识**: Unsafe Rust 概述

---

## 目录

- [Unsafe 函数与 Trait](#unsafe-函数与-trait)
  - [目录](#目录)
  - [1. Unsafe 函数](#1-unsafe-函数)
    - [1.1 定义与调用](#11-定义与调用)
    - [1.2 安全包装器模式](#12-安全包装器模式)
    - [1.3 Unsafe 函数指针](#13-unsafe-函数指针)
  - [2. Unsafe Trait](#2-unsafe-trait)
    - [2.1 定义与实现](#21-定义与实现)
    - [2.2 自定义 Unsafe Trait](#22-自定义-unsafe-trait)
  - [3. 安全抽象模式](#3-安全抽象模式)
    - [3.1 类型状态模式](#31-类型状态模式)
    - [3.2 不变量封装](#32-不变量封装)
  - [4. 常见模式](#4-常见模式)
    - [4.1 延迟初始化](#41-延迟初始化)
    - [4.2 自定义 Drop](#42-自定义-drop)
  - [5. 文档与契约](#5-文档与契约)
    - [5.1 Safety 文档规范](#51-safety-文档规范)
    - [5.2 不变量文档](#52-不变量文档)

---

## 1. Unsafe 函数

### 1.1 定义与调用

```rust
// 定义 unsafe 函数
unsafe fn dangerous_operation(ptr: *const i32) -> i32 {
    *ptr  // 解引用原始指针
}

// 调用 unsafe 函数
fn main() {
    let x = 42;
    let ptr = &x as *const i32;

    unsafe {
        let value = dangerous_operation(ptr);
        println!("{}", value);
    }
}
```

### 1.2 安全包装器模式

```rust
/// 内部实现使用 unsafe
///
/// # Safety
/// - ptr 必须是非空且对齐的
/// - ptr 必须指向有效的 i32
unsafe fn raw_read(ptr: *const i32) -> i32 {
    *ptr
}

/// 安全的公共 API
///
/// 前置条件检查确保安全
pub fn safe_read(maybe_ptr: Option<&i32>) -> Option<i32> {
    let ptr = maybe_ptr?;
    unsafe {
        // 我们知道 ptr 是有效的，因为 &i32 保证这一点
        Some(raw_read(ptr))
    }
}
```

### 1.3 Unsafe 函数指针

```rust
type UnsafeFn = unsafe fn(*const i32) -> i32;

fn call_unsafe(f: UnsafeFn, ptr: *const i32) -> i32 {
    unsafe { f(ptr) }
}
```

---

## 2. Unsafe Trait

### 2.1 定义与实现

```rust
// 标记 trait，实现者必须保证安全条件
unsafe trait Send {}
unsafe trait Sync {}

// 实现 unsafe trait
struct MyType;

unsafe impl Send for MyType {}
unsafe impl Sync for MyType {}
```

### 2.2 自定义 Unsafe Trait

```rust
/// # Safety
/// 实现者必须保证：
/// - 从指针读取的数据是有效的
/// - 不会导致数据竞争
unsafe trait RawReadable {
    /// # Safety
    /// - ptr 必须指向有效的 Self
    unsafe fn read_from_ptr(ptr: *const Self) -> Self;
}

unsafe impl RawReadable for u32 {
    unsafe fn read_from_ptr(ptr: *const Self) -> Self {
        ptr.read()
    }
}
```

---

## 3. 安全抽象模式

### 3.1 类型状态模式

```rust
use std::marker::PhantomData;

// 状态标记
struct Uninit;
struct Init;

struct SafeBuffer<T, State> {
    ptr: *mut T,
    len: usize,
    _state: PhantomData<State>,
}

impl<T> SafeBuffer<T, Uninit> {
    fn alloc(len: usize) -> Option<Self> {
        let ptr = unsafe { std::alloc::alloc(
            std::alloc::Layout::array::<T>(len).ok()?
        ) as *mut T };

        if ptr.is_null() {
            return None;
        }

        Some(Self {
            ptr,
            len,
            _state: PhantomData,
        })
    }
}

impl<T> SafeBuffer<T, Init> {
    fn get(&self, idx: usize) -> Option<&T> {
        if idx < self.len {
            unsafe { Some(&*self.ptr.add(idx)) }
        } else {
            None
        }
    }
}
```

### 3.2 不变量封装

```rust
pub struct SafeString {
    ptr: *mut u8,
    len: usize,
    // 不变量：ptr[0..len] 总是有效的 UTF-8
}

impl SafeString {
    /// 从 &str 创建，保证不变量
    pub fn new(s: &str) -> Self {
        let len = s.len();
        let ptr = unsafe {
            let p = std::alloc::alloc(
                std::alloc::Layout::array::<u8>(len).unwrap()
            );
            p.copy_from_nonoverlapping(s.as_ptr(), len);
            p
        };

        Self { ptr, len }
    }

    /// 利用不变量提供安全 API
    pub fn as_str(&self) -> &str {
        unsafe {
            std::str::from_utf8_unchecked(
                std::slice::from_raw_parts(self.ptr, self.len)
            )
        }
    }
}
```

---

## 4. 常见模式

### 4.1 延迟初始化

```rust
use std::sync::Once;

static INIT: Once = Once::new();
static mut DATA: Option<String> = None;

pub fn get_data() -> &'static str {
    unsafe {
        INIT.call_once(|| {
            DATA = Some(expensive_init());
        });
        DATA.as_ref().unwrap()
    }
}

fn expensive_init() -> String {
    String::from("initialized")
}
```

### 4.2 自定义 Drop

```rust
struct RawBuffer {
    ptr: *mut u8,
    len: usize,
}

impl Drop for RawBuffer {
    fn drop(&mut self) {
        unsafe {
            std::alloc::dealloc(
                self.ptr,
                std::alloc::Layout::array::<u8>(self.len).unwrap()
            );
        }
    }
}
```

---

## 5. 文档与契约

### 5.1 Safety 文档规范

```rust
/// # Safety
///
/// ## 前置条件
/// - `ptr` 必须是非空的
/// - `ptr` 必须是对齐的
/// - `ptr` 必须指向有效的 `T`
///
/// ## 后置条件
/// - 返回的值是 `ptr` 指向的值的副本
/// - `ptr` 仍然有效，可以再次读取
///
/// ## 示例
/// ```
/// let x = 42;
/// let ptr = &x as *const i32;
/// unsafe {
///     assert_eq!(read_ptr(ptr), 42);
/// }
/// ```
unsafe fn read_ptr<T: Copy>(ptr: *const T) -> T {
    ptr.read()
}
```

### 5.2 不变量文档

```rust
/// 一个保证元素唯一性的集合
///
/// # 安全不变量
/// - 没有两个元素相等（由类型系统保证）
/// - 所有元素都是有效的（由所有权保证）
pub struct UniqueVec<T> {
    inner: Vec<T>,
}

impl<T: PartialEq> UniqueVec<T> {
    /// # Safety
    /// - 调用者必须保证 `item` 不在集合中
    pub unsafe fn push_unchecked(&mut self, item: T) {
        self.inner.push(item);
    }

    /// 安全的包装，检查唯一性
    pub fn push(&mut self, item: T) -> Result<(), T> {
        if self.inner.contains(&item) {
            return Err(item);
        }
        unsafe { self.push_unchecked(item); }
        Ok(())
    }
}
```

---

*文档版本: 1.0.0*
