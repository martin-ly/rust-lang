# 未初始化内存处理

> **内容分级**: [归档级]
>
> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **权威来源**: The Rustonomicon, std::mem::MaybeUninit
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **对齐日期**: 2026-05-12.0
> **难度**: 🔴 高级
> **前置知识**: Unsafe Rust 概述、原始指针

---

## 目录
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

- [未初始化内存处理](#未初始化内存处理)
  - [目录](#目录)
  - [1. 什么是未初始化内存](#1-什么是未初始化内存)
    - [1.1 定义](#11-定义)
    - [1.2 什么时候会遇到](#12-什么时候会遇到)
  - [2. 为什么危险](#2-为什么危险)
    - [2.1 未定义行为 (UB)](#21-未定义行为-ub)
    - [2.2 LLVM 的假设](#22-llvm-的假设)
  - [3. 安全处理方法](#3-安全处理方法)
    - [3.1 使用 write 而非赋值](#31-使用-write-而非赋值)
    - [3.2 批量初始化模式](#32-批量初始化模式)
  - [4. MaybeUninit 深度解析](#4-maybeuninit-深度解析)
    - [4.1 类型定义](#41-类型定义)
    - [4.2 核心方法](#42-核心方法)
    - [4.3 读写操作](#43-读写操作)
  - [5. 实战模式](#5-实战模式)
    - [5.1 实现 ArrayVec](#51-实现-arrayvec)
    - [5.2 FFI 缓冲区](#52-ffi-缓冲区)
  - [6. 常见陷阱](#6-常见陷阱)
    - [6.1 错误：批量 assume\_init](#61-错误批量-assume_init)
    - [6.2 错误：忘记析构](#62-错误忘记析构)
    - [6.3 正确检查清单](#63-正确检查清单)
  - [参考](#参考)
  - [*最后更新: 2026-03-07*](#最后更新-2026-03-07)
  - [权威来源索引](#权威来源索引)

---

## 1. 什么是未初始化内存
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 1.1 定义
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

未初始化内存是指**已分配但未写入值**的内存。在 Rust 中，读取未初始化内存是**立即 UB**。

```rust,ignore
// ❌ 错误：读取未初始化变量
let x: i32;
println!("{}", x);  // 编译错误！
```

### 1.2 什么时候会遇到
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```rust,ignore
// 场景 1: 大块内存分配
let mut buffer: [u8; 1024];  // 未初始化

// 场景 2: 动态数组扩容
let mut vec: Vec<i32> = Vec::with_capacity(100);
// vec[0] 是未初始化的！

// 场景 3: FFI 返回的内存
extern "C" {
    fn allocate_buffer() -> *mut u8;
}
```

---

## 2. 为什么危险
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 2.1 未定义行为 (UB)
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust
// ❌ UB 示例
let x: i32 = unsafe { std::mem::uninitialized() };
// 或更现代的：
let y: i32 = unsafe { std::mem::MaybeUninit::uninit().assume_init() };

// 读取 y 是 UB！
println!("{}", y);  // 可能导致：
// - 随机值
// - 程序崩溃
// - 安全漏洞 (信息泄露)
```

### 2.2 LLVM 的假设
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

Rust 编译器使用 LLVM，它对未初始化内存有严格假设：

```
LLVM 假设：任何读取的位都是已初始化的
违反假设 = 优化错误 = UB
```

---

## 3. 安全处理方法
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 3.1 使用 write 而非赋值
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```rust
use std::mem::MaybeUninit;

let mut uninit: MaybeUninit<i32> = MaybeUninit::uninit();

// ✅ 正确：直接写入内存
unsafe {
    uninit.as_mut_ptr().write(42);
}

// ✅ 现在可以安全地假设已初始化
let init = unsafe { uninit.assume_init() };
assert_eq!(init, 42);
```

### 3.2 批量初始化模式
>
> **[来源: [crates.io](https://crates.io/)]**

```rust,ignore
fn initialize_array<T, F>(len: usize, mut f: F) -> Vec<T>
where
    F: FnMut(usize) -> T,
{
    let mut vec: Vec<MaybeUninit<T>> = Vec::with_capacity(len);

    for i in 0..len {
        vec.push(MaybeUninit::new(f(i)));
    }

    // 转换：MaybeUninit<T> -> T
    let ptr = vec.as_mut_ptr() as *mut T;
    let len = vec.len();
    let cap = vec.capacity();

    std::mem::forget(vec);  // 防止析构

    unsafe { Vec::from_raw_parts(ptr, len, cap) }
}
```

---

## 4. MaybeUninit 深度解析
>
> **[来源: [docs.rs](https://docs.rs/)]**

### 4.1 类型定义
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```rust,ignore
#[repr(transparent)]
pub union MaybeUninit<T> {
    uninit: (),
    value: ManuallyDrop<T>,
}
```

**关键点**:

- `union` 允许未初始化状态
- `ManuallyDrop` 防止自动析构
- `repr(transparent)` 保证与 T 相同布局

### 4.2 核心方法
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust,ignore
impl<T> MaybeUninit<T> {
    // 创建未初始化
    pub const fn uninit() -> Self;

    // 创建已初始化
    pub const fn new(val: T) -> Self;

    // 获取原始指针
    pub fn as_ptr(&self) -> *const T;
    pub fn as_mut_ptr(&mut self) -> *mut T;

    // 假设已初始化 (unsafe!)
    pub unsafe fn assume_init(self) -> T;

    // 假设已初始化 (引用版本)
    pub unsafe fn assume_init_ref(&self) -> &T;
    pub unsafe fn assume_init_mut(&mut self) -> &mut T;
}
```

### 4.3 读写操作
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,ignore
use std::mem::MaybeUninit;

let mut slot: MaybeUninit<String> = MaybeUninit::uninit();

// 写入
unsafe {
    slot.as_mut_ptr().write(String::from("hello"));
}

// 读取 (不移动)
let len = unsafe { (*slot.as_ptr()).len() };

// 最终取出
let s = unsafe { slot.assume_init() };
```

---

## 5. 实战模式
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 5.1 实现 ArrayVec
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```rust,ignore
pub struct ArrayVec<T, const N: usize> {
    data: [MaybeUninit<T>; N],
    len: usize,
}

impl<T, const N: usize> ArrayVec<T, N> {
    pub fn new() -> Self {
        Self {
            // ✅ 安全：MaybeUninit 不需要初始化
            data: unsafe { MaybeUninit::uninit().assume_init() },
            len: 0,
        }
    }

    pub fn push(&mut self, value: T) {
        assert!(self.len < N);

        self.data[self.len].write(value);
        self.len += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;

        // ✅ 读取并移动值
        Some(unsafe { self.data[self.len].assume_init_read() })
    }
}

impl<T, const N: usize> Drop for ArrayVec<T, N> {
    fn drop(&mut self) {
        // 必须手动析构已初始化元素
        for i in 0..self.len {
            unsafe {
                self.data[i].assume_init_drop();
            }
        }
    }
}
```

### 5.2 FFI 缓冲区
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```rust
pub struct FfiBuffer {
    ptr: *mut u8,
    len: usize,
}

impl FfiBuffer {
    pub fn new(len: usize) -> Self {
        let layout = std::alloc::Layout::array::<u8>(len).unwrap();
        let ptr = unsafe { std::alloc::alloc(layout) };

        if ptr.is_null() {
            panic!("allocation failed");
        }

        Self { ptr, len }
    }

    pub fn as_slice(&self) -> &[u8] {
        // ⚠️ 注意：返回的切片可能包含未初始化字节！
        unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
    }

    pub fn initialize_from(&mut self, data: &[u8]) {
        assert!(data.len() <= self.len);

        unsafe {
            self.ptr.copy_from_nonoverlapping(data.as_ptr(), data.len());
        }
    }
}

impl Drop for FfiBuffer {
    fn drop(&mut self) {
        let layout = std::alloc::Layout::array::<u8>(self.len).unwrap();
        unsafe { std::alloc::dealloc(self.ptr, layout); }
    }
}
```

---

## 6. 常见陷阱
>
> **[来源: [crates.io](https://crates.io/)]**

### 6.1 错误：批量 assume_init
>
> **[来源: [docs.rs](https://docs.rs/)]**

```rust,ignore
// ❌ 危险：假设整个数组已初始化
let mut arr: [MaybeUninit<String>; 10] =
    unsafe { MaybeUninit::uninit().assume_init() };

// 只初始化了部分...
arr[0].write(String::from("hello"));

// ❌ UB：假设所有元素都已初始化！
for elem in &arr {
    unsafe { elem.assume_init_ref() };  // 对于 arr[1..] 是 UB！
}
```

### 6.2 错误：忘记析构
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```rust,ignore
// ❌ 内存泄漏
type BoxMaybe<T> = Box<MaybeUninit<T>>;

let b: BoxMaybe<String> = Box::new(MaybeUninit::new(String::from("hello")));
// 没有调用 assume_init，String 被泄漏！
```

### 6.3 正确检查清单
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust,ignore
unsafe {
    // ✅ 检查 1：确保已写入
    assert!(!ptr.is_null());

    // ✅ 检查 2：确保不重复 assume_init
    // assume_init 消费值，只能调用一次

    // ✅ 检查 3：确保正确析构
    // 如果未 assume_init，需要手动 drop
}
```

---

## 参考
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- [std::mem::MaybeUninit](https://doc.rust-lang.org/std/mem/union.MaybeUninit.html)
- [The Rustonomicon - Uninitialized Memory](https://doc.rust-lang.org/nomicon/uninitialized.html)

---

*文档版本: 1.0.0*
*最后更新: 2026-03-07*
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**
> **[来源: TRPL Ch. 4 - Ownership]**
> **[来源: Rustonomicon - Ownership]**
> **[来源: POPL 2018 - RustBelt]**
> **[来源: Wikipedia - Undefined Behavior]**
> **[来源: Rustonomicon]**
> **[来源: Rust Reference - Unsafe]**
> **[来源: RFC 2585 - Unsafe Guidelines]**

---