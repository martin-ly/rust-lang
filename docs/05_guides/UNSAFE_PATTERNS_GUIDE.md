# Unsafe Rust 模式库指南

> **文档定位**: Rust 学习项目 - Unsafe Rust 最佳实践与模式库
> **创建日期**: 2026-03-17
> **最后更新**: 2026-03-17
> **Rust 版本**: 1.94.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📋 目录

- [Unsafe Rust 模式库指南](#unsafe-rust-模式库指南)
  - [📋 目录](#-目录)
  - [1. 简介与概述](#1-简介与概述)
    - [目标读者](#目标读者)
    - [前置知识](#前置知识)
  - [2. Unsafe Rust 核心概念](#2-unsafe-rust-核心概念)
    - [2.1 什么是 Unsafe Rust](#21-什么是-unsafe-rust)
    - [2.2 Unsafe 的五种能力](#22-unsafe-的五种能力)
    - [2.3 安全抽象原则](#23-安全抽象原则)
  - [3. 原始指针模式](#3-原始指针模式)
    - [模式 3.1: 裸指针算术](#模式-31-裸指针算术)
      - [正确做法](#正确做法)
      - [安全分析](#安全分析)
      - [错误做法对比](#错误做法对比)
      - [Miri 验证](#miri-验证)
    - [模式 3.2: 指针类型转换](#模式-32-指针类型转换)
      - [正确做法](#正确做法-1)
      - [安全分析](#安全分析-1)
      - [常见陷阱](#常见陷阱)
    - [模式 3.3: 自定义智能指针](#模式-33-自定义智能指针)
      - [正确做法](#正确做法-2)
      - [安全分析](#安全分析-2)
      - [Miri 验证](#miri-验证-1)
    - [模式 3.4: 指针别名管理](#模式-34-指针别名管理)
      - [正确做法](#正确做法-3)
      - [安全分析](#安全分析-3)
  - [4. Union 模式](#4-union-模式)
    - [模式 4.1: 类型双关](#模式-41-类型双关)
      - [正确做法](#正确做法-4)
      - [安全分析](#安全分析-4)
      - [Miri 验证](#miri-验证-2)
    - [模式 4.2: 节省内存的数据结构](#模式-42-节省内存的数据结构)
      - [正确做法](#正确做法-5)
      - [安全分析](#安全分析-5)
  - [5. Transmute 模式](#5-transmute-模式)
    - [模式 5.1: 字节重解释](#模式-51-字节重解释)
      - [正确做法](#正确做法-6)
      - [安全分析](#安全分析-6)
    - [模式 5.2: 类型擦除](#模式-52-类型擦除)
      - [正确做法](#正确做法-7)
      - [安全分析](#安全分析-7)
  - [6. FFI 边界模式](#6-ffi-边界模式)
    - [模式 6.1: 回调函数](#模式-61-回调函数)
      - [正确做法](#正确做法-8)
      - [安全分析](#安全分析-8)
    - [模式 6.2: 不透明指针](#模式-62-不透明指针)
      - [正确做法](#正确做法-9)
      - [安全分析](#安全分析-9)
    - [模式 6.3: 字符串传递](#模式-63-字符串传递)
      - [正确做法](#正确做法-10)
      - [安全分析](#安全分析-10)
  - [7. Miri 使用指南](#7-miri-使用指南)
    - [7.1 安装与配置](#71-安装与配置)
    - [7.2 基本用法](#72-基本用法)
    - [7.3 常见错误检测](#73-常见错误检测)
    - [7.4 CI 集成](#74-ci-集成)
  - [8. 安全审查清单](#8-安全审查清单)
    - [8.1 代码审查要点](#81-代码审查要点)
    - [8.2 文档化要求](#82-文档化要求)
    - [8.3 测试策略](#83-测试策略)
  - [9. 参考与资源](#9-参考与资源)
    - [官方文档](#官方文档)
    - [项目内相关文档](#项目内相关文档)
    - [学术资源](#学术资源)

---

## 1. 简介与概述

本指南是 Rust 学习项目的重要组成部分，旨在提供 Unsafe Rust 的**系统化模式库**。与官方的 [Rustonomicon](https://doc.rust-lang.org/nomicon/) 不同，本指南专注于：

- **可复用的代码模式** - 经过验证的安全抽象模板
- **实战案例分析** - 真实场景中的最佳实践
- **Miri 验证指导** - 如何验证 unsafe 代码的安全性
- **错误模式对比** - 正确做法与错误做法的直观对比

### 目标读者

- 需要实现底层数据结构的系统程序员
- 编写 FFI 绑定的高级开发者
- 研究 Rust 内存模型的学习者
- 需要优化性能关键代码的工程师

### 前置知识

- 掌握 Rust 所有权和借用规则
- 理解生命周期系统
- 熟悉基本的数据结构实现
- 了解 C 语言内存模型（对 FFI 部分有帮助）

---

## 2. Unsafe Rust 核心概念

### 2.1 什么是 Unsafe Rust

Rust 的 `unsafe` 关键字提供了突破编译器安全检查的能力。**关键点**：`unsafe` 并不意味着代码一定危险，而是意味着编译器无法自动验证某些安全属性，这些验证责任转移到了程序员身上。

```rust
// safe Rust: 编译器保证内存安全
fn safe_code() {
    let mut v = vec![1, 2, 3];
    v.push(4);  // 编译器检查边界和所有权
}

// unsafe Rust: 程序员承担安全责任
unsafe fn unsafe_code(ptr: *mut i32) {
    *ptr = 42;  // 编译器不检查 ptr 是否有效
}
```

### 2.2 Unsafe 的五种能力

| 能力 | 语法 | 风险等级 | 常见场景 |
|------|------|----------|----------|
| **解引用原始指针** | `*ptr` | 🔴 高 | 自定义集合、FFI |
| **调用 unsafe 函数** | `unsafe_fn()` | 🟡 中 | 底层系统调用 |
| **实现 unsafe trait** | `unsafe impl` | 🟡 中 | Send/Sync 标记 |
| **访问 union 字段** | `union.field` | 🟡 中 | 类型双关、FFI |
| **使用内联汇编** | `asm!()` | 🔴 高 | 底层硬件操作 |

### 2.3 安全抽象原则

**核心原则**: 用 safe API 包装 unsafe 实现，确保安全边界。

```rust
/// # Safety
/// `ptr` 必须是非空且正确对齐的有效指针
unsafe fn dangerous_write(ptr: *mut i32, value: i32) {
    *ptr = value;
}

/// 安全的公开 API
pub fn safe_write(target: &mut i32, value: i32) {
    // 在 safe API 内部使用 unsafe
    unsafe { dangerous_write(target, value) }
}

// 使用者无需关心 unsafe
fn main() {
    let mut x = 0;
    safe_write(&mut x, 42);  // ✅ 完全安全
}
```

---

## 3. 原始指针模式

原始指针 (`*const T` 和 `*mut T`) 是 Rust 中最底层的指针类型。它们不参与所有权系统，不进行生命周期检查，提供最大的灵活性但也带来最大的风险。

### 模式 3.1: 裸指针算术

**场景说明**: 实现高性能的内存缓冲区操作，需要直接控制指针位置。常见于网络协议解析、二进制数据处理和自定义集合实现。

#### 正确做法

```rust
/// 安全的缓冲区读取器，支持高效的指针算术操作
pub struct BufferReader<'a> {
    // 数据起始位置
    start: *const u8,
    // 数据结束位置（最后一个有效字节之后）
    end: *const u8,
    // 当前读取位置
    current: *const u8,
    // 保留生命周期标记
    _marker: std::marker::PhantomData<&'a [u8]>,
}

impl<'a> BufferReader<'a> {
    /// 从字节切片创建读取器
    pub fn new(data: &'a [u8]) -> Self {
        let start = data.as_ptr();
        // 计算结束位置，处理空切片情况
        let end = unsafe { start.add(data.len()) };

        Self {
            start,
            end,
            current: start,
            _marker: std::marker::PhantomData,
        }
    }

    /// 安全地读取一个字节
    pub fn read_u8(&mut self) -> Option<u8> {
        // 边界检查 - 在 safe 代码中完成
        if self.current >= self.end {
            return None;
        }

        // 读取字节 - unsafe 操作
        let value = unsafe { *self.current };

        // 安全地推进指针
        self.current = unsafe { self.current.add(1) };

        Some(value)
    }

    /// 读取指定数量的字节
    pub fn read_bytes(&mut self, count: usize) -> Option<&'a [u8]> {
        // 计算剩余字节数
        let remaining = unsafe { self.end.offset_from(self.current) as usize };

        // 边界检查
        if count > remaining {
            return None;
        }

        // 创建切片 - 使用 from_raw_parts 需要 unsafe
        let slice = unsafe {
            std::slice::from_raw_parts(self.current, count)
        };

        // 推进指针
        self.current = unsafe { self.current.add(count) };

        Some(slice)
    }

    /// 读取 u32（大端序）
    pub fn read_u32_be(&mut self) -> Option<u32> {
        let bytes = self.read_bytes(4)?;
        Some(
            ((bytes[0] as u32) << 24)
            | ((bytes[1] as u32) << 16)
            | ((bytes[2] as u32) << 8)
            | (bytes[3] as u32)
        )
    }

    /// 获取当前位置
    pub fn position(&self) -> usize {
        unsafe { self.current.offset_from(self.start) as usize }
    }

    /// 获取剩余字节数
    pub fn remaining(&self) -> usize {
        unsafe { self.end.offset_from(self.current) as usize }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_buffer_reader() {
        let data = vec![0x01, 0x02, 0x03, 0x04, 0x05];
        let mut reader = BufferReader::new(&data);

        assert_eq!(reader.read_u8(), Some(0x01));
        assert_eq!(reader.read_u8(), Some(0x02));

        let bytes = reader.read_bytes(2).unwrap();
        assert_eq!(bytes, &[0x03, 0x04]);

        assert_eq!(reader.read_u8(), Some(0x05));
        assert_eq!(reader.read_u8(), None);  // 越界
    }

    #[test]
    fn test_read_u32_be() {
        let data = vec![0x12, 0x34, 0x56, 0x78];
        let mut reader = BufferReader::new(&data);

        assert_eq!(reader.read_u32_be(), Some(0x12345678));
    }
}
```

#### 安全分析

**为什么这个实现是安全的？**

1. **边界检查完全在 safe 代码中**: 所有 `read_*` 方法都在调用 unsafe 操作前进行边界检查
2. **生命周期保证**: `PhantomData<&'a [u8]>` 确保读取器不会超过底层数据的生命周期
3. **指针有效性**: 所有指针都派生自有效的切片引用，且只在分配的范围内偏移
4. **无悬垂指针风险**: 指针只在 `new` 时创建，后续操作只是偏移，不会重新分配

#### 错误做法对比

```rust
/// ❌ 错误的实现：不进行边界检查
pub struct UnsafeBufferReader {
    ptr: *const u8,
    len: usize,
    pos: usize,
}

impl UnsafeBufferReader {
    pub fn read_u8_unchecked(&mut self) -> u8 {
        // ❌ 危险：没有检查 pos < len
        unsafe {
            let val = *self.ptr.add(self.pos);
            self.pos += 1;
            val
        }
    }

    pub fn read_u32_unchecked(&mut self) -> u32 {
        // ❌ 危险：没有检查是否有4个字节
        unsafe {
            let ptr = self.ptr.add(self.pos) as *const u32;
            self.pos += 4;
            *ptr  // 可能对齐错误！
        }
    }
}

/// ❌ 另一个常见错误：使用已释放的指针
fn dangling_pointer_example() {
    let ptr: *const u8 = {
        let data = vec![1, 2, 3];
        data.as_ptr()  // data 在这里被释放
    };  // ptr 现在是悬垂指针

    // ❌ UB: 使用悬垂指针
    unsafe {
        let _ = *ptr;  // 未定义行为！
    }
}
```

#### Miri 验证

```bash
# 保存上述代码到 src/lib.rs，然后运行：
cargo miri test

# 预期输出：所有测试通过，没有 UB 报告
```

---

### 模式 3.2: 指针类型转换

**场景说明**: 在 FFI 边界、序列化/反序列化或内存映射中，需要将一个类型的指针转换为另一个类型的指针。这涉及到对齐、大小和内存布局的仔细管理。

#### 正确做法

```rust
use std::alloc::{alloc, dealloc, Layout};
use std::ptr::NonNull;

/// 类型安全的指针转换包装
pub struct TypedPointer<T> {
    ptr: NonNull<T>,
    layout: Layout,
}

impl<T> TypedPointer<T> {
    /// 分配指定数量的元素
    pub fn alloc(count: usize) -> Option<Self> {
        if count == 0 {
            return None;
        }

        let layout = Layout::array::<T>(count).ok()?;

        // 分配内存
        let ptr = unsafe { alloc(layout) };
        if ptr.is_null() {
            return None;
        }

        Some(Self {
            ptr: unsafe { NonNull::new_unchecked(ptr as *mut T) },
            layout,
        })
    }

    /// 转换为字节指针（用于原始操作）
    pub fn as_byte_ptr(&self) -> *mut u8 {
        self.ptr.as_ptr() as *mut u8
    }

    /// 从字节指针安全转换（检查对齐）
    ///
    /// # Safety
    /// - `byte_ptr` 必须指向至少 `size_of::<T>()` 字节的有效内存
    /// - 内存必须正确对齐到 `align_of::<T>()`
    pub unsafe fn from_aligned_ptr(byte_ptr: *mut u8) -> Option<NonNull<T>> {
        if byte_ptr.is_null() {
            return None;
        }

        // 检查对齐
        let align = std::mem::align_of::<T>();
        if (byte_ptr as usize) % align != 0 {
            return None;
        }

        Some(NonNull::new_unchecked(byte_ptr as *mut T))
    }

    /// 使用未对齐读取（当对齐无法保证时）
    ///
    /// # Safety
    /// - `byte_ptr` 必须指向至少 `size_of::<T>()` 字节的有效内存
    pub unsafe fn read_unaligned_from_bytes(byte_ptr: *const u8) -> T {
        let typed_ptr = byte_ptr as *const T;
        typed_ptr.read_unaligned()
    }

    /// 写入值
    pub fn write(&mut self, index: usize, value: T) {
        assert!(
            index < self.layout.size() / std::mem::size_of::<T>(),
            "索引越界"
        );

        unsafe {
            self.ptr.as_ptr().add(index).write(value);
        }
    }

    /// 读取值
    pub fn read(&self, index: usize) -> T {
        assert!(
            index < self.layout.size() / std::mem::size_of::<T>(),
            "索引越界"
        );

        unsafe {
            self.ptr.as_ptr().add(index).read()
        }
    }
}

impl<T> Drop for TypedPointer<T> {
    fn drop(&mut self) {
        unsafe {
            dealloc(self.ptr.as_ptr() as *mut u8, self.layout);
        }
    }
}

/// 演示：安全的类型转换模式
pub mod type_conversions {
    use super::*;

    /// 模式 1: 通过字节操作进行序列化
    pub fn serialize_u32_to_bytes(value: u32, buffer: &mut [u8]) {
        assert!(buffer.len() >= 4, "缓冲区太小");

        // 使用标准库的安全方法
        let bytes = value.to_le_bytes();
        buffer[..4].copy_from_slice(&bytes);
    }

    /// 模式 2: 从字节反序列化（对齐安全版本）
    pub fn deserialize_u32_from_bytes(buffer: &[u8]) -> Option<u32> {
        if buffer.len() < 4 {
            return None;
        }

        // 方法 A: 使用标准库的安全方法（推荐）
        let bytes: [u8; 4] = [buffer[0], buffer[1], buffer[2], buffer[3]];
        Some(u32::from_le_bytes(bytes))
    }

    /// 模式 3: 使用原始指针进行批量转换（高级）
    ///
    /// # Safety
    /// - `src` 必须包含有效数据
    /// - `dst` 必须有足够的空间
    /// - 类型必须有相同的内存布局
    pub unsafe fn bulk_transmute_copy<T, U>(
        src: &[T],
        dst: &mut [U],
    ) where
        T: Copy,
        U: Copy,
    {
        assert_eq!(
            std::mem::size_of::<T>(),
            std::mem::size_of::<U>(),
            "类型大小必须相同"
        );
        assert!(
            dst.len() >= src.len(),
            "目标缓冲区太小"
        );

        let src_ptr = src.as_ptr();
        let dst_ptr = dst.as_mut_ptr();

        for i in 0..src.len() {
            // 复制值，不执行类型转换
            let val = src_ptr.add(i).read();
            dst_ptr.add(i).write(std::mem::transmute_copy(&val));
        }
    }

    /// 模式 4: 使用 MaybeUninit 进行安全的类型转换
    pub fn safe_transmute_with_maybeuninit<T, U>(value: T) -> U
    where
        T: Copy,
        U: Copy,
    {
        use std::mem::MaybeUninit;

        assert_eq!(
            std::mem::size_of::<T>(),
            std::mem::size_of::<U>(),
            "类型大小必须相同"
        );

        unsafe {
            let src: MaybeUninit<T> = MaybeUninit::new(value);
            src.as_ptr().cast::<U>().read()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::type_conversions::*;

    #[test]
    fn test_typed_pointer() {
        let mut ptr = TypedPointer::<i32>::alloc(5).unwrap();

        ptr.write(0, 10);
        ptr.write(1, 20);
        ptr.write(2, 30);

        assert_eq!(ptr.read(0), 10);
        assert_eq!(ptr.read(1), 20);
    }

    #[test]
    fn test_serialize_deserialize() {
        let value: u32 = 0x12345678;
        let mut buffer = [0u8; 4];

        serialize_u32_to_bytes(value, &mut buffer);
        let recovered = deserialize_u32_from_bytes(&buffer).unwrap();

        assert_eq!(value, recovered);
    }

    #[test]
    fn test_bulk_transmute() {
        let src: [u32; 3] = [1, 2, 3];
        let mut dst: [i32; 3] = [0; 3];

        unsafe {
            bulk_transmute_copy(&src, &mut dst);
        }

        assert_eq!(dst, [1, 2, 3]);
    }
}
```

#### 安全分析

**为什么这些转换是安全的？**

1. **对齐检查**: `from_aligned_ptr` 显式检查指针对齐
2. **大小验证**: 所有操作都验证缓冲区大小是否足够
3. **未对齐处理**: 提供 `read_unaligned` 路径处理未对齐情况
4. **类型安全**: 使用 `PhantomData` 和泛型保持类型信息
5. **内存管理**: `Drop` 实现确保内存正确释放

#### 常见陷阱

```rust
/// ❌ 错误：忽略对齐要求
fn unsafe_transmute(bytes: &[u8]) -> u32 {
    assert!(bytes.len() >= 4);

    unsafe {
        let ptr = bytes.as_ptr() as *const u32;
        *ptr  // ❌ UB: 如果 bytes 未对齐到 4 字节
    }
}

/// ❌ 错误：假设类型布局
fn wrong_transmute<T, U>(value: T) -> U {
    unsafe {
        std::mem::transmute::<T, U>(value)  // ❌ 可能编译失败或产生 UB
    }
}

/// ❌ 错误：未检查大小
fn read_slice_unchecked<T>(ptr: *const T, count: usize) -> &[T] {
    unsafe {
        std::slice::from_raw_parts(ptr, count)  // ❌ 没有验证 count 的有效性
    }
}
```

---

### 模式 3.3: 自定义智能指针

**场景说明**: 实现类似于 `Box<T>`、`Rc<T>` 或 `Arc<T>` 的自定义智能指针，需要管理内存分配、释放，并确保类型安全和线程安全。

#### 正确做法

```rust
use std::alloc::{alloc, dealloc, Layout};
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

/// 自定义智能指针 - 教学用 Box 实现
///
/// 特性：
/// - 堆分配单一值
/// - 独占所有权语义
/// - 自动内存管理
pub struct MyBox<T> {
    ptr: NonNull<T>,
}

/// 为 Send + Sync 类型实现 Send�n///
/// # Safety
/// 只要 T 是 Send，MyBox<T> 就是 Send，因为所有权是独占的
unsafe impl<T: Send> Send for MyBox<T> {}

/// 为 Send + Sync 类型实现 Sync
///
/// # Safety
/// 只要 T 是 Sync，MyBox<T> 就是 Sync，因为不可变访问是安全的
unsafe impl<T: Sync> Sync for MyBox<T> {}

impl<T> MyBox<T> {
    /// 在堆上分配一个新值
    pub fn new(value: T) -> Self {
        let layout = Layout::new::<T>();

        unsafe {
            // 分配内存
            let ptr = alloc(layout) as *mut T;

            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            // 写入值
            ptr.write(value);

            Self {
                ptr: NonNull::new_unchecked(ptr),
            }
        }
    }

    /// 获取原始指针
    pub fn as_ptr(&self) -> *mut T {
        self.ptr.as_ptr()
    }

    /// 消耗 MyBox，返回内部值（不释放内存）
    pub fn into_inner(self) -> T {
        unsafe {
            let value = self.ptr.as_ptr().read();
            // 防止 Drop 运行
            std::mem::forget(self);
            value
        }
    }

    /// 将 MyBox 转换为引用（不消耗所有权）
    ///
    /// # Safety
    /// 返回的引用的生命周期不能超过 MyBox 的生命周期
    pub unsafe fn as_ref_unchecked(&self) -> &T {
        self.ptr.as_ref()
    }
}

impl<T> Deref for MyBox<T> {
    type Target = T;

    fn deref(&self) -> &T {
        // 安全：我们知道指针是有效的，且 Box 保证独占访问
        unsafe { self.ptr.as_ref() }
    }
}

impl<T> DerefMut for MyBox<T> {
    fn deref_mut(&mut self) -> &mut T {
        // 安全：我们知道指针是有效的，且 &mut self 保证独占访问
        unsafe { self.ptr.as_mut() }
    }
}

impl<T> Drop for MyBox<T> {
    fn drop(&mut self) {
        unsafe {
            // 1. 调用析构函数
            self.ptr.as_ptr().drop_in_place();

            // 2. 释放内存
            let layout = Layout::new::<T>();
            dealloc(self.ptr.as_ptr() as *mut u8, layout);
        }
    }
}

/// 实现 From<T> 以便更方便地创建
impl<T> From<T> for MyBox<T> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

/// 自定义引用计数智能指针（简化版 Rc）
pub struct MyRc<T> {
    ptr: NonNull<RcInner<T>>,
}

/// 内部数据，包含引用计数和值
struct RcInner<T> {
    ref_count: std::cell::Cell<usize>,
    value: T,
}

impl<T> MyRc<T> {
    pub fn new(value: T) -> Self {
        let layout = Layout::new::<RcInner<T>>();

        unsafe {
            let ptr = alloc(layout) as *mut RcInner<T>;

            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            // 初始化内部结构
            ptr.write(RcInner {
                ref_count: std::cell::Cell::new(1),
                value,
            });

            Self {
                ptr: NonNull::new_unchecked(ptr),
            }
        }
    }

    /// 获取引用计数
    pub fn strong_count(&self) -> usize {
        unsafe { self.ptr.as_ref().ref_count.get() }
    }

    /// 获取内部值的引用
    fn inner(&self) -> &RcInner<T> {
        unsafe { self.ptr.as_ref() }
    }
}

impl<T> Clone for MyRc<T> {
    fn clone(&self) -> Self {
        // 增加引用计数
        let count = self.inner().ref_count.get();
        self.inner().ref_count.set(count + 1);

        Self { ptr: self.ptr }
    }
}

impl<T> Deref for MyRc<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.inner().value
    }
}

impl<T> Drop for MyRc<T> {
    fn drop(&mut self) {
        let inner = self.inner();
        let count = inner.ref_count.get();

        if count == 1 {
            // 最后一个引用，释放内存
            unsafe {
                let layout = Layout::new::<RcInner<T>>();
                // 先 drop 值
                std::ptr::drop_in_place(&mut (*self.ptr.as_ptr()).value);
                // 释放整个结构
                dealloc(self.ptr.as_ptr() as *mut u8, layout);
            }
        } else {
            // 减少引用计数
            inner.ref_count.set(count - 1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_my_box_basics() {
        let b = MyBox::new(42);
        assert_eq!(*b, 42);
    }

    #[test]
    fn test_my_box_deref_mut() {
        let mut b = MyBox::new(String::from("hello"));
        b.push_str(" world");
        assert_eq!(*b, "hello world");
    }

    #[test]
    fn test_my_box_into_inner() {
        let b = MyBox::new(vec![1, 2, 3]);
        let v = b.into_inner();
        assert_eq!(v, vec![1, 2, 3]);
    }

    #[test]
    fn test_my_box_drop() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        struct DropCounter;
        impl Drop for DropCounter {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }

        {
            let _b = MyBox::new(DropCounter);
        } // Drop 在这里发生

        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn test_my_rc_basics() {
        let rc1 = MyRc::new(42);
        assert_eq!(*rc1, 42);
        assert_eq!(rc1.strong_count(), 1);

        let rc2 = rc1.clone();
        assert_eq!(rc1.strong_count(), 2);
        assert_eq!(rc2.strong_count(), 2);

        drop(rc1);
        assert_eq!(rc2.strong_count(), 1);
    }
}
```

#### 安全分析

**智能指针的安全保证：**

1. **内存分配检查**: 每次 `alloc` 后都检查空指针
2. **正确的 Drop 顺序**: 先调用值析构函数，再释放内存
3. **线程安全标记**: 仅在适当条件下实现 Send 和 Sync
4. **Deref 保证**: 提供安全的解引用体验
5. **所有权管理**: MyBox 独占，MyRc 共享，都有正确的语义

#### Miri 验证

```bash
# 测试内存安全
cargo miri test test_my_box_basics
cargo miri test test_my_box_drop
cargo miri test test_my_rc_basics

# 检查数据竞争（使用多线程测试）
MIRIFLAGS="-Zmiri-disable-isolation" cargo miri test
```

---

### 模式 3.4: 指针别名管理

**场景说明**: 在复杂数据结构中（如链表、图），多个指针可能指向同一内存。需要确保在任何时刻都遵守 Rust 的别名规则（多个可变引用 XOR 一个可变引用）。

#### 正确做法

```rust
use std::ptr::NonNull;

/// 安全的双链表节点（使用原始指针管理别名）
///
/// 设计要点：
/// - 使用原始指针打破引用循环
/// - 在安全的抽象层管理别名规则
pub struct Node<T> {
    data: T,
    next: Option<NonNull<Node<T>>>,
    prev: Option<NonNull<Node<T>>>,
}

impl<T> Node<T> {
    pub fn new(data: T) -> Self {
        Self {
            data,
            next: None,
            prev: None,
        }
    }
}

/// 安全的双向链表
pub struct DoublyLinkedList<T> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
}

impl<T> DoublyLinkedList<T> {
    pub fn new() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
        }
    }

    /// 在尾部添加元素
    pub fn push_back(&mut self, data: T) {
        let new_node = Box::new(Node::new(data));
        let new_node_ptr = unsafe {
            NonNull::new_unchecked(Box::into_raw(new_node))
        };

        match self.tail {
            None => {
                // 空列表
                self.head = Some(new_node_ptr);
                self.tail = Some(new_node_ptr);
            }
            Some(tail_ptr) => {
                // 非空列表，链接到尾部
                unsafe {
                    (*new_node_ptr.as_ptr()).prev = Some(tail_ptr);
                    (*tail_ptr.as_ptr()).next = Some(new_node_ptr);
                }
                self.tail = Some(new_node_ptr);
            }
        }

        self.len += 1;
    }

    /// 从尾部移除元素
    pub fn pop_back(&mut self) -> Option<T> {
        self.tail.map(|tail_ptr| {
            unsafe {
                let tail = Box::from_raw(tail_ptr.as_ptr());

                self.tail = tail.prev;

                match tail.prev {
                    None => self.head = None,
                    Some(prev) => (*prev.as_ptr()).next = None,
                }

                self.len -= 1;
                tail.data
            }
        })
    }

    /// 在头部添加元素
    pub fn push_front(&mut self, data: T) {
        let new_node = Box::new(Node::new(data));
        let new_node_ptr = unsafe {
            NonNull::new_unchecked(Box::into_raw(new_node))
        };

        match self.head {
            None => {
                self.head = Some(new_node_ptr);
                self.tail = Some(new_node_ptr);
            }
            Some(head_ptr) => {
                unsafe {
                    (*new_node_ptr.as_ptr()).next = Some(head_ptr);
                    (*head_ptr.as_ptr()).prev = Some(new_node_ptr);
                }
                self.head = Some(new_node_ptr);
            }
        }

        self.len += 1;
    }

    /// 从头部移除元素
    pub fn pop_front(&mut self) -> Option<T> {
        self.head.map(|head_ptr| {
            unsafe {
                let head = Box::from_raw(head_ptr.as_ptr());

                self.head = head.next;

                match head.next {
                    None => self.tail = None,
                    Some(next) => (*next.as_ptr()).prev = None,
                }

                self.len -= 1;
                head.data
            }
        })
    }

    /// 获取链表长度
    pub fn len(&self) -> usize {
        self.len
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// 迭代器
    pub fn iter(&self) -> Iter<T> {
        Iter {
            current: self.head,
            marker: std::marker::PhantomData,
        }
    }
}

impl<T> Drop for DoublyLinkedList<T> {
    fn drop(&mut self) {
        // 逐个移除所有节点以释放内存
        while self.pop_front().is_some() {}
    }
}

/// 安全的迭代器
pub struct Iter<'a, T> {
    current: Option<NonNull<Node<T>>>,
    marker: std::marker::PhantomData<&'a Node<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.current.map(|node_ptr| {
            unsafe {
                let node = &*node_ptr.as_ptr();
                self.current = node.next;
                &node.data
            }
        })
    }
}

/// 别名安全的内存池（另一种模式）
///
/// 使用索引而非指针来管理别名
pub struct ObjectPool<T> {
    objects: Vec<Option<T>>,
    free_list: Vec<usize>,
}

impl<T> ObjectPool<T> {
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            objects: (0..capacity).map(|_| None).collect(),
            free_list: (0..capacity).collect(),
        }
    }

    /// 分配一个对象，返回索引
    pub fn allocate(&mut self, value: T) -> Option<PoolIndex> {
        self.free_list.pop().map(|index| {
            self.objects[index] = Some(value);
            PoolIndex { index }
        })
    }

    /// 获取引用
    pub fn get(&self, index: PoolIndex) -> Option<&T> {
        self.objects.get(index.index)?.as_ref()
    }

    /// 获取可变引用
    pub fn get_mut(&mut self, index: PoolIndex) -> Option<&mut T> {
        self.objects.get_mut(index.index)?.as_mut()
    }

    /// 释放对象
    pub fn deallocate(&mut self, index: PoolIndex) -> Option<T> {
        if index.index < self.objects.len() {
            let value = self.objects[index.index].take()?;
            self.free_list.push(index.index);
            Some(value)
        } else {
            None
        }
    }
}

/// 池索引类型（防止误用）
#[derive(Debug, Clone, Copy)]
pub struct PoolIndex {
    index: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_doubly_linked_list() {
        let mut list = DoublyLinkedList::new();

        list.push_back(1);
        list.push_back(2);
        list.push_front(0);

        assert_eq!(list.len(), 3);

        let values: Vec<_> = list.iter().copied().collect();
        assert_eq!(values, vec![0, 1, 2]);

        assert_eq!(list.pop_back(), Some(2));
        assert_eq!(list.pop_front(), Some(0));
        assert_eq!(list.pop_front(), Some(1));
        assert_eq!(list.pop_front(), None);
    }

    #[test]
    fn test_object_pool() {
        let mut pool = ObjectPool::<String>::with_capacity(3);

        let idx1 = pool.allocate(String::from("hello")).unwrap();
        let idx2 = pool.allocate(String::from("world")).unwrap();

        assert_eq!(pool.get(idx1).unwrap(), "hello");
        assert_eq!(pool.get(idx2).unwrap(), "world");

        pool.deallocate(idx1);
        let idx3 = pool.allocate(String::from("new")).unwrap();
        // 应该复用 index 0
        assert_eq!(pool.get(idx3).unwrap(), "new");
    }
}
```

#### 安全分析

**别名管理的策略：**

1. **所有权分离**: 使用 `Box::into_raw` 和 `Box::from_raw` 精确控制所有权
2. **非空保证**: 使用 `NonNull` 表示有效的非空指针
3. **生命周期隔离**: 通过 `PhantomData` 在迭代器中维护生命周期关系
4. **索引替代指针**: ObjectPool 使用索引避免直接的指针别名问题
5. **清晰的 Drop 链**: 确保所有分配的内存都被正确释放

---

## 4. Union 模式

Union 允许同一内存位置存储不同类型的值。这在 FFI、性能优化和底层数据处理中非常有用。

### 模式 4.1: 类型双关

**场景说明**: 需要以不同方式解释同一块内存的内容，例如查看浮点数的位表示，或处理网络协议中的变长字段。

#### 正确做法

```rust
/// 安全的类型双关 - 使用 union 替代 transmute
///
/// 优势：
/// - 编译器知道这些类型共享内存
/// - 更清晰、更安全的语义
#[repr(C)]
pub union FloatBits {
    pub float: f32,
    pub int: u32,
    pub bytes: [u8; 4],
}

impl FloatBits {
    /// 从 f32 创建
    pub fn from_float(f: f32) -> Self {
        Self { float: f }
    }

    /// 从 u32 创建
    pub fn from_int(i: u32) -> Self {
        Self { int: i }
    }

    /// 安全地获取整数表示
    pub fn to_bits(self) -> u32 {
        unsafe { self.int }
    }

    /// 安全地获取字节表示
    pub fn to_bytes(self) -> [u8; 4] {
        unsafe { self.bytes }
    }

    /// 安全地获取浮点值
    pub fn to_float(self) -> f32 {
        unsafe { self.float }
    }
}

/// 网络协议中的变长字段示例
#[repr(C, packed)]
pub struct ProtocolHeader {
    pub version: u8,
    pub flags: u8,
    pub length: u16,
    pub payload: PayloadUnion,
}

#[repr(C)]
pub union PayloadUnion {
    /// 小数据模式：直接存储在头部
    pub inline: [u8; 8],
    /// 大数据模式：指向堆内存的指针
    pub external: ExternalPayload,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct ExternalPayload {
    pub ptr: *const u8,
    pub len: usize,
    pub capacity: usize,
}

impl ProtocolHeader {
    /// 创建内联存储的头部
    pub fn new_inline(version: u8, flags: u8, data: &[u8]) -> Option<Self> {
        if data.len() > 8 {
            return None;
        }

        let mut inline = [0u8; 8];
        inline[..data.len()].copy_from_slice(data);

        Some(Self {
            version,
            flags,
            length: data.len() as u16,
            payload: PayloadUnion { inline },
        })
    }

    /// 创建外部存储的头部
    ///
    /// # Safety
    /// - `ptr` 必须指向有效的内存
    /// - 内存必须至少包含 `len` 字节
    pub unsafe fn new_external(
        version: u8,
        flags: u8,
        ptr: *const u8,
        len: usize,
        capacity: usize,
    ) -> Self {
        Self {
            version,
            flags: flags | 0x80,  // 设置外部存储标志
            length: len as u16,
            payload: PayloadUnion {
                external: ExternalPayload {
                    ptr,
                    len,
                    capacity,
                },
            },
        }
    }

    /// 安全地获取数据
    pub fn data(&self) -> &[u8] {
        if self.flags & 0x80 == 0 {
            // 内联模式
            unsafe {
                &self.payload.inline[..self.length as usize]
            }
        } else {
            // 外部模式
            unsafe {
                std::slice::from_raw_parts(
                    self.payload.external.ptr,
                    self.payload.external.len,
                )
            }
        }
    }
}

/// 带标签的 union 包装器（类型安全增强）
#[repr(C)]
pub union TaggedValue {
    pub integer: i64,
    pub float: f64,
    pub boolean: bool,
    pub pointer: *mut (),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ValueType {
    Integer,
    Float,
    Boolean,
    Pointer,
}

/// 安全的 tagged union 包装
pub struct SafeValue {
    ty: ValueType,
    value: TaggedValue,
}

impl SafeValue {
    pub fn from_integer(i: i64) -> Self {
        Self {
            ty: ValueType::Integer,
            value: TaggedValue { integer: i },
        }
    }

    pub fn from_float(f: f64) -> Self {
        Self {
            ty: ValueType::Float,
            value: TaggedValue { float: f },
        }
    }

    pub fn from_boolean(b: bool) -> Self {
        Self {
            ty: ValueType::Boolean,
            value: TaggedValue { boolean: b },
        }
    }

    pub fn get_type(&self) -> ValueType {
        self.ty
    }

    pub fn as_integer(&self) -> Option<i64> {
        if self.ty == ValueType::Integer {
            Some(unsafe { self.value.integer })
        } else {
            None
        }
    }

    pub fn as_float(&self) -> Option<f64> {
        if self.ty == ValueType::Float {
            Some(unsafe { self.value.float })
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_float_bits() {
        let bits = FloatBits::from_float(1.0);
        assert_eq!(bits.to_bits(), 0x3F800000);

        // 往返测试
        let round_trip = FloatBits::from_int(bits.to_bits());
        assert_eq!(round_trip.to_float(), 1.0);
    }

    #[test]
    fn test_inline_header() {
        let data = b"hello";
        let header = ProtocolHeader::new_inline(1, 0, data).unwrap();

        assert_eq!(header.version, 1);
        assert_eq!(header.data(), data.as_slice());
    }

    #[test]
    fn test_safe_value() {
        let v = SafeValue::from_integer(42);
        assert_eq!(v.get_type(), ValueType::Integer);
        assert_eq!(v.as_integer(), Some(42));
        assert_eq!(v.as_float(), None);
    }
}
```

#### 安全分析

**Union 安全使用的关键：**

1. **repr(C)**: 确保可预测的内存布局
2. **类型标签**: `SafeValue` 模式使用显式标签跟踪当前类型
3. **访问模式**: 提供安全的访问方法，在读取时验证类型
4. **正确的 Drop**: 如果 union 包含需要 Drop 的类型，需要手动实现

#### Miri 验证

```bash
cargo miri test test_float_bits
cargo miri test test_inline_header
```

---

### 模式 4.2: 节省内存的数据结构

**场景说明**: 利用 union 在同一位置存储互斥的数据变体，显著减少内存占用。适用于状态机、AST 节点、配置项等场景。

#### 正确做法

```rust
use std::mem::MaybeUninit;

/// 内存高效的 AST 节点
///
/// 使用 union 存储不同的节点类型，节省内存
pub struct AstNode {
    pub kind: NodeKind,
    pub data: NodeData,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NodeKind {
    Integer,
    Float,
    String,
    BinaryOp,
    UnaryOp,
    Identifier,
}

#[repr(C)]
pub union NodeData {
    pub integer: i64,
    pub float: f64,
    pub string: StringData,
    pub binary_op: BinaryOpData,
    pub unary_op: UnaryOpData,
    pub identifier: IdentifierData,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct StringData {
    pub ptr: *const u8,
    pub len: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct BinaryOpData {
    pub op: BinaryOperator,
    pub left: u32,   // 索引到其他节点
    pub right: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct UnaryOpData {
    pub op: UnaryOperator,
    pub operand: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct IdentifierData {
    pub name_idx: u32,  // 索引到符号表
    pub scope: u32,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum UnaryOperator {
    Neg,
    Not,
}

impl AstNode {
    pub fn integer(value: i64) -> Self {
        Self {
            kind: NodeKind::Integer,
            data: NodeData { integer: value },
        }
    }

    pub fn float(value: f64) -> Self {
        Self {
            kind: NodeKind::Float,
            data: NodeData { float: value },
        }
    }

    pub fn binary_op(op: BinaryOperator, left: u32, right: u32) -> Self {
        Self {
            kind: NodeKind::BinaryOp,
            data: NodeData {
                binary_op: BinaryOpData { op, left, right },
            },
        }
    }

    /// 获取整数值（如果类型匹配）
    pub fn as_integer(&self) -> Option<i64> {
        if self.kind == NodeKind::Integer {
            Some(unsafe { self.data.integer })
        } else {
            None
        }
    }

    /// 获取浮点值（如果类型匹配）
    pub fn as_float(&self) -> Option<f64> {
        if self.kind == NodeKind::Float {
            Some(unsafe { self.data.float })
        } else {
            None
        }
    }

    /// 获取二元操作数据（如果类型匹配）
    pub fn as_binary_op(&self) -> Option<(BinaryOperator, u32, u32)> {
        if self.kind == NodeKind::BinaryOp {
            let data = unsafe { self.data.binary_op };
            Some((data.op, data.left, data.right))
        } else {
            None
        }
    }
}

/// 内存池管理器（配合 AST 使用）
pub struct AstPool {
    nodes: Vec<AstNode>,
    strings: Vec<String>,
}

impl AstPool {
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            strings: Vec::new(),
        }
    }

    /// 添加节点，返回索引
    pub fn add_node(&mut self, node: AstNode) -> u32 {
        let idx = self.nodes.len() as u32;
        self.nodes.push(node);
        idx
    }

    /// 添加字符串，返回索引
    pub fn add_string(&mut self, s: String) -> u32 {
        let idx = self.strings.len() as u32;
        self.strings.push(s);
        idx
    }

    /// 获取节点
    pub fn get_node(&self, idx: u32) -> Option<&AstNode> {
        self.nodes.get(idx as usize)
    }

    /// 获取字符串
    pub fn get_string(&self, idx: u32) -> Option<&str> {
        self.strings.get(idx as usize).map(|s| s.as_str())
    }
}

/// 另一种模式：紧凑的配置项存储
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ConfigType {
    Boolean = 0,
    Integer = 1,
    Float = 2,
    String = 3,
}

#[repr(C)]
pub union ConfigValue {
    pub boolean: bool,
    pub integer: i32,
    pub float: f32,
    pub string: [u8; 4],  // 短字符串内联存储
}

/// 8 字节的配置项（紧凑存储）
#[repr(C, packed)]
pub struct ConfigItem {
    pub key_hash: u32,      // 键名的哈希值
    pub ty: ConfigType,     // 值类型（1 字节）
    pub _padding: [u8; 3],  // 对齐填充
    pub value: ConfigValue, // 4 字节的值
}

impl ConfigItem {
    pub fn new_boolean(key_hash: u32, value: bool) -> Self {
        Self {
            key_hash,
            ty: ConfigType::Boolean,
            _padding: [0; 3],
            value: ConfigValue { boolean: value },
        }
    }

    pub fn new_integer(key_hash: u32, value: i32) -> Self {
        Self {
            key_hash,
            ty: ConfigType::Integer,
            _padding: [0; 3],
            value: ConfigValue { integer: value },
        }
    }

    pub fn get_boolean(&self) -> Option<bool> {
        if self.ty == ConfigType::Boolean {
            Some(unsafe { self.value.boolean })
        } else {
            None
        }
    }

    pub fn get_integer(&self) -> Option<i32> {
        if self.ty == ConfigType::Integer {
            Some(unsafe { self.value.integer })
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ast_node() {
        let node = AstNode::integer(42);
        assert_eq!(node.as_integer(), Some(42));
        assert_eq!(node.as_float(), None);

        let float_node = AstNode::float(3.14);
        assert!((float_node.as_float().unwrap() - 3.14).abs() < 0.001);

        let bin_op = AstNode::binary_op(BinaryOperator::Add, 0, 1);
        assert_eq!(bin_op.as_binary_op(), Some((BinaryOperator::Add, 0, 1)));
    }

    #[test]
    fn test_config_item_size() {
        // 验证紧凑布局
        assert_eq!(std::mem::size_of::<ConfigItem>(), 12);
    }

    #[test]
    fn test_config_item() {
        let item = ConfigItem::new_boolean(12345, true);
        assert_eq!(item.get_boolean(), Some(true));
        assert_eq!(item.get_integer(), None);

        let item2 = ConfigItem::new_integer(67890, 42);
        assert_eq!(item2.get_integer(), Some(42));
    }
}
```

#### 安全分析

**内存优化模式的关键点：**

1. **静态大小**: Union 的大小等于最大变体的大小，保证内存可预测
2. **类型标签**: 始终使用外部标签跟踪当前变体类型
3. **安全的访问器**: 所有 union 字段访问都通过类型检查
4. **内存池管理**: 复杂数据（如字符串）存储在外部，union 中只存索引

---

## 5. Transmute 模式

`std::mem::transmute` 是最强大的类型转换工具，也是最危险的。它允许将一个类型的位模式重新解释为另一个类型。

### 模式 5.1: 字节重解释

**场景说明**: 将字节序列转换为结构体，或查看类型的底层位表示。这在序列化、网络协议解析和底层系统编程中很常见。

#### 正确做法

```rust
use std::mem::MaybeUninit;

/// 安全的字节到结构体转换
///
/// 要求：
/// - 结构体必须实现 Copy（没有 Drop）
/// - 结构体必须有确定的内存布局
/// - 字节数组必须足够大
#[repr(C, packed)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct PacketHeader {
    pub magic: u16,
    pub version: u8,
    pub flags: u8,
    pub length: u32,
    pub timestamp: u64,
}

impl PacketHeader {
    /// 结构体大小（常量）
    pub const SIZE: usize = std::mem::size_of::<Self>();

    /// 从字节切片安全转换
    ///
    /// # Safety
    /// - `bytes` 必须至少有 `SIZE` 字节
    /// - 字节必须是有效的结构体位模式
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> Self {
        debug_assert!(bytes.len() >= Self::SIZE);

        // 方法 1: 使用指针转换（推荐用于 packed 结构）
        let ptr = bytes.as_ptr() as *const PacketHeader;
        ptr.read_unaligned()
    }

    /// 安全的转换（带验证）
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() < Self::SIZE {
            return None;
        }

        // 验证魔数
        let magic = u16::from_le_bytes([bytes[0], bytes[1]]);
        if magic != 0x1234 {
            return None;
        }

        Some(unsafe { Self::from_bytes_unchecked(bytes) })
    }

    /// 转换为字节数组
    pub fn to_bytes(&self) -> [u8; Self::SIZE] {
        // 使用标准库的安全方法
        let mut bytes = [0u8; Self::SIZE];

        bytes[0..2].copy_from_slice(&self.magic.to_le_bytes());
        bytes[2] = self.version;
        bytes[3] = self.flags;
        bytes[4..8].copy_from_slice(&self.length.to_le_bytes());
        bytes[8..16].copy_from_slice(&self.timestamp.to_le_bytes());

        bytes
    }

    /// 使用 MaybeUninit 的安全转换（替代 transmute）
    pub fn from_bytes_safe(bytes: &[u8]) -> Option<Self> {
        if bytes.len() < Self::SIZE {
            return None;
        }

        let mut header: MaybeUninit<Self> = MaybeUninit::uninit();

        unsafe {
            let ptr = header.as_mut_ptr() as *mut u8;
            std::ptr::copy_nonoverlapping(
                bytes.as_ptr(),
                ptr,
                Self::SIZE
            );
            Some(header.assume_init())
        }
    }
}

/// 使用标准库 trait 进行序列化（最推荐的方式）
pub trait BytesSerializable: Sized {
    const SIZE: usize;

    fn from_bytes(bytes: &[u8]) -> Option<Self>;
    fn to_bytes(&self) -> Vec<u8>;
}

impl BytesSerializable for PacketHeader {
    const SIZE: usize = 16;

    fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() < Self::SIZE {
            return None;
        }

        Some(Self {
            magic: u16::from_le_bytes([bytes[0], bytes[1]]),
            version: bytes[2],
            flags: bytes[3],
            length: u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]),
            timestamp: u64::from_le_bytes([
                bytes[8], bytes[9], bytes[10], bytes[11],
                bytes[12], bytes[13], bytes[14], bytes[15],
            ]),
        })
    }

    fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(Self::SIZE);
        bytes.extend_from_slice(&self.magic.to_le_bytes());
        bytes.push(self.version);
        bytes.push(self.flags);
        bytes.extend_from_slice(&self.length.to_le_bytes());
        bytes.extend_from_slice(&self.timestamp.to_le_bytes());
        bytes
    }
}

/// 安全的类型转换辅助函数
///
/// 仅适用于相同大小的 POD（Plain Old Data）类型
pub fn safe_transmute<T, U>(value: T) -> Result<U, &'static str>
where
    T: Copy,
    U: Copy,
{
    if std::mem::size_of::<T>() != std::mem::size_of::<U>() {
        return Err("类型大小不匹配");
    }

    if std::mem::align_of::<T>() < std::mem::align_of::<U>() {
        return Err("对齐要求不满足");
    }

    // 使用 transmute_copy 比 transmute 更安全
    Ok(unsafe { std::mem::transmute_copy(&value) })
}

/// 字节序处理函数
pub mod endian {
    /// 大端序 u64 转换
    pub fn read_u64_be(bytes: &[u8]) -> Option<u64> {
        if bytes.len() < 8 {
            return None;
        }

        Some(
            ((bytes[0] as u64) << 56)
            | ((bytes[1] as u64) << 48)
            | ((bytes[2] as u64) << 40)
            | ((bytes[3] as u64) << 32)
            | ((bytes[4] as u64) << 24)
            | ((bytes[5] as u64) << 16)
            | ((bytes[6] as u64) << 8)
            | (bytes[7] as u64)
        )
    }

    /// 小端序 u64 转换
    pub fn read_u64_le(bytes: &[u8]) -> Option<u64> {
        if bytes.len() < 8 {
            return None;
        }

        Some(
            (bytes[0] as u64)
            | ((bytes[1] as u64) << 8)
            | ((bytes[2] as u64) << 16)
            | ((bytes[3] as u64) << 24)
            | ((bytes[4] as u64) << 32)
            | ((bytes[5] as u64) << 40)
            | ((bytes[6] as u64) << 48)
            | ((bytes[7] as u64) << 56)
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_packet_header_roundtrip() {
        let header = PacketHeader {
            magic: 0x1234,
            version: 1,
            flags: 0xFF,
            length: 1024,
            timestamp: 1234567890,
        };

        let bytes = header.to_bytes();
        let recovered = PacketHeader::from_bytes(&bytes).unwrap();

        assert_eq!(header, recovered);
    }

    #[test]
    fn test_invalid_magic() {
        let bytes = vec![0x00, 0x00, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0];
        assert!(PacketHeader::from_bytes(&bytes).is_none());
    }

    #[test]
    fn test_safe_transmute() {
        let x: u32 = 0x12345678;
        let y: [u8; 4] = safe_transmute(x).unwrap();

        // 根据平台字节序验证
        if cfg!(target_endian = "little") {
            assert_eq!(y, [0x78, 0x56, 0x34, 0x12]);
        } else {
            assert_eq!(y, [0x12, 0x34, 0x56, 0x78]);
        }
    }

    #[test]
    fn test_endian_read() {
        let bytes = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08];

        assert_eq!(endian::read_u64_be(&bytes), Some(0x0102030405060708));
        assert_eq!(endian::read_u64_le(&bytes), Some(0x0807060504030201));
    }
}
```

#### 安全分析

**安全的字节转换策略：**

1. **repr(C, packed)**: 确保可预测的内存布局
2. **显式字节序处理**: 使用 `to_le_bytes` / `from_le_bytes`
3. **大小验证**: 转换前总是检查缓冲区大小
4. **MaybeUninit**: 避免未初始化内存的 UB
5. **transmute_copy 优于 transmute**: 不会移动值，更安全

---

### 模式 5.2: 类型擦除

**场景说明**: 在需要存储不同类型但统一处理的场景中，使用类型擦除隐藏具体类型信息，同时保持类型安全。

#### 正确做法

```rust
use std::any::{Any, TypeId};
use std::ptr::NonNull;

/// 安全的类型擦除容器
///
/// 设计要点：
/// - 存储类型ID用于运行时类型检查
/// - 使用虚函数表（vtable）实现多态行为
pub struct TypeErased {
    data: NonNull<u8>,
    vtable: &'static VTable,
}

/// 虚函数表
struct VTable {
    type_id: TypeId,
    type_name: &'static str,
    drop: unsafe fn(*mut u8),
    clone: unsafe fn(*const u8) -> TypeErased,
}

impl TypeErased {
    /// 从具体类型创建
    pub fn new<T: 'static>(value: T) -> Self
    where
        T: Clone,
    {
        // 在堆上分配
        let layout = std::alloc::Layout::new::<T>();
        let ptr = unsafe { std::alloc::alloc(layout) };

        if ptr.is_null() {
            std::alloc::handle_alloc_error(layout);
        }

        // 写入值
        unsafe {
            (ptr as *mut T).write(value);
        }

        Self {
            data: unsafe { NonNull::new_unchecked(ptr) },
            vtable: &VTable {
                type_id: TypeId::of::<T>(),
                type_name: std::any::type_name::<T>(),
                drop: |ptr| unsafe {
                    std::ptr::drop_in_place(ptr as *mut T);
                    std::alloc::dealloc(ptr, layout);
                },
                clone: |ptr| unsafe {
                    let value = (ptr as *const T).read();
                    TypeErased::new(value)
                },
            },
        }
    }

    /// 检查类型
    pub fn is<T: 'static>(&self) -> bool {
        self.vtable.type_id == TypeId::of::<T>()
    }

    /// 安全地下转换
    pub fn downcast_ref<T: 'static>(&self) -> Option<&T> {
        if self.is::<T>() {
            Some(unsafe { &*(self.data.as_ptr() as *const T) })
        } else {
            None
        }
    }

    /// 安全地下转换为可变引用
    pub fn downcast_mut<T: 'static>(&mut self) -> Option<&mut T> {
        if self.is::<T>() {
            Some(unsafe { &mut *(self.data.as_ptr() as *mut T) })
        } else {
            None
        }
    }

    /// 克隆（使用 vtable）
    pub fn clone(&self) -> Self {
        unsafe {
            (self.vtable.clone)(self.data.as_ptr())
        }
    }

    /// 获取类型名称
    pub fn type_name(&self) -> &'static str {
        self.vtable.type_name
    }
}

impl Drop for TypeErased {
    fn drop(&mut self) {
        unsafe {
            (self.vtable.drop)(self.data.as_ptr());
        }
    }
}

/// 使用示例：异构集合
pub struct HeterogeneousVec {
    items: Vec<TypeErased>,
}

impl HeterogeneousVec {
    pub fn new() -> Self {
        Self { items: Vec::new() }
    }

    pub fn push<T: 'static>(&mut self, value: T)
    where
        T: Clone,
    {
        self.items.push(TypeErased::new(value));
    }

    pub fn get<T: 'static>(&self, index: usize) -> Option<&T> {
        self.items.get(index)?.downcast_ref::<T>()
    }

    pub fn iter(&self) -> impl Iterator<Item = &TypeErased> {
        self.items.iter()
    }
}

/// 另一种模式：函数指针类型擦除
///
/// 用于存储不同签名的回调函数
pub type ErasedCallback = Box<dyn Fn(&dyn Any) -> Box<dyn Any>>;

/// 类型安全的回调包装
pub struct TypedCallback<Input, Output> {
    f: Box<dyn Fn(Input) -> Output>,
}

impl<Input: 'static, Output: 'static> TypedCallback<Input, Output> {
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(Input) -> Output + 'static,
    {
        Self { f: Box::new(f) }
    }

    /// 擦除类型，转换为通用回调
    pub fn erase(self) -> ErasedCallback {
        Box::new(move |input: &dyn Any| -> Box<dyn Any> {
            let input = input.downcast_ref::<Input>()
                .expect("类型不匹配");
            Box::new((self.f)(*input))
        })
    }
}

/// 使用标准库 Any trait 的简单类型擦除
pub struct SimpleTypeErased {
    inner: Box<dyn Any>,
}

impl SimpleTypeErased {
    pub fn new<T: 'static>(value: T) -> Self {
        Self { inner: Box::new(value) }
    }

    pub fn downcast_ref<T: 'static>(&self) -> Option<&T> {
        self.inner.downcast_ref::<T>()
    }

    pub fn downcast_mut<T: 'static>(&mut self) -> Option<&mut T> {
        self.inner.downcast_mut::<T>()
    }

    pub fn downcast<T: 'static>(self) -> Result<T, Self> {
        match self.inner.downcast::<T>() {
            Ok(boxed) => Ok(*boxed),
            Err(inner) => Err(Self { inner }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_erased() {
        let erased = TypeErased::new(42i32);

        assert!(erased.is::<i32>());
        assert!(!erased.is::<i64>());
        assert_eq!(erased.downcast_ref::<i32>(), Some(&42));
        assert_eq!(erased.downcast_ref::<i64>(), None);
    }

    #[test]
    fn test_heterogeneous_vec() {
        let mut vec = HeterogeneousVec::new();
        vec.push(42i32);
        vec.push("hello".to_string());
        vec.push(3.14f64);

        assert_eq!(vec.get::<i32>(0), Some(&42));
        assert_eq!(vec.get::<String>(1), Some(&"hello".to_string()));
        assert_eq!(vec.get::<f64>(2), Some(&3.14));
    }

    #[test]
    fn test_simple_type_erased() {
        let erased = SimpleTypeErased::new(vec![1, 2, 3]);

        assert_eq!(erased.downcast_ref::<Vec<i32>>(), Some(&vec![1, 2, 3]));

        let vec = erased.downcast::<Vec<i32>>().unwrap();
        assert_eq!(vec, vec![1, 2, 3]);
    }
}
```

#### 安全分析

**类型擦除的安全保证：**

1. **运行时类型检查**: 使用 `TypeId` 确保类型安全
2. **正确的 Drop**: VTable 确保任何类型都能正确释放
3. **类型一致性**: 一旦创建，内部类型不会改变
4. **Any trait 备选**: 标准库的 `Any` trait 提供简单但安全的类型擦除

---

## 6. FFI 边界模式

Foreign Function Interface (FFI) 允许 Rust 与其他语言（主要是 C）交互。这是 unsafe Rust 最常见的使用场景之一。

### 模式 6.1: 回调函数

**场景说明**: Rust 代码需要将函数指针传递给 C 库作为回调，或从 C 库接收回调。

#### 正确做法

```rust
use std::ffi::{c_char, c_int, c_void, CStr, CString};
use std::panic::catch_unwind;

/// C 库回调函数类型
pub type CCallback = extern "C" fn(data: *const c_char, len: c_int, user_data: *mut c_void);

/// 安全的 Rust 回调包装
///
/// 关键安全措施：
/// 1. 捕获 panic 防止跨 FFI 边界展开
/// 2. 验证 C 字符串的有效性
/// 3. 正确管理用户数据生命周期
pub struct RustCallback<F> {
    callback: F,
}

impl<F> RustCallback<F>
where
    F: FnMut(&str),
{
    pub fn new(callback: F) -> Self {
        Self { callback }
    }

    /// 生成 C 兼容的回调函数
    ///
    /// # Safety
    /// - 返回的函数指针只能与有效的 RustCallback 一起使用
    /// - 必须确保 callback 的生命周期足够长
    pub unsafe fn as_c_callback(&mut self) -> CCallback {
        // 闭包转换为函数指针
        extern "C" fn trampoline<F>(
            data: *const c_char,
            len: c_int,
            user_data: *mut c_void,
        )
        where
            F: FnMut(&str),
        {
            // 捕获 panic，防止跨 FFI 边界
            let result = catch_unwind(|| {
                // 验证指针非空
                if data.is_null() || len < 0 {
                    return;
                }

                // 安全地创建切片
                let slice = std::slice::from_raw_parts(
                    data as *const u8,
                    len as usize
                );

                // 转换为字符串（验证 UTF-8）
                if let Ok(s) = std::str::from_utf8(slice) {
                    // 恢复闭包引用
                    let callback = &mut *(user_data as *mut F);
                    (callback)(s);
                }
            });

            // 记录 panic（如果发生）
            if result.is_err() {
                eprintln!("Callback panicked!");
            }
        }

        // 将闭包指针作为 user_data
        std::mem::transmute::<
            extern "C" fn(*const c_char, c_int, *mut c_void),
            CCallback,
        >(trampoline::<F>)
    }

    /// 获取 user_data 指针
    pub fn as_user_data(&mut self) -> *mut c_void {
        &mut self.callback as *mut F as *mut c_void
    }
}

/// 更简单的回调模式：使用全局状态（适用于简单场景）
pub mod global_callback {
    use super::*;
    use std::sync::Mutex;

    /// 回调函数类型
    type CallbackFn = Box<dyn Fn(&str) + Send>;

    /// 全局回调存储
    static CALLBACK: Mutex<Option<CallbackFn>> = Mutex::new(None);

    /// 注册回调
    pub fn set_callback<F>(f: F)
    where
        F: Fn(&str) + Send + 'static,
    {
        let mut guard = CALLBACK.lock().unwrap();
        *guard = Some(Box::new(f));
    }

    /// C 兼容的回调函数
    ///
    /// # Safety
    /// 必须由 C 代码在有效上下文中调用
    pub unsafe extern "C" fn c_callback(
        data: *const c_char,
        len: c_int,
    ) {
        // 忽略空指针
        if data.is_null() || len <= 0 {
            return;
        }

        let slice = std::slice::from_raw_parts(
            data as *const u8,
            len as usize
        );

        if let Ok(s) = std::str::from_utf8(slice) {
            if let Ok(guard) = CALLBACK.lock() {
                if let Some(ref callback) = *guard {
                    callback(s);
                }
            }
        }
    }
}

/// 模拟 C 库接口
pub mod c_library {
    use super::*;

    /// 模拟的 C 库函数
    ///
    /// 在实际项目中，这是 C 库的声明：
    /// extern "C" {
    ///     fn register_callback(cb: CCallback, user_data: *mut c_void);
    /// }
    pub fn simulate_c_call(callback: CCallback, user_data: *mut c_void) {
        let data = CString::new("Hello from C!").unwrap();
        callback(data.as_ptr(), data.as_bytes().len() as c_int, user_data);
    }
}

/// 使用示例
pub fn example_usage() {
    let mut received = String::new();

    {
        let mut callback = RustCallback::new(|s: &str| {
            received.push_str(s);
            println!("Received: {}", s);
        });

        unsafe {
            c_library::simulate_c_call(
                callback.as_c_callback(),
                callback.as_user_data(),
            );
        }
    }

    assert_eq!(received, "Hello from C!");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_callback() {
        let mut called = false;
        let mut received = String::new();

        {
            let mut callback = RustCallback::new(|s: &str| {
                called = true;
                received = s.to_string();
            });

            unsafe {
                c_library::simulate_c_call(
                    callback.as_c_callback(),
                    callback.as_user_data(),
                );
            }
        }

        assert!(called);
        assert_eq!(received, "Hello from C!");
    }

    #[test]
    fn test_global_callback() {
        use global_callback::*;

        let received = std::sync::Arc::new(std::sync::Mutex::new(String::new()));
        let received_clone = received.clone();

        set_callback(move |s: &str| {
            received_clone.lock().unwrap().push_str(s);
        });

        unsafe {
            let data = CString::new("Test").unwrap();
            c_callback(data.as_ptr(), data.as_bytes().len() as c_int);
        }

        assert_eq!(received.lock().unwrap().as_str(), "Test");
    }
}
```

#### 安全分析

**回调函数的关键安全措施：**

1. **Panic 捕获**: `catch_unwind` 防止 Rust panic 传播到 C 代码
2. **空指针检查**: 始终验证 C 传入的指针
3. **边界验证**: 检查长度参数，防止缓冲区溢出
4. **UTF-8 验证**: 将字节转换为字符串时验证编码
5. **生命周期管理**: 确保 Rust 闭包比 C 调用存活更久

---

### 模式 6.2: 不透明指针

**场景说明**: C 库经常使用 "不透明指针" 模式（opaque pointers），即只暴露指针类型而隐藏具体结构定义。Rust 需要安全地包装这种模式。

#### 正确做法

```rust
use std::ffi::{c_char, c_void, CStr, CString};
use std::ptr::NonNull;

/// 模拟 C 库的不透明类型
///
/// 在真实场景中，这是 C 头文件中的：
/// typedef struct MyHandle MyHandle;
#[repr(C)]
pub struct COpaqueHandle {
    _private: [u8; 0],  // 零大小数组，防止直接构造
}

/// C 库函数（模拟）
extern "C" {
    fn mylib_create_handle(name: *const c_char) -> *mut COpaqueHandle;
    fn mylib_destroy_handle(handle: *mut COpaqueHandle);
    fn mylib_do_work(handle: *mut COpaqueHandle, data: c_int) -> c_int;
    fn mylib_get_status(handle: *const COpaqueHandle) -> c_int;
}

/// 安全的 Rust 包装器
///
/// 使用 RAII 模式确保资源释放
pub struct Handle {
    ptr: NonNull<COpaqueHandle>,
}

/// 确保线程安全（根据 C 库的线程安全性）
unsafe impl Send for Handle {}
unsafe impl Sync for Handle {}

impl Handle {
    /// 创建新句柄
    pub fn new(name: &str) -> Option<Self> {
        let c_name = CString::new(name).ok()?;

        let ptr = unsafe { mylib_create_handle(c_name.as_ptr()) };

        NonNull::new(ptr).map(|ptr| Self { ptr })
    }

    /// 执行操作
    pub fn do_work(&mut self, data: i32) -> i32 {
        unsafe {
            mylib_do_work(self.ptr.as_ptr(), data)
        }
    }

    /// 获取状态
    pub fn status(&self) -> i32 {
        unsafe {
            mylib_get_status(self.ptr.as_ptr())
        }
    }

    /// 获取原始指针（用于高级用法）
    ///
    /// # Safety
    /// - 返回的指针在 Handle 存活期间有效
    /// - 不要调用会消耗句柄的 C 函数
    pub unsafe fn as_raw(&self) -> *mut COpaqueHandle {
        self.ptr.as_ptr()
    }
}

impl Drop for Handle {
    fn drop(&mut self) {
        unsafe {
            mylib_destroy_handle(self.ptr.as_ptr());
        }
    }
}

/// 另一种模式：支持自定义 Drop 的泛型包装
pub struct OpaquePtr<T: OpaqueType> {
    ptr: NonNull<T>,
}

/// Opaque 类型 trait
pub unsafe trait OpaqueType: Sized {
    /// 创建函数
    unsafe fn create() -> *mut Self;
    /// 销毁函数
    unsafe fn destroy(ptr: *mut Self);
}

impl<T: OpaqueType> OpaquePtr<T> {
    pub fn new() -> Option<Self> {
        let ptr = unsafe { T::create() };
        NonNull::new(ptr).map(|ptr| Self { ptr })
    }

    pub fn as_ptr(&self) -> *mut T {
        self.ptr.as_ptr()
    }
}

impl<T: OpaqueType> Drop for OpaquePtr<T> {
    fn drop(&mut self) {
        unsafe {
            T::destroy(self.ptr.as_ptr());
        }
    }
}

// 示例实现
pub struct MyContext;

unsafe impl OpaqueType for MyContext {
    unsafe fn create() -> *mut Self {
        // 模拟创建
        std::ptr::null_mut()
    }

    unsafe fn destroy(_ptr: *mut Self) {
        // 模拟销毁
    }
}

/// C 库模拟实现（仅用于测试）
#[cfg(test)]
mod c_impl {
    use super::*;
    use std::sync::Mutex;

    lazy_static::lazy_static! {
        static ref HANDLES: Mutex<Vec<String>> = Mutex::new(Vec::new());
    }

    #[no_mangle]
    pub extern "C" fn mylib_create_handle(name: *const c_char) -> *mut COpaqueHandle {
        if name.is_null() {
            return std::ptr::null_mut();
        }

        let name = unsafe { CStr::from_ptr(name) }
            .to_string_lossy()
            .into_owned();

        let mut handles = HANDLES.lock().unwrap();
        handles.push(name);

        // 返回一个伪造的指针（实际上是索引 + 1）
        (handles.len()) as *mut COpaqueHandle
    }

    #[no_mangle]
    pub extern "C" fn mylib_destroy_handle(handle: *mut COpaqueHandle) {
        if !handle.is_null() {
            let idx = handle as usize - 1;
            let mut handles = HANDLES.lock().unwrap();
            if idx < handles.len() {
                handles[idx].clear();
            }
        }
    }

    #[no_mangle]
    pub extern "C" fn mylib_do_work(_handle: *mut COpaqueHandle, data: c_int) -> c_int {
        data * 2
    }

    #[no_mangle]
    pub extern "C" fn mylib_get_status(_handle: *const COpaqueHandle) -> c_int {
        0  // OK
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_handle() {
        let handle = Handle::new("test").expect("Failed to create handle");

        let status = handle.status();
        assert_eq!(status, 0);

        // handle 在这里自动 drop
    }

    #[test]
    fn test_do_work() {
        let mut handle = Handle::new("work_test").unwrap();
        let result = handle.do_work(21);
        assert_eq!(result, 42);
    }
}
```

#### 安全分析

**不透明指针的安全策略：**

1. **NonNull 保证**: 使用 `NonNull` 确保指针永远不会为空
2. **RAII 管理**: Drop 实现确保资源释放
3. **线程安全标记**: 根据 C 库特性标记 Send/Sync
4. **生命周期隔离**: Rust 包装器的生命周期管理 C 指针的有效性

---

### 模式 6.3: 字符串传递

**场景说明**: Rust 的 UTF-8 字符串与 C 的以 null 结尾的字节字符串之间的转换是 FFI 中最常见的操作之一，需要特别注意编码和生命周期。

#### 正确做法

```rust
use std::ffi::{c_char, CStr, CString, OsStr, OsString};
use std::path::{Path, PathBuf};

/// 安全的 C 字符串借用
///
/// 封装 CStr 提供更友好的 API
pub struct CStrRef<'a> {
    inner: &'a CStr,
}

impl<'a> CStrRef<'a> {
    /// 从原始指针创建
    ///
    /// # Safety
    /// - `ptr` 必须指向有效的以 null 结尾的 C 字符串
    /// - 字符串必须至少存活 'a 生命周期
    pub unsafe fn from_ptr(ptr: *const c_char) -> Option<Self> {
        if ptr.is_null() {
            return None;
        }

        Some(Self {
            inner: CStr::from_ptr(ptr),
        })
    }

    /// 转换为 Rust 字符串（如果有效 UTF-8）
    pub fn to_str(&self) -> Option<&str> {
        self.inner.to_str().ok()
    }

    /// 转换为字符串（允许替换无效字符）
    pub fn to_string_lossy(&self) -> std::borrow::Cow<'a, str> {
        self.inner.to_string_lossy()
    }

    /// 获取原始指针
    pub fn as_ptr(&self) -> *const c_char {
        self.inner.as_ptr()
    }
}

/// 安全的 C 字符串拥有者
pub struct CStrBuf {
    inner: CString,
}

impl CStrBuf {
    pub fn new(s: &str) -> Option<Self> {
        CString::new(s).ok().map(|inner| Self { inner })
    }

    pub fn from_os_str(s: &OsStr) -> Option<Self> {
        use std::os::unix::ffi::OsStrExt;
        CString::new(s.as_bytes()).ok().map(|inner| Self { inner })
    }

    pub fn as_ptr(&self) -> *const c_char {
        self.inner.as_ptr()
    }
}

/// 字符串传递模式
pub mod string_patterns {
    use super::*;

    /// 模式 1: Rust → C，传递静态字符串
    ///
    /// 适用于：C 只读取，不保存指针
    pub fn pass_static(s: &str) -> Option<CStrBuf> {
        CStrBuf::new(s)
    }

    /// 模式 2: Rust → C，传递并允许 C 保存
    ///
    /// 适用于：C 需要长期保存指针
    pub fn pass_owned(s: String) -> *mut c_char {
        match CString::new(s) {
            Ok(cstr) => cstr.into_raw(),  // 转移所有权到 C
            Err(_) => std::ptr::null_mut(),
        }
    }

    /// 模式 3: C → Rust，借用
    ///
    /// 适用于：C 临时提供字符串
    pub fn receive_borrowed<'a>(ptr: *const c_char) -> Option<&'a str> {
        unsafe {
            CStrRef::from_ptr(ptr)?.to_str()
        }
    }

    /// 模式 4: C → Rust，复制
    ///
    /// 适用于：需要长期保存 C 的字符串
    pub fn receive_copied(ptr: *const c_char) -> Option<String> {
        unsafe {
            CStrRef::from_ptr(ptr).map(|s| s.to_string_lossy().into_owned())
        }
    }

    /// 模式 5: C 释放 Rust 分配的字符串
    ///
    /// # Safety
    /// - `ptr` 必须是由 `pass_owned` 返回的指针
    /// - 只能调用一次
    pub unsafe fn free_string(ptr: *mut c_char) {
        if !ptr.is_null() {
            let _ = CString::from_raw(ptr);  // 重新获取所有权并 drop
        }
    }
}

/// 路径处理（跨平台 FFI）
pub struct FfiPath {
    inner: CString,
}

impl FfiPath {
    /// 从 Path 创建（Unix）
    #[cfg(unix)]
    pub fn new(path: &Path) -> Option<Self> {
        use std::os::unix::ffi::OsStrExt;
        let bytes = path.as_os_str().as_bytes();
        CString::new(bytes).ok().map(|inner| Self { inner })
    }

    /// 从 Path 创建（Windows）
    #[cfg(windows)]
    pub fn new(path: &Path) -> Option<Self> {
        // Windows 需要特殊处理宽字符
        let utf8 = path.to_str()?;
        CString::new(utf8).ok().map(|inner| Self { inner })
    }

    pub fn as_ptr(&self) -> *const c_char {
        self.inner.as_ptr()
    }
}

/// 批量字符串传递
pub struct StringList {
    strings: Vec<CString>,
    ptrs: Vec<*const c_char>,
}

impl StringList {
    pub fn new(strs: &[&str]) -> Option<Self> {
        let strings: Vec<CString> = strs
            .iter()
            .map(|&s| CString::new(s).ok())
            .collect::<Option<_>>()?;

        let ptrs: Vec<*const c_char> = strings
            .iter()
            .map(|s| s.as_ptr())
            .collect();

        Some(Self { strings, ptrs })
    }

    pub fn as_ptr(&self) -> *const *const c_char {
        self.ptrs.as_ptr()
    }

    pub fn len(&self) -> usize {
        self.ptrs.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::string_patterns::*;

    #[test]
    fn test_cstr_ref() {
        let cstr = CString::new("hello").unwrap();
        let ref_cstr = unsafe { CStrRef::from_ptr(cstr.as_ptr()) }.unwrap();

        assert_eq!(ref_cstr.to_str(), Some("hello"));
    }

    #[test]
    fn test_pass_and_receive() {
        let original = "Test String";
        let cstr = pass_static(original).unwrap();

        let recovered = receive_borrowed(cstr.as_ptr()).unwrap();
        assert_eq!(recovered, original);
    }

    #[test]
    fn test_owned_roundtrip() {
        let original = String::from("Owned String");

        // 传递给 C
        let ptr = pass_owned(original);
        assert!(!ptr.is_null());

        // 从 C 接收
        let received = receive_copied(ptr).unwrap();
        assert_eq!(received, "Owned String");

        // 释放
        unsafe { free_string(ptr); }
    }

    #[test]
    fn test_string_list() {
        let list = StringList::new(&["one", "two", "three"]).unwrap();
        assert_eq!(list.len(), 3);
        assert!(!list.as_ptr().is_null());
    }
}
```

#### 安全分析

**字符串传递的关键点：**

1. **所有权明确**: 区分借用（`&CStr`）和拥有（`CString`）
2. **编码验证**: 始终验证 UTF-8，或使用 `to_string_lossy`
3. **空指针检查**: 接收 C 字符串时首先检查 null
4. **生命周期管理**: 确保 Rust 拥有的字符串在 C 使用期间保持有效

---

## 7. Miri 使用指南

Miri（Mid-level IR Interpreter）是 Rust 的官方解释器，用于检测程序中的未定义行为。它是验证 unsafe 代码安全性的重要工具。

### 7.1 安装与配置

```bash
# 安装 Miri
rustup component add miri

# 验证安装
cargo miri --version
```

### 7.2 基本用法

```bash
# 运行程序
cargo miri run

# 运行测试
cargo miri test

# 运行特定测试
cargo miri test test_name

# 带环境变量
MIRIFLAGS="-Zmiri-disable-isolation" cargo miri test
```

### 7.3 常见错误检测

| 错误类型 | 示例 | Miri 输出 |
|----------|------|-----------|
| **未初始化内存** | `let x: i32; println!("{}", x);` | "use of uninitialized data" |
| **悬垂指针** | 使用已释放的指针 | "dereferenced after this allocation got freed" |
| **数据竞争** | 多线程无同步访问 | "data race detected" |
| **违反别名规则** | 同时存在可变引用 | "no item granting read access... in the borrow stack" |
| **对齐违规** | 未对齐的指针解引用 | "must be aligned to X bytes" |
| **越界访问** | 数组/切片越界 | "out-of-bounds pointer arithmetic" |

### 7.4 CI 集成

```yaml
# .github/workflows/miri.yml
name: Miri

on: [push, pull_request]

jobs:
  miri:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-action@stable
        with:
          components: miri

      - name: Run Miri tests
        run: cargo miri test

      - name: Run Miri tests (Tree Borrows)
        run: MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test
```

---

## 8. 安全审查清单

### 8.1 代码审查要点

- [ ] **边界检查**: 所有指针访问前都有边界验证
- [ ] **空指针检查**: 解引用前验证指针非 null
- [ ] **对齐验证**: 确保指针正确对齐，或使用 `read_unaligned`
- [ ] **生命周期管理**: 确保引用不会比被引用对象存活更久
- [ ] **Drop 安全性**: 正确实现 Drop，防止内存泄漏和 double-free
- [ ] **Send/Sync 正确性**: 仅在类型真正安全时实现这些 trait

### 8.2 文档化要求

每个 unsafe 函数必须包含：

```rust
/// 函数描述
///
/// # Safety
/// - 前置条件 1
/// - 前置条件 2
///
/// # Examples
/// ```
/// // 安全使用示例
/// ```
unsafe fn dangerous_function(ptr: *const i32) -> i32 {
    *ptr
}
```

### 8.3 测试策略

```rust
#[cfg(test)]
mod unsafe_tests {
    use super::*;

    #[test]
    fn test_normal_case() {
        // 测试正常路径
    }

    #[test]
    fn test_edge_cases() {
        // 测试边界条件
    }

    #[test]
    #[should_panic(expected = "...")]
    fn test_invalid_input() {
        // 测试错误输入
    }
}
```

---

## 9. 参考与资源

### 官方文档

- [The Rustonomicon](https://doc.rust-lang.org/nomicon/) - Unsafe Rust 权威指南
- [Rust Reference - Unsafe](https://doc.rust-lang.org/reference/unsafe-keyword.html)
- [std::ptr 文档](https://doc.rust-lang.org/std/ptr/)
- [Miri GitHub](https://github.com/rust-lang/miri)

### 项目内相关文档

- [UNSAFE_RUST_GUIDE.md](./UNSAFE_RUST_GUIDE.md) - 专题指南
- [FFI_PRACTICAL_GUIDE.md](./FFI_PRACTICAL_GUIDE.md) - FFI 实践指南
- [INLINE_ASSEMBLY_GUIDE.md](./INLINE_ASSEMBLY_GUIDE.md) - 内联汇编指南

### 学术资源

- [Stacked Borrows 论文](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)
- [Tree Borrows 文档](https://github.com/Vanille-N/tree-borrows)
- [RustBelt 项目](https://plv.mpi-sws.org/rustbelt/)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-17
**版本**: 1.0.0
