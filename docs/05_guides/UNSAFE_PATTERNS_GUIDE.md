# Unsafe Rust 模式指南

> **危险等级**: 🔴 高级主题 - 使用不当将导致未定义行为 (UB)
> **目标读者**: 已掌握 Safe Rust，需要编写/审计 unsafe 代码的开发者
> **参考标准**: [Rustonomicon](https://doc.rust-lang.org/nomicon/), [Rust Reference](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)

---

## 📋 目录

- [Unsafe Rust 模式指南](#unsafe-rust-模式指南)
  - [📋 目录](#-目录)
  - [1. 概述与 Miri 验证](#1-概述与-miri-验证)
    - [1.1 什么是 Miri](#11-什么是-miri)
    - [1.2 安装 Miri](#12-安装-miri)
    - [1.3 常用 Miri 命令](#13-常用-miri-命令)
    - [1.4 Miri 输出解读](#14-miri-输出解读)
    - [1.5 Stacked Borrows vs Tree Borrows](#15-stacked-borrows-vs-tree-borrows)
  - [2. 原始指针操作模式](#2-原始指针操作模式)
    - [2.1 问题场景](#21-问题场景)
    - [2.2 代码示例：堆分配和裸指针解引用](#22-代码示例堆分配和裸指针解引用)
    - [2.3 安全契约](#23-安全契约)
    - [2.4 Miri 验证](#24-miri-验证)
    - [2.5 常见错误：UB 示例和修复](#25-常见错误ub-示例和修复)
    - [2.6 替代方案](#26-替代方案)
    - [2.7 生产案例](#27-生产案例)
  - [3. 自引用结构体](#3-自引用结构体)
    - [3.1 问题场景](#31-问题场景)
    - [3.2 代码示例：Pin 和堆分配自引用](#32-代码示例pin-和堆分配自引用)
    - [3.3 栈上自引用（危险模式）](#33-栈上自引用危险模式)
    - [3.4 安全契约](#34-安全契约)
    - [3.5 替代方案](#35-替代方案)
    - [3.6 生产案例](#36-生产案例)
  - [4. 自定义 Drop 和内存管理](#4-自定义-drop-和内存管理)
    - [4.1 问题场景](#41-问题场景)
    - [4.2 代码示例：与 C 内存交互](#42-代码示例与-c-内存交互)
    - [4.3 Drop 检查绕过](#43-drop-检查绕过)
    - [4.4 生产案例](#44-生产案例)
  - [5. Union 访问](#5-union-访问)
    - [5.1 问题场景](#51-问题场景)
    - [5.2 代码示例：Union 安全访问](#52-代码示例union-安全访问)
    - [5.3 常见错误](#53-常见错误)
    - [5.4 生产案例](#54-生产案例)
  - [6. FFI 边界处理](#6-ffi-边界处理)
    - [6.1 问题场景](#61-问题场景)
    - [6.2 代码示例：完整 FFI 边界](#62-代码示例完整-ffi-边界)
    - [6.3 FFI 安全契约](#63-ffi-安全契约)
    - [6.4 生产案例](#64-生产案例)
  - [7. SIMD 和矢量化](#7-simd-和矢量化)
    - [7.1 问题场景](#71-问题场景)
    - [7.2 代码示例：SIMD 安全包装](#72-代码示例simd-安全包装)
    - [7.3 常见错误](#73-常见错误)
    - [7.4 生产案例](#74-生产案例)
  - [8. 并发原语实现](#8-并发原语实现)
    - [8.1 问题场景](#81-问题场景)
    - [8.2 代码示例：自定义自旋锁](#82-代码示例自定义自旋锁)
    - [8.3 内存序选择指南](#83-内存序选择指南)
    - [8.4 生产案例](#84-生产案例)
  - [9. 未初始化内存](#9-未初始化内存)
    - [9.1 问题场景](#91-问题场景)
    - [9.2 代码示例：MaybeUninit 模式](#92-代码示例maybeuninit-模式)
    - [9.3 MaybeUninit 方法选择指南](#93-maybeuninit-方法选择指南)
    - [9.4 生产案例](#94-生产案例)
  - [10. 静态可变状态](#10-静态可变状态)
    - [10.1 问题场景](#101-问题场景)
    - [10.2 代码示例：安全初始化模式](#102-代码示例安全初始化模式)
    - [10.3 初始化模式对比](#103-初始化模式对比)
    - [10.4 生产案例](#104-生产案例)
  - [11. 契约和不变式](#11-契约和不变式)
    - [11.1 问题场景](#111-问题场景)
    - [11.2 代码示例：契约验证模式](#112-代码示例契约验证模式)
    - [11.3 契约文档模板](#113-契约文档模板)
    - [11.4 生产案例](#114-生产案例)
  - [12. UB 分类速查表](#12-ub-分类速查表)
    - [12.1 未定义行为分类](#121-未定义行为分类)
    - [12.2 Miri 错误解读](#122-miri-错误解读)
    - [12.3 调试技巧](#123-调试技巧)
  - [13. Rustonomicon 章节映射](#13-rustonomicon-章节映射)
  - [附录：Miri 完整配置](#附录miri-完整配置)
    - [`.cargo/config.toml` 示例](#cargoconfigtoml-示例)
    - [GitHub Actions 配置](#github-actions-配置)
  - [总结](#总结)
    - [危险等级总结](#危险等级总结)

---

## 1. 概述与 Miri 验证

### 1.1 什么是 Miri

Miri 是 Rust 的解释器，用于检测未定义行为。它执行 Rust 中间表示 (MIR) 并检查所有 unsafe 操作的安全性。

### 1.2 安装 Miri

```bash
# 安装 Miri
rustup component add miri

# 更新工具链
rustup update

# 验证安装
cargo miri --version
```

### 1.3 常用 Miri 命令

```bash
# 运行测试
cargo +nightly miri test

# 运行特定测试
cargo +nightly miri test -- test_name

# 运行示例
cargo +nightly miri run --example example_name

# 启用 Tree Borrows (实验性)
MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test

# 启用数据竞争检测
MIRIFLAGS="-Zmiri-disable-isolation" cargo +nightly miri test

# 限制输出大小
MIRIFLAGS="-Zmiri-report-progress=10000" cargo +nightly miri test
```

### 1.4 Miri 输出解读

| 输出类型 | 含义 | 处理方式 |
|---------|------|---------|
| `error: Undefined Behavior` | 检测到 UB | 必须修复 |
| `warning: thread panicked` | 线程恐慌 | 检查恐慌原因 |
| `note: inside call to ...` | 调用堆栈 | 定位问题源 |

### 1.5 Stacked Borrows vs Tree Borrows

```bash
# Stacked Borrows (默认，更严格)
cargo +nightly miri test

# Tree Borrows (实验性，更宽松)
MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test
```

**差异示例**:

- Stacked Borrows 对指针别名要求更严格
- Tree Borrows 允许更多合法的指针别名模式
- 两个模型都通过 = 代码是正确的
- Tree Borrows 通过但 Stacked Borrows 失败 = 可能是假阳性，但建议修复

---

## 2. 原始指针操作模式

### 2.1 问题场景

当需要：

- 与 C 代码交互
- 实现自定义数据结构（如 Vec, HashMap）
- 进行性能关键的字节操作
- 需要绕过借用检查器的场景

### 2.2 代码示例：堆分配和裸指针解引用

```rust
//! 原始指针基础操作示例
//! 运行: cargo +nightly miri test -- raw_pointer

use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

/// 危险等级: ⚠️ 中等
///
/// 动态分配数组并管理其生命周期
pub struct RawBuffer<T> {
    ptr: *mut T,
    len: usize,
    capacity: usize,
}

impl<T> RawBuffer<T> {
    /// 创建指定容量的原始缓冲区
    ///
    /// # Safety
    /// - 容量必须大于 0
    /// - T 必须是非零大小类型
    pub fn new(capacity: usize) -> Option<Self> {
        if capacity == 0 || std::mem::size_of::<T>() == 0 {
            return None;
        }

        // SAFETY: 已检查 capacity > 0 且 size_of::<T>() > 0
        let layout = match Layout::array::<T>(capacity) {
            Ok(layout) => layout,
            Err(_) => return None,
        };

        // SAFETY: layout 是有效的，大小非零
        let ptr = unsafe { alloc(layout) as *mut T };

        if ptr.is_null() {
            handle_alloc_error(layout);
        }

        Some(Self {
            ptr,
            len: 0,
            capacity,
        })
    }

    /// 获取指定索引的元素引用
    ///
    /// # Safety
    /// - index < self.len
    /// - 引用的生命周期必须有效
    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        debug_assert!(index < self.len, "index out of bounds");
        // SAFETY: 调用者保证 index < len，且 ptr 有效
        unsafe { &*self.ptr.add(index) }
    }

    /// 设置指定索引的元素
    ///
    /// # Safety
    /// - index < self.capacity
    /// - 不会导致内存泄漏（旧值未 drop）
    pub unsafe fn set_unchecked(&mut self, index: usize, value: T) {
        debug_assert!(index < self.capacity, "index out of capacity");
        // SAFETY: 调用者保证 index < capacity
        unsafe {
            self.ptr.add(index).write(value);
        }
        if index >= self.len {
            self.len = index + 1;
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn capacity(&self) -> usize {
        self.capacity
    }
}

impl<T> Drop for RawBuffer<T> {
    fn drop(&mut self) {
        // 先 drop 所有已初始化的元素
        for i in 0..self.len {
            // SAFETY: 0..len 范围内的元素都已初始化
            unsafe {
                std::ptr::drop_in_place(self.ptr.add(i));
            }
        }

        // 释放内存
        // SAFETY: ptr 是通过 alloc 分配的，layout 计算正确
        unsafe {
            let layout = Layout::array::<T>(self.capacity).unwrap_unchecked();
            dealloc(self.ptr as *mut u8, layout);
        }
    }
}

// SAFETY: RawBuffer 是 Send，因为拥有唯一所有权
unsafe impl<T: Send> Send for RawBuffer<T> {}

// SAFETY: RawBuffer 是 Sync，因为所有方法都需要 &self 或 &mut self
unsafe impl<T: Sync> Sync for RawBuffer<T> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_raw_buffer_basic() {
        let mut buf = RawBuffer::<i32>::new(10).unwrap();

        unsafe {
            buf.set_unchecked(0, 42);
            buf.set_unchecked(5, 100);
        }

        assert_eq!(unsafe { *buf.get_unchecked(0) }, 42);
        assert_eq!(buf.len(), 6);
    }
}
```

### 2.3 安全契约

| 契约 | 说明 | 违反后果 |
|-----|------|---------|
| 有效性 | 指针必须指向有效的、已分配的内存 | 段错误/UB |
| 对齐 | 指针必须正确对齐 | 未对齐访问 UB |
| 生命周期 | 解引用必须在内存生命周期内 | 使用已释放内存 |
| 别名规则 | 可变引用不能有别名 | 数据竞争/UB |

### 2.4 Miri 验证

```bash
# 验证原始指针操作
cargo +nightly miri test raw_buffer

# 预期输出: 无错误，测试通过
```

### 2.5 常见错误：UB 示例和修复

```rust
/// ❌ 错误：悬垂指针
fn dangling_pointer_bug() {
    let ptr: *const i32;
    {
        let x = 42;
        ptr = &x;  // x 的生命周期在此结束
    }  // x 被 drop
    // UB: 使用已释放内存
    unsafe { println!("{}", *ptr); }
}

/// ✅ 修复：确保生命周期有效
fn fixed_dangling_pointer() -> Box<i32> {
    let x = Box::new(42);
    let ptr: *const i32 = &*x;
    // ptr 在 x 生命周期内有效
    unsafe { println!("{}", *ptr); }
    x  // 返回 Box 保持生命周期
}

/// ❌ 错误：未对齐访问
fn unaligned_access_bug() {
    let bytes: [u8; 8] = [0; 8];
    let ptr = bytes.as_ptr() as *const u64;  // 可能未对齐到 8
    // UB: 未对齐读取
    unsafe { let _ = *ptr; }
}

/// ✅ 修复：使用 read_unaligned
fn fixed_unaligned_access() {
    let bytes: [u8; 8] = [0; 8];
    let ptr = bytes.as_ptr() as *const u64;
    // 安全：允许未对齐读取
    let value = unsafe { ptr.read_unaligned() };
}
```

### 2.6 替代方案

| 场景 | Unsafe 方案 | Safe 替代 |
|-----|-------------|----------|
| 动态数组 | RawBuffer | `Vec<T>` |
| 堆分配 | `alloc`/`dealloc` | `Box::new` |
| 指针算术 | `ptr.add()` | 索引访问 |
| 类型转换 | `mem::transmute` | `From`/`Into` traits |

### 2.7 生产案例

- **`Vec<T>`**: Rust 标准库使用原始指针实现
- **`HashMap`**: hashbrown 库使用原始指针管理桶
- **`String`**: 内部使用 `Vec<u8>` 的原始指针操作

---

## 3. 自引用结构体

### 3.1 问题场景

当结构体需要引用自身的其他字段时：

- 解析器需要引用输入缓冲区的切片
- 异步状态机保存对其自身的引用
- 复杂的树结构需要父子引用

### 3.2 代码示例：Pin 和堆分配自引用

```rust
//! 自引用结构体安全模式
//! 运行: cargo +nightly miri test -- self_referential

use std::pin::Pin;
use std::marker::PhantomPinned;

/// 危险等级: 🔴 高
///
/// 自引用结构体的安全实现
/// 使用 Pin + PhantomPinned 防止移动
pub struct SelfReferential {
    // 实际数据
    data: String,

    // 指向 data 的指针
    // 注意：这是危险的，因为 data 移动时 ptr 会悬垂
    data_ptr: *const String,

    // 标记此类型不应被移动（除非在 Pin 后）
    _pin: PhantomPinned,
}

impl SelfReferential {
    pub fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::new(Self {
            data,
            data_ptr: std::ptr::null(),
            _pin: PhantomPinned,
        });

        // 设置自引用指针
        let ptr = &boxed.data as *const String;
        boxed.data_ptr = ptr;

        // 返回 Pin<Box<_>>，防止移动
        Box::into_pin(boxed)
    }

    /// 通过原始指针安全访问 data
    pub fn data_ref(self: Pin<&Self>) -> &String {
        // SAFETY:
        // 1. 我们被 Pin 保护，不会移动
        // 2. data_ptr 指向有效的 data 字段
        unsafe { &*self.data_ptr }
    }

    /// 安全地更新数据
    ///
    /// # Safety
    /// 必须保持 Pin 契约
    pub fn set_data(self: Pin<&mut Self>, new_data: String) {
        // SAFETY: 我们不会移动 self
        let this = unsafe { self.get_unchecked_mut() };

        // 更新数据
        this.data = new_data;

        // 更新自引用指针
        this.data_ptr = &this.data as *const String;
    }
}

impl Drop for SelfReferential {
    fn drop(&mut self) {
        // 清理逻辑，data 会自动 drop
        println!("Dropping SelfReferential");
    }
}

/// 更复杂的例子：解析结果持有输入引用
pub struct ParserResult<'a> {
    input: String,
    // 指向 input 的切片
    tokens: Vec<&'a str>,
}

/// 危险等级: 🔴 极高
///
/// 使用 Pin 和 unsafe 实现安全的自引用解析器
pub struct OwningParser {
    input: String,
    tokens: Vec<*const str>,
    _pin: PhantomPinned,
}

impl OwningParser {
    pub fn new(input: String) -> Pin<Box<Self>> {
        let mut boxed = Box::new(Self {
            input,
            tokens: Vec::new(),
            _pin: PhantomPinned,
        });

        // 解析并存储指针
        let input_ptr = boxed.input.as_str() as *const str;
        let tokens: Vec<*const str> = boxed.input
            .split_whitespace()
            .map(|s| s as *const str)
            .collect();
        boxed.tokens = tokens;

        Box::into_pin(boxed)
    }

    pub fn tokens(self: Pin<&Self>) -> Vec<&str> {
        // SAFETY: Pin 保证我们不会被移动，所有指针都有效
        self.tokens
            .iter()
            .map(|&ptr| unsafe { &*ptr })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_self_referential() {
        let pinned = SelfReferential::new(String::from("Hello, World!"));
        assert_eq!(pinned.as_ref().data_ref(), "Hello, World!");
    }

    #[test]
    fn test_owning_parser() {
        let parser = OwningParser::new(String::from("hello world test"));
        let tokens = parser.as_ref().tokens();
        assert_eq!(tokens, vec!["hello", "world", "test"]);
    }
}
```

### 3.3 栈上自引用（危险模式）

```rust
/// 🔴 极度危险：栈上自引用
/// 永远不要这样做！
fn stack_self_reference_bug() {
    let mut x = String::from("hello");
    let ptr: *const String = &x;

    // 任何移动都会导致 UB
    let y = x;  // 移动！ptr 现在悬垂

    // UB: 使用悬垂指针
    unsafe { println!("{}", (*ptr).len()); }
}

/// ✅ 使用 rental 或 ouroboros crate
/// 或者使用 Pin<Box<_>> 确保堆分配
```

### 3.4 安全契约

| 契约 | 说明 |
|-----|------|
| Pin 约束 | 必须保持 Pin 契约，不移动数据 |
| 堆分配 | 自引用结构体必须堆分配 |
| PhantomPinned | 必须标记以防止自动 Unpin |
| 指针更新 | 任何可能移动内部数据的操作必须更新指针 |

### 3.5 替代方案

- **`rental` crate**: 简化自引用结构体
- **`ouroboros` crate**: 宏驱动的自引用
- **`yoke` crate**: 从 ICU4X 项目，零拷贝反序列化

### 3.6 生产案例

- **异步/等待**: Rust 的 async/await 使用 Pin 保存自引用状态机
- **Futures**: `std::future::Future` 大量使用 Pin
- **Str 切片**: 解析器库如 `nom` 使用引用避免拷贝

---

## 4. 自定义 Drop 和内存管理

### 4.1 问题场景

当需要：

- 与 C 库分配的内存交互
- 实现自定义的智能指针
- 管理非 Rust 资源（文件句柄、网络连接）
- 处理循环引用

### 4.2 代码示例：与 C 内存交互

```rust
//! 自定义 Drop 和 C 内存管理
//! 运行: cargo +nightly miri test -- custom_drop

use std::ffi::{c_void, CStr, CString};
use std::ptr::NonNull;

/// 模拟 C 库接口
mod c_lib {
    use std::ffi::c_void;

    #[repr(C)]
    pub struct CBuffer {
        pub data: *mut u8,
        pub len: usize,
        pub capacity: usize,
    }

    extern "C" {
        pub fn c_buffer_new(capacity: usize) -> *mut CBuffer;
        pub fn c_buffer_free(buf: *mut CBuffer);
        pub fn c_buffer_append(buf: *mut CBuffer, data: *const u8, len: usize) -> i32;
    }
}

/// 危险等级: 🔴 高
///
/// 安全包装 C 分配的资源
pub struct CBufferWrapper {
    inner: NonNull<c_lib::CBuffer>,
}

impl CBufferWrapper {
    pub fn new(capacity: usize) -> Option<Self> {
        // SAFETY: C 函数期望正确的参数
        let ptr = unsafe { c_lib::c_buffer_new(capacity) };
        NonNull::new(ptr).map(|inner| Self { inner })
    }

    pub fn append(&mut self, data: &[u8]) -> Result<(), ()> {
        // SAFETY: inner 是有效的，data 是有效的字节切片
        let result = unsafe {
            c_lib::c_buffer_append(
                self.inner.as_ptr(),
                data.as_ptr(),
                data.len(),
            )
        };

        if result == 0 {
            Ok(())
        } else {
            Err(())
        }
    }

    pub fn as_slice(&self) -> &[u8] {
        // SAFETY: inner 是有效的
        let buf = unsafe { self.inner.as_ref() };
        if buf.data.is_null() || buf.len == 0 {
            return &[];
        }
        // SAFETY: C 库保证 data 指向 len 个有效字节
        unsafe { std::slice::from_raw_parts(buf.data, buf.len) }
    }
}

impl Drop for CBufferWrapper {
    fn drop(&mut self) {
        // SAFETY: inner 是有效的，只 drop 一次
        unsafe {
            c_lib::c_buffer_free(self.inner.as_ptr());
        }
    }
}

// SAFETY: CBufferWrapper 拥有唯一的非空指针
unsafe impl Send for CBufferWrapper {}
unsafe impl Sync for CBufferWrapper {}

/// 手动内存释放模式：Box::from_raw / into_raw
pub struct RawBox<T> {
    ptr: NonNull<T>,
}

impl<T> RawBox<T> {
    pub fn new(value: T) -> Self {
        let boxed = Box::new(value);
        let ptr = NonNull::new(Box::into_raw(boxed)).unwrap();
        Self { ptr }
    }

    /// 转换为原始指针，调用者负责释放
    ///
    /// # Safety
    /// 调用者必须使用对应的方法释放内存
    pub unsafe fn into_raw(self) -> *mut T {
        let ptr = self.ptr.as_ptr();
        std::mem::forget(self);  // 防止正常 drop
        ptr
    }

    /// 从原始指针创建，假设它是有效的
    ///
    /// # Safety
    /// - ptr 必须是通过 into_raw 创建的
    /// - ptr 必须只被使用一次
    pub unsafe fn from_raw(ptr: *mut T) -> Self {
        Self {
            ptr: NonNull::new(ptr).expect("null pointer"),
        }
    }
}

impl<T> std::ops::Deref for RawBox<T> {
    type Target = T;

    fn deref(&self) -> &T {
        // SAFETY: ptr 是有效的 Box 指针
        unsafe { self.ptr.as_ref() }
    }
}

impl<T> std::ops::DerefMut for RawBox<T> {
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: ptr 是有效的 Box 指针，我们有唯一访问权
        unsafe { self.ptr.as_mut() }
    }
}

impl<T> Drop for RawBox<T> {
    fn drop(&mut self) {
        // SAFETY: ptr 是通过 Box::into_raw 创建的
        unsafe {
            drop(Box::from_raw(self.ptr.as_ptr()));
        }
    }
}

/// Drop 检查绕过模式：ManuallyDrop
pub struct FlexibleUnion<T, U> {
    tag: u8,
    // SAFETY: 必须根据 tag 来正确解释
    data: std::mem::ManuallyDrop<std::mem::MaybeUninit<(T, U)>>,
}

impl<T, U> FlexibleUnion<T, U> {
    pub fn new_t(value: T) -> Self {
        Self {
            tag: 0,
            data: std::mem::ManuallyDrop::new(
                std::mem::MaybeUninit::new((value, unsafe { std::mem::zeroed() }))
            ),
        }
    }

    pub fn as_t(&self) -> Option<&T> {
        if self.tag == 0 {
            // SAFETY: tag 表示这是 T 变体
            Some(unsafe { &(*self.data.as_ptr()).0 })
        } else {
            None
        }
    }
}

impl<T, U> Drop for FlexibleUnion<T, U> {
    fn drop(&mut self) {
        // SAFETY: 根据 tag 正确 drop
        unsafe {
            if self.tag == 0 {
                std::ptr::drop_in_place(&mut (*self.data.as_mut_ptr()).0);
            } else {
                std::ptr::drop_in_place(&mut (*self.data.as_mut_ptr()).1);
            }
            // ManuallyDrop 不会自动 drop，我们手动处理了
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_raw_box() {
        let raw = RawBox::new(42i32);
        assert_eq!(*raw, 42);
    }
}
```

### 4.3 Drop 检查绕过

```rust
/// ❌ 错误：双 Drop
fn double_drop_bug() {
    let x = Box::new(42);
    let ptr = Box::into_raw(x);
    unsafe {
        drop(Box::from_raw(ptr));  // 第一次 drop
        drop(Box::from_raw(ptr));  // UB: 双释放！
    }
}

/// ✅ 修复：使用 ManuallyDrop 或标记已 drop
use std::sync::atomic::{AtomicBool, Ordering};

pub struct SafeDrop<T> {
    value: Option<T>,
    dropped: AtomicBool,
}

impl<T> SafeDrop<T> {
    pub fn take(&mut self) -> Option<T> {
        if !self.dropped.swap(true, Ordering::SeqCst) {
            self.value.take()
        } else {
            None
        }
    }
}

impl<T> Drop for SafeDrop<T> {
    fn drop(&mut self) {
        if !self.dropped.load(Ordering::SeqCst) {
            self.dropped.store(true, Ordering::SeqCst);
            // 现在安全 drop value
            drop(self.value.take());
        }
    }
}
```

### 4.4 生产案例

- **`Box<T>`**: 标准库的智能指针实现
- **`Rc<T>`/`Arc<T>`**: 引用计数实现
- **`CString`**: C 字符串的内存管理

---

## 5. Union 访问

### 5.1 问题场景

当需要：

- 与 C 联合体互操作
- 类型双关（如网络协议解析）
- 手动内存布局控制

### 5.2 代码示例：Union 安全访问

```rust
//! Union 访问模式
//! 运行: cargo +nightly miri test -- union_access

/// 危险等级: 🔴 高
///
/// 带标签的联合体实现
#[repr(C)]
pub enum TaggedValue {
    Integer(i64),
    Float(f64),
    Boolean(bool),
}

/// 危险等级: 🔴 极高
///
/// 与 C 互操作的联合体
#[repr(C)]
pub union RawValue {
    pub int: i64,
    pub float: f64,
    pub bool: bool,
    pub ptr: *mut (),
}

/// 安全包装器：带运行时标签检查
pub struct SafeUnion {
    tag: UnionTag,
    value: RawValue,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum UnionTag {
    Integer,
    Float,
    Boolean,
    Pointer,
}

impl SafeUnion {
    pub fn new_integer(v: i64) -> Self {
        Self {
            tag: UnionTag::Integer,
            value: RawValue { int: v },
        }
    }

    pub fn new_float(v: f64) -> Self {
        Self {
            tag: UnionTag::Float,
            value: RawValue { float: v },
        }
    }

    /// 安全获取整数
    pub fn as_integer(&self) -> Option<i64> {
        if self.tag == UnionTag::Integer {
            // SAFETY: 标签匹配
            Some(unsafe { self.value.int })
        } else {
            None
        }
    }

    /// 安全获取浮点数
    pub fn as_float(&self) -> Option<f64> {
        if self.tag == UnionTag::Float {
            // SAFETY: 标签匹配
            Some(unsafe { self.value.float })
        } else {
            None
        }
    }

    /// 危险：类型双关读取
    ///
    /// # Safety
    /// 调用者必须知道这种解释是有效的
    pub unsafe fn reinterpret_as_bytes(&self) -> [u8; 8] {
        // SAFETY: 读取 union 的原始字节
        unsafe { std::mem::transmute::<i64, [u8; 8]>(self.value.int) }
    }
}

impl Drop for SafeUnion {
    fn drop(&mut self) {
        // SAFETY: 根据标签正确 drop 可能包含指针的变体
        unsafe {
            match self.tag {
                UnionTag::Pointer => {
                    // 如果有指针需要 drop
                    if !self.value.ptr.is_null() {
                        drop(Box::from_raw(self.value.ptr as *mut i32));
                    }
                }
                _ => {}  // 其他类型是 Copy，不需要特殊处理
            }
        }
    }
}

/// 类型双关示例：网络协议头解析
#[repr(C, packed)]
struct Ipv4Header {
    version_ihl: u8,
    tos: u8,
    total_length: u16,
    identification: u16,
    flags_fragment: u16,
    ttl: u8,
    protocol: u8,
    checksum: u16,
    src_ip: [u8; 4],
    dst_ip: [u8; 4],
}

union PacketHeader {
    bytes: [u8; 20],
    ipv4: std::mem::ManuallyDrop<Ipv4Header>,
}

/// 安全地解析 IPv4 头部
pub fn parse_ipv4_header(bytes: &[u8]) -> Option<Ipv4Header> {
    if bytes.len() < 20 {
        return None;
    }

    // SAFETY: 我们检查了长度，使用 ManuallyDrop 避免 double drop
    Some(unsafe {
        let mut header = PacketHeader { bytes: [0; 20] };
        header.bytes.copy_from_slice(&bytes[..20]);
        std::mem::ManuallyDrop::into_inner(header.ipv4)
    })
}

/// ❌ 错误：读取未初始化的 union 字段
fn uninitialized_union_bug() {
    let u: RawValue;
    // UB: 读取未初始化的 union 字段
    let _ = unsafe { u.int };
}

/// ✅ 修复：确保写入后再读取
fn fixed_uninitialized_union() {
    let u = RawValue { int: 42 };
    let v = unsafe { u.int };  // 安全：int 已初始化
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_safe_union() {
        let u = SafeUnion::new_integer(42);
        assert_eq!(u.as_integer(), Some(42));
        assert_eq!(u.as_float(), None);
    }
}
```

### 5.3 常见错误

```rust
/// ❌ 错误：错误类型双关（可能导致无效值）
fn invalid_bool_bug() {
    let u = RawValue { int: 42 };  // 42 不是有效的 bool 值
    // UB: bool 必须是 0 或 1
    let b = unsafe { u.bool };
}

/// ✅ 修复：确保值有效
fn fixed_invalid_bool() {
    let u = RawValue { bool: true };
    let b = unsafe { u.bool };  // 安全
}
```

### 5.4 生产案例

- **`std::mem::MaybeUninit`**: 内部使用 union 实现
- **网络库**: 如 `tokio` 使用 union 处理协议头
- **FFI 绑定**: 如 `winapi` 使用 union 映射 C 结构

---

## 6. FFI 边界处理

### 6.1 问题场景

当需要：

- 调用 C/C++ 库
- 暴露 Rust 函数给 C
- 处理不同 ABI 的交互
- 管理跨语言生命周期

### 6.2 代码示例：完整 FFI 边界

```rust
//! FFI 边界安全处理
//! 运行: cargo +nightly miri test -- ffi_boundary

use std::ffi::{c_char, c_int, c_void, CStr, CString};
use std::sync::{Arc, Mutex};

// ============================================================================
// C 库接口声明
// ============================================================================

#[repr(C)]
pub struct CContext {
    _opaque: [u8; 0],  // 不透明指针
}

#[link(name = "example_c_lib")]
extern "C" {
    fn ctx_create() -> *mut CContext;
    fn ctx_destroy(ctx: *mut CContext);
    fn ctx_process(ctx: *mut CContext, data: *const c_char, len: c_int) -> c_int;
    fn ctx_set_callback(ctx: *mut CContext, cb: extern "C" fn(*const c_char));
}

// ============================================================================
// 安全的 Rust 包装器
// ============================================================================

/// 危险等级: 🔴 高
///
/// C 上下文的安全包装器
pub struct Context {
    ptr: *mut CContext,
    callback: Option<Box<dyn Fn(&str) + Send>>,
}

// SAFETY: Context 内部使用 Mutex 保护访问
unsafe impl Send for Context {}
unsafe impl Sync for Context {}

impl Context {
    pub fn new() -> Option<Self> {
        // SAFETY: C 函数返回有效的指针或 null
        let ptr = unsafe { ctx_create() };
        if ptr.is_null() {
            None
        } else {
            Some(Self {
                ptr,
                callback: None,
            })
        }
    }

    /// 处理字符串数据
    pub fn process(&mut self, data: &str) -> Result<(), ()> {
        // 转换 Rust 字符串为 C 字符串
        let c_string = match CString::new(data) {
            Ok(s) => s,
            Err(_) => return Err(()),  // 数据包含 null 字节
        };

        // SAFETY:
        // 1. ptr 是有效的
        // 2. c_string.as_ptr() 在调用期间有效
        let result = unsafe {
            ctx_process(self.ptr, c_string.as_ptr(), c_string.as_bytes().len() as c_int)
        };

        if result == 0 {
            Ok(())
        } else {
            Err(())
        }
    }

    /// 设置回调函数
    ///
    /// # Safety
    /// 回调必须在 Context 生命周期内有效
    pub unsafe fn set_callback<F>(&mut self, callback: F)
    where
        F: Fn(&str) + Send + 'static,
    {
        self.callback = Some(Box::new(callback));

        // SAFETY: 回调是 'static 的，我们保存了 Box
        unsafe {
            ctx_set_callback(self.ptr, global_callback_trampoline);
        }
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        // 先清除回调，防止在销毁期间被调用
        self.callback = None;

        // SAFETY: ptr 是有效的，且只销毁一次
        unsafe {
            ctx_destroy(self.ptr);
        }
    }
}

/// 全局回调跳板函数
extern "C" fn global_callback_trampoline(data: *const c_char) {
    // SAFETY: C 库保证 data 是有效的 C 字符串
    let c_str = unsafe { CStr::from_ptr(data) };

    if let Ok(s) = c_str.to_str() {
        // 这里需要通过某种方式获取注册的回调
        // 简化示例：直接打印
        println!("Callback received: {}", s);
    }
}

// ============================================================================
// 暴露 Rust 函数给 C
// ============================================================================

/// 线程安全的计数器，暴露给 C
static COUNTER: Mutex<i64> = Mutex::new(0);

/// C 可调用的函数
///
/// # Safety
/// 必须确保是单线程或通过其他方式同步
#[no_mangle]
pub extern "C" fn rust_increment_counter() -> i64 {
    let mut guard = COUNTER.lock().unwrap();
    *guard += 1;
    *guard
}

/// 处理 C 字符串并返回结果
///
/// # Safety
/// - input 必须是有效的 C 字符串指针
/// - output_len 必须指向可写的内存
#[no_mangle]
pub unsafe extern "C" fn rust_process_string(
    input: *const c_char,
    output: *mut c_char,
    output_len: *mut usize,
) -> c_int {
    // 验证输入
    if input.is_null() || output.is_null() || output_len.is_null() {
        return -1;
    }

    // SAFETY: 调用者保证指针有效
    let input_str = match unsafe { CStr::from_ptr(input).to_str() } {
        Ok(s) => s,
        Err(_) => return -2,  // 无效的 UTF-8
    };

    // 处理字符串
    let result = input_str.to_uppercase();

    // SAFETY: 调用者保证 output_len 有效
    let max_len = unsafe { *output_len };

    if result.len() >= max_len {
        // 输出缓冲区太小
        return -3;
    }

    // 复制结果到输出缓冲区
    // SAFETY: 我们已检查缓冲区大小
    unsafe {
        std::ptr::copy_nonoverlapping(
            result.as_ptr() as *const c_char,
            output,
            result.len(),
        );
        *output.add(result.len()) = 0;  // null 终止
        *output_len = result.len();
    }

    0  // 成功
}

// ============================================================================
// 常见错误示例
// ============================================================================

/// ❌ 错误：跨越 FFI 边界的裸指针使用
///
/// 不要将引用作为指针传递，除非确保生命周期
fn ffi_pointer_bug() {
    let x = 42;
    let ptr: *const i32 = &x;
    // 假设传递给 C 并存储...
    // C 稍后使用 ptr -> UB，因为 x 已被 drop
}

/// ✅ 修复：使用堆分配
fn fixed_ffi_pointer() -> Box<i32> {
    Box::new(42)  // 生命周期由调用者管理
}

/// ❌ 错误：panic 跨越 FFI 边界
#[no_mangle]
pub extern "C" fn may_panic() {
    panic!("This will cause UB if called from C!");
}

/// ✅ 修复：捕获 panic
use std::panic::catch_unwind;

#[no_mangle]
pub extern "C" fn safe_may_panic() -> c_int {
    match catch_unwind(|| {
        // 可能 panic 的操作
        if std::env::var("PANIC").is_ok() {
            panic!("controlled panic");
        }
        0
    }) {
        Ok(result) => result,
        Err(_) => -1,  // panic 发生
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_counter() {
        let v1 = rust_increment_counter();
        let v2 = rust_increment_counter();
        assert_eq!(v2, v1 + 1);
    }
}
```

### 6.3 FFI 安全契约

| 方面 | 契约 | 检查方式 |
|-----|------|---------|
| 空指针 | 检查所有指针参数 | `ptr.is_null()` |
| 生命周期 | 确保引用在 C 使用期间有效 | 文档 + 架构 |
| ABI | 使用正确的 `extern "C"` | 编译器检查 |
| Panic | 不要跨越 FFI 边界 | `catch_unwind` |
| 线程 | 确保线程安全 | `Send`/`Sync` |

### 6.4 生产案例

- **`libc` crate**: 标准 C 库绑定
- **`winapi` crate**: Windows API 绑定
- **`openssl-sys`**: OpenSSL FFI 绑定

---

## 7. SIMD 和矢量化

### 7.1 问题场景

当需要：

- 高性能数值计算
- 批量数据处理
- 图形/图像处理
- 密码学运算

### 7.2 代码示例：SIMD 安全包装

```rust
//! SIMD 和矢量化操作
//! 运行: cargo +nightly miri test -- simd  (注意：Miri 对 SIMD 支持有限)

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

/// 危险等级: ⚠️ 中等
///
/// 安全的 SIMD 向量加法包装器
#[cfg(target_arch = "x86_64")]
pub fn simd_add_f32(a: &[f32], b: &[f32], result: &mut [f32]) {
    assert_eq!(a.len(), b.len());
    assert_eq!(a.len(), result.len());

    let len = a.len();
    let mut i = 0;

    // SAFETY: 我们已检查长度
    unsafe {
        // 使用 AVX (256-bit = 8 f32)
        while i + 8 <= len {
            let va = _mm256_loadu_ps(a.as_ptr().add(i));
            let vb = _mm256_loadu_ps(b.as_ptr().add(i));
            let vr = _mm256_add_ps(va, vb);
            _mm256_storeu_ps(result.as_mut_ptr().add(i), vr);
            i += 8;
        }

        // 使用 SSE (128-bit = 4 f32)
        while i + 4 <= len {
            let va = _mm_loadu_ps(a.as_ptr().add(i));
            let vb = _mm_loadu_ps(b.as_ptr().add(i));
            let vr = _mm_add_ps(va, vb);
            _mm_storeu_ps(result.as_mut_ptr().add(i), vr);
            i += 4;
        }
    }

    // 处理剩余元素
    for j in i..len {
        result[j] = a[j] + b[j];
    }
}

/// 安全的数组求和（自动 SIMD 向量化）
pub fn safe_sum(arr: &[f32]) -> f32 {
    arr.iter().sum()
}

/// 手动向量化点积
#[cfg(target_arch = "x86_64")]
pub fn simd_dot_product(a: &[f32], b: &[f32]) -> f32 {
    assert_eq!(a.len(), b.len());

    let len = a.len();
    let mut sum = 0.0f32;
    let mut i = 0;

    // SAFETY: 我们已检查长度和对齐
    unsafe {
        // AVX 累加
        let mut acc = _mm256_setzero_ps();

        while i + 8 <= len {
            let va = _mm256_loadu_ps(a.as_ptr().add(i));
            let vb = _mm256_loadu_ps(b.as_ptr().add(i));
            acc = _mm256_fmadd_ps(va, vb, acc);  // a * b + acc
            i += 8;
        }

        // 水平累加
        let mut temp = [0.0f32; 8];
        _mm256_storeu_ps(temp.as_mut_ptr(), acc);
        sum = temp.iter().sum();
    }

    // 处理剩余
    for j in i..len {
        sum += a[j] * b[j];
    }

    sum
}

/// 内联汇编示例（极度危险）
#[cfg(target_arch = "x86_64")]
pub unsafe fn read_tsc() -> u64 {
    let low: u32;
    let high: u32;

    // SAFETY: rdtsc 在所有 x86_64 上都可用
    unsafe {
        core::arch::asm!(
            "rdtsc",
            lateout("eax") low,
            lateout("edx") high,
            options(nomem, nostack)
        );
    }

    ((high as u64) << 32) | (low as u64)
}

/// 类型对齐检查
pub fn check_alignment<T>(ptr: *const T) -> bool {
    let align = std::mem::align_of::<T>();
    (ptr as usize) % align == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_safe_sum() {
        let arr = vec![1.0, 2.0, 3.0, 4.0];
        assert_eq!(safe_sum(&arr), 10.0);
    }

    #[test]
    #[cfg(target_arch = "x86_64")]
    fn test_simd_dot_product() {
        let a = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
        let b = vec![1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0];
        let result = simd_dot_product(&a, &b);
        assert!((result - 36.0).abs() < 0.001);
    }
}
```

### 7.3 常见错误

```rust
/// ❌ 错误：未对齐访问（可能崩溃）
#[cfg(target_arch = "x86_64")]
unsafe fn unaligned_simd_bug() {
    let arr = [0u8; 32];
    let ptr = arr.as_ptr().add(1) as *const __m256;  // 未对齐到 32 字节
    let _ = _mm256_load_ps(ptr);  // 可能段错误
}

/// ✅ 修复：使用未对齐加载
#[cfg(target_arch = "x86_64")]
unsafe fn fixed_unaligned_simd() {
    let arr = [0u8; 32];
    let ptr = arr.as_ptr().add(1) as *const __m256;
    let _ = _mm256_loadu_ps(ptr as *const f32);  // 'u' = unaligned
}
```

### 7.4 生产案例

- **`packed_simd`**: 可移植 SIMD 库
- **`std::simd` (nightly)**: 标准库 SIMD
- **`wide` crate**: 安全的跨平台 SIMD

---

## 8. 并发原语实现

### 8.1 问题场景

当需要：

- 实现自定义同步原语
- 无锁数据结构
- 性能关键的并发代码
- 特定平台的原子操作

### 8.2 代码示例：自定义自旋锁

```rust
//! 并发原语实现
//! 运行: cargo +nightly miri test -- concurrency
//! 注意：Miri 可以检测并发问题

use std::cell::UnsafeCell;
use std::ops::{Deref, DerefMut};
use std::sync::atomic::{fence, AtomicBool, Ordering};
use std::thread;
use std::time::Duration;

/// 危险等级: 🔴 极高
///
/// 简单的自旋锁实现
pub struct SpinLock<T> {
    locked: AtomicBool,
    data: UnsafeCell<T>,
}

// SAFETY: SpinLock 可以被发送到其他线程
unsafe impl<T: Send> Send for SpinLock<T> {}

// SAFETY: SpinLock 可以在线程间共享
unsafe impl<T: Send> Sync for SpinLock<T> {}

pub struct SpinLockGuard<'a, T> {
    lock: &'a SpinLock<T>,
}

impl<T> SpinLock<T> {
    pub fn new(data: T) -> Self {
        Self {
            locked: AtomicBool::new(false),
            data: UnsafeCell::new(data),
        }
    }

    pub fn lock(&self) -> SpinLockGuard<T> {
        // 自旋直到获取锁
        while self.locked.compare_exchange(
            false,
            true,
            Ordering::Acquire,  // 获取锁时的内存序
            Ordering::Relaxed,
        ).is_err() {
            // 提示处理器我们在自旋
            std::hint::spin_loop();
        }

        // 内存屏障：确保锁获取后的读写不会重排序到前面
        fence(Ordering::Acquire);

        SpinLockGuard { lock: self }
    }

    /// 尝试获取锁
    pub fn try_lock(&self) -> Option<SpinLockGuard<T>> {
        if self.locked.compare_exchange(
            false,
            true,
            Ordering::Acquire,
            Ordering::Relaxed,
        ).is_ok() {
            fence(Ordering::Acquire);
            Some(SpinLockGuard { lock: self })
        } else {
            None
        }
    }
}

impl<T> Deref for SpinLockGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // SAFETY: 我们持有锁，且锁保证独占访问
        unsafe { &*self.lock.data.get() }
    }
}

impl<T> DerefMut for SpinLockGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: 我们持有锁，且锁保证独占访问
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<T> Drop for SpinLockGuard<'_, T> {
    fn drop(&mut self) {
        // 内存屏障：确保锁释放前的读写不会重排序到后面
        fence(Ordering::Release);

        // 释放锁
        self.lock.locked.store(false, Ordering::Release);
    }
}

/// 无锁计数器（原子操作）
pub struct AtomicCounter {
    count: std::sync::atomic::AtomicUsize,
}

impl AtomicCounter {
    pub fn new() -> Self {
        Self {
            count: std::sync::atomic::AtomicUsize::new(0),
        }
    }

    /// 递增并返回新值
    pub fn increment(&self) -> usize {
        self.count.fetch_add(1, Ordering::Relaxed)
    }

    /// 获取当前值
    pub fn get(&self) -> usize {
        self.count.load(Ordering::SeqCst)
    }
}

/// 使用 UnsafeCell 的可变引用模式
pub struct UnsafeContainer<T> {
    inner: UnsafeCell<T>,
}

impl<T> UnsafeContainer<T> {
    pub fn new(value: T) -> Self {
        Self {
            inner: UnsafeCell::new(value),
        }
    }

    /// 获取不可变引用
    pub fn get(&self) -> &T {
        // SAFETY: 调用者必须确保没有其他可变引用
        unsafe { &*self.inner.get() }
    }

    /// 获取可变引用
    pub fn get_mut(&mut self) -> &mut T {
        // SAFETY: &mut self 保证独占访问
        unsafe { &mut *self.inner.get() }
    }

    /// 不安全地获取原始指针
    pub fn as_ptr(&self) -> *mut T {
        self.inner.get()
    }
}

// SAFETY: 如果 T 是 Send，UnsafeContainer 也是 Send
unsafe impl<T: Send> Send for UnsafeContainer<T> {}

// SAFETY: 如果 T 是 Sync，UnsafeContainer 也是 Sync
// 注意：这需要调用者正确使用
unsafe impl<T: Send + Sync> Sync for UnsafeContainer<T> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spin_lock() {
        let lock = SpinLock::new(0);

        {
            let mut guard = lock.lock();
            *guard += 1;
        }

        {
            let guard = lock.lock();
            assert_eq!(*guard, 1);
        }
    }

    #[test]
    fn test_counter() {
        let counter = AtomicCounter::new();

        let handles: Vec<_> = (0..10)
            .map(|_| {
                thread::spawn(move || {
                    for _ in 0..100 {
                        counter.increment();
                    }
                })
            })
            .collect();

        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(counter.get(), 1000);
    }
}
```

### 8.3 内存序选择指南

| 场景 | 推荐 Ordering | 说明 |
|-----|---------------|------|
| 计数器 | `Relaxed` | 不需要同步其他数据 |
| 标志位 | `Acquire`/`Release` | 需要看到之前的写入 |
| 初始化 | `SeqCst` | 确保全局顺序 |
| 锁 | `Acquire`/`Release` + fence | 标准锁语义 |

### 8.4 生产案例

- **`parking_lot`**: 高性能锁实现
- **`crossbeam`**: 无锁数据结构
- **`std::sync`**: 标准库同步原语

---

## 9. 未初始化内存

### 9.1 问题场景

当需要：

- 避免不必要的初始化开销
- 实现自定义容器
- 处理 C 库分配的未初始化内存
- 条件初始化

### 9.2 代码示例：MaybeUninit 模式

```rust
//! 未初始化内存处理
//! 运行: cargo +nightly miri test -- maybe_uninit

use std::mem::{self, MaybeUninit};

/// 危险等级: 🔴 高
///
/// 使用 MaybeUninit 实现固定大小的栈数组
pub struct ArrayVec<T, const N: usize> {
    // 未初始化的存储
    storage: [MaybeUninit<T>; N],
    len: usize,
}

impl<T, const N: usize> ArrayVec<T, N> {
    pub fn new() -> Self {
        // SAFETY: MaybeUninit 不需要初始化
        Self {
            storage: unsafe { MaybeUninit::uninit().assume_init() },
            len: 0,
        }
    }

    pub fn push(&mut self, value: T) -> Result<(), T> {
        if self.len >= N {
            return Err(value);
        }

        // 在未初始化位置写入
        self.storage[self.len].write(value);
        self.len += 1;

        Ok(())
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;

        // SAFETY: 该位置的值已初始化
        Some(unsafe { self.storage[self.len].assume_init_read() })
    }

    pub fn as_slice(&self) -> &[T] {
        // SAFETY: 0..len 范围内的元素都已初始化
        unsafe {
            std::slice::from_raw_parts(
                self.storage.as_ptr() as *const T,
                self.len,
            )
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }
}

impl<T, const N: usize> Drop for ArrayVec<T, N> {
    fn drop(&mut self) {
        // 只 drop 已初始化的元素
        for i in 0..self.len {
            // SAFETY: 0..len 范围内的元素都已初始化
            unsafe {
                self.storage[i].assume_init_drop();
            }
        }
    }
}

// SAFETY: ArrayVec 的行为类似于 Vec
unsafe impl<T: Send, const N: usize> Send for ArrayVec<T, N> {}
unsafe impl<T: Sync, const N: usize> Sync for ArrayVec<T, N> {}

/// 条件初始化模式
pub fn conditional_init(condition: bool) -> i32 {
    // SAFETY: MaybeUninit 创建未初始化值是安全的
    let mut value = MaybeUninit::<i32>::uninit();

    if condition {
        value.write(42);
    } else {
        value.write(0);
    }

    // SAFETY: 我们确保在所有分支都写入了值
    unsafe { value.assume_init() }
}

/// 批量初始化模式
pub fn batch_init<const N: usize>() -> [String; N] {
    // 创建未初始化数组
    let mut arr: [MaybeUninit<String>; N] =
        unsafe { MaybeUninit::uninit().assume_init() };

    // 初始化计数器，用于出错时清理
    let mut initialized = 0;

    for i in 0..N {
        // 可能 panic 的初始化
        let value = format!("element {}", i);
        arr[i].write(value);
        initialized += 1;
    }

    // 使用 ManuallyDrop 防止在转换期间 drop
    let mut arr = mem::ManuallyDrop::new(arr);

    // SAFETY: 所有元素都已初始化
    unsafe {
        mem::transmute_copy::<_, [String; N]>(&*arr)
    }
}

/// ❌ 错误：读取未初始化内存
fn read_uninit_bug() {
    let x: i32;
    // let y = x;  // 编译错误：使用未初始化变量

    let mut mu = MaybeUninit::<i32>::uninit();
    let ptr = mu.as_mut_ptr();
    // UB: 读取未初始化值
    // let val = unsafe { ptr.read() };
}

/// ✅ 修复：先写入再读取
fn fixed_read_uninit() {
    let mut mu = MaybeUninit::<i32>::uninit();
    mu.write(42);
    let val = unsafe { mu.assume_init() };  // 安全
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_array_vec() {
        let mut vec = ArrayVec::<i32, 5>::new();

        assert!(vec.push(1).is_ok());
        assert!(vec.push(2).is_ok());
        assert!(vec.push(3).is_ok());

        assert_eq!(vec.as_slice(), &[1, 2, 3]);

        assert_eq!(vec.pop(), Some(3));
        assert_eq!(vec.pop(), Some(2));
    }

    #[test]
    fn test_conditional_init() {
        assert_eq!(conditional_init(true), 42);
        assert_eq!(conditional_init(false), 0);
    }
}
```

### 9.3 MaybeUninit 方法选择指南

| 方法 | 用途 | 安全要求 |
|-----|------|---------|
| `uninit()` | 创建未初始化 | 总是安全 |
| `write()` | 写入值 | 位置未初始化或已 drop |
| `assume_init()` | 转为 T（消耗） | 值已初始化 |
| `assume_init_ref()` | 获取 &T | 值已初始化 |
| `assume_init_mut()` | 获取 &mut T | 值已初始化 |
| `assume_init_read()` | 复制值（不消耗） | 值已初始化 |
| `assume_init_drop()` | 执行 drop | 值已初始化 |

### 9.4 生产案例

- **`Vec<T>`**: 使用 MaybeUninit 管理容量
- **`Box::new_uninit`**: 标准库未初始化分配
- **`Read::read`**: 读取到未初始化缓冲区

---

## 10. 静态可变状态

### 10.1 问题场景

当需要：

- 全局配置
- 单例模式
- 缓存
- 线程局部存储

### 10.2 代码示例：安全初始化模式

```rust
//! 静态可变状态管理
//! 运行: cargo +nightly miri test -- static_state

use std::cell::UnsafeCell;
use std::mem::MaybeUninit;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{LazyLock, Mutex, OnceLock, RwLock};

// ============================================================================
// OnceLock 模式（推荐）
// ============================================================================

static CONFIG: OnceLock<AppConfig> = OnceLock::new();

#[derive(Debug, Clone)]
pub struct AppConfig {
    pub database_url: String,
    pub port: u16,
}

pub fn init_config(config: AppConfig) -> Result<(), ()> {
    CONFIG.set(config).map_err(|_| ())
}

pub fn get_config() -> &'static AppConfig {
    CONFIG.get().expect("config not initialized")
}

// ============================================================================
// LazyLock 模式（Nightly）
// ============================================================================

static COUNTER: LazyLock<Mutex<u64>> = LazyLock::new(|| {
    println!("Initializing counter...");
    Mutex::new(0)
});

pub fn increment_global() -> u64 {
    let mut guard = COUNTER.lock().unwrap();
    *guard += 1;
    *guard
}

// ============================================================================
// 自定义 Once 模式（unsafe）
// ============================================================================

/// 危险等级: 🔴 高
///
/// 自定义线程安全的一次性初始化
pub struct StaticInit<T> {
    initialized: AtomicBool,
    value: UnsafeCell<MaybeUninit<T>>,
}

// SAFETY: StaticInit 使用原子操作确保线程安全
unsafe impl<T: Send + Sync> Send for StaticInit<T> {}
unsafe impl<T: Send + Sync> Sync for StaticInit<T> {}

impl<T> StaticInit<T> {
    pub const fn new() -> Self {
        Self {
            initialized: AtomicBool::new(false),
            value: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    /// 初始化值
    ///
    /// # Safety
    /// 只能调用一次，且必须在任何 get 之前
    pub unsafe fn init(&self, value: T) {
        if self.initialized.swap(true, Ordering::SeqCst) {
            panic!("StaticInit already initialized");
        }

        // SAFETY: 我们是第一个初始化者
        unsafe {
            (*self.value.get()).write(value);
        }
    }

    /// 获取已初始化的值
    pub fn get(&self) -> Option<&T> {
        if self.initialized.load(Ordering::Acquire) {
            // SAFETY: 值已初始化
            Some(unsafe { (*self.value.get()).assume_init_ref() })
        } else {
            None
        }
    }
}

impl<T> Drop for StaticInit<T> {
    fn drop(&mut self) {
        if *self.initialized.get_mut() {
            // SAFETY: 值已初始化
            unsafe {
                (*self.value.get()).assume_init_drop();
            }
        }
    }
}

static CUSTOM_INIT: StaticInit<String> = StaticInit::new();

// ============================================================================
// 线程局部存储
// ============================================================================

thread_local! {
    static THREAD_DATA: std::cell::RefCell<Vec<i32>> = std::cell::RefCell::new(Vec::new());
}

pub fn add_to_thread_local(value: i32) {
    THREAD_DATA.with(|data| {
        data.borrow_mut().push(value);
    });
}

pub fn get_thread_local_sum() -> i32 {
    THREAD_DATA.with(|data| {
        data.borrow().iter().sum()
    })
}

// ============================================================================
// 常见错误示例
// ============================================================================

/// ❌ 错误：直接修改 static mut
static mut GLOBAL_VALUE: i32 = 0;

fn unsafe_modify_static() {
    // UB 风险：数据竞争
    unsafe {
        GLOBAL_VALUE += 1;
    }
}

/// ✅ 修复：使用 Mutex
static SAFE_GLOBAL: Mutex<i32> = Mutex::new(0);

fn safe_modify_static() {
    let mut guard = SAFE_GLOBAL.lock().unwrap();
    *guard += 1;
}

/// ❌ 错误：双重初始化
fn double_init_bug() {
    // CONFIG.set(...).ok();
    // CONFIG.set(...).ok();  // 第二次设置会失败但代码继续
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lazy_lock() {
        let v1 = increment_global();
        let v2 = increment_global();
        assert_eq!(v2, v1 + 1);
    }

    #[test]
    fn test_thread_local() {
        add_to_thread_local(10);
        add_to_thread_local(20);
        assert_eq!(get_thread_local_sum(), 30);
    }
}
```

### 10.3 初始化模式对比

| 模式 | 线程安全 | 性能 | 复杂度 | 推荐场景 |
|-----|---------|------|--------|---------|
| `OnceLock` | 是 | 好 | 低 | 大多数场景 |
| `LazyLock` | 是 | 好 | 低 | 需要延迟计算 |
| `lazy_static!` | 是 | 一般 | 低 | 旧代码兼容 |
| 自定义 | 需验证 | 可优化 | 高 | 极端性能需求 |

### 10.4 生产案例

- **`log` crate**: 全局 logger 配置
- **`tokio`**: 运行时全局状态
- **`lazy_static`**: 广泛使用的延迟初始化

---

## 11. 契约和不变式

### 11.1 问题场景

所有 unsafe 代码都需要：

- 明确的安全契约
- 不变式的文档化
- 前置/后置条件的验证

### 11.2 代码示例：契约验证模式

```rust
//! 契约和不变式文档化
//! 运行: cargo +nightly miri test -- contracts

use std::ptr::NonNull;

/// 危险等级: 🔴 极高
///
/// 带完整契约注释的 unsafe 函数
///
/// # Safety
///
/// ## 前置条件
/// - `ptr` 必须指向有效的、已分配的内存块
/// - `ptr` 必须正确对齐到 `T`
/// - `len` 不能超过分配的内存大小
/// - 在返回切片生命周期内，内存必须保持有效
///
/// ## 后置条件
/// - 返回的切片长度等于 `len`
/// - 返回的切片包含 `len` 个有效初始化的 `T` 值
///
/// ## 不变式
/// - 切片内的所有元素都是有效的 `T` 实例
///
/// # 示例
/// ```
/// let vec = vec![1, 2, 3];
/// let ptr = vec.as_ptr();
/// let len = vec.len();
/// std::mem::forget(vec);  // 防止 double free
///
/// unsafe {
///     let slice = slice_from_raw_parts_verified(ptr, len);
///     assert_eq!(slice, &[1, 2, 3]);
/// }
/// ```
unsafe fn slice_from_raw_parts_verified<T>(ptr: *const T, len: usize) -> &'static [T] {
    // 前置条件验证
    assert!(!ptr.is_null(), "ptr must not be null");
    assert!(ptr.is_aligned(), "ptr must be aligned");
    assert!(len < isize::MAX as usize, "len must be less than isize::MAX");

    // 可选：在 debug 模式下额外检查
    #[cfg(debug_assertions)]
    {
        // 检查可读性（平台相关）
        // std::ptr::read_volatile(ptr);
    }

    // SAFETY: 所有前置条件已验证
    unsafe { std::slice::from_raw_parts(ptr, len) }
}

/// 运行时不变式检查结构体
pub struct InvariantChecked<T> {
    value: T,
    validator: fn(&T) -> bool,
}

impl<T> InvariantChecked<T> {
    /// 创建带不变式检查的值
    ///
    /// # Panics
    /// 如果初始值违反不变式则 panic
    pub fn new(value: T, validator: fn(&T) -> bool) -> Self {
        assert!(
            validator(&value),
            "Initial value violates invariant"
        );
        Self { value, validator }
    }

    pub fn get(&self) -> &T {
        &self.value
    }

    /// 修改值，保持不变式
    ///
    /// # Panics
    /// 如果新值违反不变式则 panic，原值保持不变
    pub fn modify<F>(&mut self, f: F)
    where
        F: FnOnce(&mut T),
    {
        let mut new_value = unsafe {
            // SAFETY: 我们即将验证并可能丢弃
            std::ptr::read(&self.value)
        };

        f(&mut new_value);

        if (self.validator)(&new_value) {
            // 验证通过，提交更改
            std::mem::drop(std::mem::replace(&mut self.value, new_value));
        } else {
            // 验证失败，丢弃新值，保持原值
            std::mem::drop(new_value);
            panic!("Modification violates invariant");
        }
    }
}

impl<T> Drop for InvariantChecked<T> {
    fn drop(&mut self) {
        // 最终不变式检查
        debug_assert!(
            (self.validator)(&self.value),
            "Invariant violated before drop"
        );
    }
}

/// 调试断言宏，用于 unsafe 契约
#[macro_export]
macro_rules! unsafe_assert {
    ($condition:expr, $msg:expr) => {
        debug_assert!($condition, concat!("Safety contract violation: ", $msg));
        if cfg!(debug_assertions) && !($condition) {
            panic!("Safety contract violation in unsafe code");
        }
    };
}

/// 使用契约验证的示例
pub struct SafeBuffer {
    ptr: NonNull<u8>,
    len: usize,
    capacity: usize,
}

impl SafeBuffer {
    /// # Safety
    /// - ptr 必须是通过标准分配器分配的
    /// - len <= capacity
    /// - capacity > 0
    pub unsafe fn from_raw_parts(
        ptr: NonNull<u8>,
        len: usize,
        capacity: usize,
    ) -> Self {
        unsafe_assert!(!ptr.as_ptr().is_null(), "ptr must not be null");
        unsafe_assert!(len <= capacity, "len must be <= capacity");
        unsafe_assert!(capacity > 0, "capacity must be > 0");
        unsafe_assert!(ptr.as_ptr().is_aligned(), "ptr must be aligned");

        Self { ptr, len, capacity }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn capacity(&self) -> usize {
        self.capacity
    }
}

/// 文档化 UB 边界
///
/// 以下操作会导致 UB：
/// 1. 使用 null 指针创建
/// 2. len > capacity
/// 3. 使用未对齐的指针
/// 4. 指针来自不同的分配

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_invariant_checked() {
        let mut val = InvariantChecked::new(10, |v| *v > 0);
        assert_eq!(*val.get(), 10);

        val.modify(|v| *v = 20);
        assert_eq!(*val.get(), 20);
    }

    #[test]
    #[should_panic]
    fn test_invariant_violation() {
        let mut val = InvariantChecked::new(10, |v| *v > 0);
        val.modify(|v| *v = -5);  // 违反不变式
    }
}
```

### 11.3 契约文档模板

```rust
/// # Safety
///
/// ## 前置条件
/// 1. 条件 1
/// 2. 条件 2
///
/// ## 后置条件
/// 1. 结果保证
///
/// ## 不变式
/// - 调用前后保持的属性
///
/// ## 违反后果
/// - 违反条件 1: 未定义行为（空指针解引用）
/// - 违反条件 2: 数据竞争
```

### 11.4 生产案例

- **`std` 标准库**: 所有 unsafe 函数都有详细的安全文档
- **`hashbrown`**: 每个 unsafe 块都有 SAFETY 注释
- **`tokio`**: 复杂的不变式系统

---

## 12. UB 分类速查表

### 12.1 未定义行为分类

| 类别 | 示例 | 检测方式 |
|-----|------|---------|
| **内存访问** | 使用已释放内存、越界访问 | Miri, ASan |
| **对齐违规** | 未对齐的原始指针解引用 | Miri, 硬件异常 |
| **类型违规** | 错误的 enum 值、无效 bool | Miri, 断言 |
| **并发违规** | 数据竞争 | Miri, TSan |
| **生命周期违规** | 悬垂引用 | Borrow Checker |
| **FFI 违规** | Panic 跨越边界 | 文档审查 |

### 12.2 Miri 错误解读

```text
error: Undefined Behavior: attempting a write access using <TAG> at <ADDR>,
       but that tag only grants SharedReadOnly permission

解释：违反了 Stacked Borrows 规则，试图写入只读引用
修复：检查指针别名，确保可变引用是独占的
```

```text
error: Undefined Behavior: using uninitialized data

解释：读取了未初始化的内存
修复：使用 MaybeUninit 或确保完全初始化
```

```text
error: Undefined Behavior: trying to reborrow for SharedReadOnly,
       but parent tag <TAG> does not have an appropriate item in the borrow stack

解释：父引用已失效
修复：检查引用生命周期，避免过早 drop
```

### 12.3 调试技巧

```bash
# 启用详细输出
MIRIFLAGS="-Zmiri-backtrace=full" cargo +nightly miri test

# 检查特定测试
MIRIFLAGS="-Zmiri-disable-isolation" cargo +nightly miri test -- test_name

# 忽略某些检查（仅用于隔离问题）
MIRIFLAGS="-Zmiri-disable-stacked-borrows" cargo +nightly miri test
```

---

## 13. Rustonomicon 章节映射

| 本指南章节 | Rustonomicon 对应章节 |
|-----------|---------------------|
| 2. 原始指针 | [Chapter 1: Introduction](https://doc.rust-lang.org/nomicon/index.html) |
| 3. 自引用 | [Chapter 4: Ownership and Lifetimes](https://doc.rust-lang.org/nomicon/lifetimes.html) |
| 4. Drop 管理 | [Chapter 7: Ownership Based Resource Management](https://doc.rust-lang.org/nomicon/obrm.html) |
| 5. Union | [Chapter 9: Type Layout](https://doc.rust-lang.org/nomicon/other-reprs.html) |
| 6. FFI | [Chapter 3: FFI](https://doc.rust-lang.org/nomicon/ffi.html) |
| 7. SIMD | [Chapter 10: Implementing Vec](https://doc.rust-lang.org/nomicon/vec/vec.html) |
| 8. 并发 | [Chapter 8: Concurrency](https://doc.rust-lang.org/nomicon/concurrency.html) |
| 9. MaybeUninit | [Chapter 12: Unchecked](https://doc.rust-lang.org/nomicon/unchecked-uninit.html) |

---

## 附录：Miri 完整配置

### `.cargo/config.toml` 示例

```toml
[target.'cfg(all())']
rustflags = ["-Z", "miri-disable-isolation"]

[env]
RUST_BACKTRACE = "1"
```

### GitHub Actions 配置

```yaml
name: Miri Test

on: [push, pull_request]

jobs:
  miri:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Install Miri
        run: |
          rustup toolchain install nightly --component miri
          rustup override set nightly
          cargo miri setup
      - name: Test with Miri
        run: cargo miri test
```

---

## 总结

编写安全的 Unsafe Rust 代码需要：

1. **最小化 unsafe 范围**: 只将必要的代码放在 unsafe 块中
2. **完整文档化**: 每个 unsafe 块都需要 SAFETY 注释
3. **使用 Miri 验证**: 定期运行 `cargo miri test`
4. **理解 UB**: 清楚知道什么是未定义行为
5. **维护不变式**: 确保所有安全契约都被满足

### 危险等级总结

| 等级 | 模式 | 风险 |
|-----|------|------|
| 🔴 极高 | 自引用、并发原语 | 极难调试，可能隐藏多年 |
| 🔴 高 | 自定义 Drop、Union、MaybeUninit | 容易引入内存错误 |
| ⚠️ 中 | 原始指针、FFI、SIMD | 相对容易检测和修复 |
| ℹ️ 低 | 静态初始化 | 通常有安全封装 |

---

*最后更新: 2026-02-28*
*维护者: Rust 学习项目*
*许可证: MIT OR Apache-2.0*
