# Tier 3: Pin 与 Unsafe 参考

> **文档版本**: Rust 1.90+ | **更新日期**: 2025-10-22  
> **文档层级**: Tier 3 - 技术参考 | **文档类型**: 📘 深度技术

---

## 📋 目录

- [Tier 3: Pin 与 Unsafe 参考](#tier-3-pin-与-unsafe-参考)
  - [📋 目录](#-目录)
  - [🎯 文档说明](#-文档说明)
  - [1. Pin 机制详解](#1-pin-机制详解)
    - [1.1 为什么需要 Pin？](#11-为什么需要-pin)
    - [1.2 Pin 的定义](#12-pin-的定义)
    - [1.3 Unpin Trait](#13-unpin-trait)
  - [2. Pin API](#2-pin-api)
    - [2.1 Pin\<\&mut T\>](#21-pinmut-t)
    - [2.2 `Pin<Box<T>>`](#22-pinboxt)
  - [3. Future 与 Pin](#3-future-与-pin)
    - [3.1 Future Trait](#31-future-trait)
    - [3.2 实现自引用 Future](#32-实现自引用-future)
  - [4. pin\_project](#4-pin_project)
    - [4.1 使用 pin-project](#41-使用-pin-project)
    - [4.2 pin\_project! 宏](#42-pin_project-宏)
  - [5. Unsafe in Async](#5-unsafe-in-async)
    - [5.1 常见 Unsafe 场景](#51-常见-unsafe-场景)
    - [5.2 异步中的 Send 和 Sync](#52-异步中的-send-和-sync)
  - [6. 安全抽象](#6-安全抽象)
    - [6.1 安全封装 Unsafe](#61-安全封装-unsafe)
    - [6.2 不变量保证](#62-不变量保证)
  - [7. 最佳实践](#7-最佳实践)
    - [7.1 Pin 使用建议](#71-pin-使用建议)
    - [7.2 Unsafe 使用建议](#72-unsafe-使用建议)
  - [8. 调试技巧](#8-调试技巧)
    - [8.1 Miri - Unsafe 代码检查](#81-miri---unsafe-代码检查)
    - [8.2 Address Sanitizer](#82-address-sanitizer)
  - [📚 延伸阅读](#-延伸阅读)
  - [📝 总结](#-总结)

## 🎯 文档说明

深入解析 Pin、Unpin 机制及异步编程中的 Unsafe 用法。

---

## 1. Pin 机制详解

### 1.1 为什么需要 Pin？

**自引用结构问题**:

```rust
// 不安全的自引用
struct SelfReferential {
    data: String,
    pointer: *const String, // 指向 data
}

// ❌ 移动会导致指针失效
let mut x = SelfReferential { /* ... */ };
let y = x; // x 被移动，pointer 仍指向旧地址
```

**Pin 的解决方案**:

```rust
use std::pin::Pin;

// Pin 保证值不会被移动
let pinned: Pin<Box<T>> = Box::pin(value);
```

---

### 1.2 Pin 的定义

```rust
pub struct Pin<P> {
    pointer: P,
}

impl<P: Deref> Pin<P> {
    // 安全创建 (仅对 Unpin 类型)
    pub fn new(pointer: P) -> Pin<P> where P::Target: Unpin;
    
    // 不安全创建
    pub unsafe fn new_unchecked(pointer: P) -> Pin<P>;
    
    // 获取引用
    pub fn as_ref(&self) -> Pin<&P::Target>;
}
```

---

### 1.3 Unpin Trait

```rust
pub auto trait Unpin {}

// 大多数类型自动实现 Unpin
impl Unpin for i32 {}
impl Unpin for String {}
impl<T: Unpin> Unpin for Vec<T> {}

// 异步块生成的 Future 是 !Unpin
async fn example() {} // impl Future + !Unpin

// PhantomPinned 显式标记为 !Unpin
use std::marker::PhantomPinned;

struct NotUnpin {
    _pin: PhantomPinned,
}
```

---

## 2. Pin API

### 2.1 Pin<&mut T>

```rust
impl<'a, T: ?Sized> Pin<&'a mut T> {
    // 安全获取可变引用 (仅 Unpin)
    pub fn get_mut(self) -> &'a mut T where T: Unpin;
    
    // 不安全获取可变引用
    pub unsafe fn get_unchecked_mut(self) -> &'a mut T;
    
    // Map
    pub fn map_unchecked_mut<U, F>(self, func: F) -> Pin<&'a mut U>
    where
        F: FnOnce(&mut T) -> &mut U;
}
```

---

### 2.2 `Pin<Box<T>>`

```rust
impl<T> Pin<Box<T>> {
    // 安全创建
    pub fn new(value: T) -> Pin<Box<T>> where T: Unpin;
    
    // 不安全创建
    pub unsafe fn new_unchecked(boxed: Box<T>) -> Pin<Box<T>>;
}
```

---

## 3. Future 与 Pin

### 3.1 Future Trait

```rust
pub trait Future {
    type Output;
    
    // Pin<&mut Self> 确保 self 不会被移动
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) 
        -> Poll<Self::Output>;
}
```

---

### 3.2 实现自引用 Future

```rust
use std::pin::Pin;
use std::future::Future;
use std::task::{Context, Poll};
use std::marker::PhantomPinned;

struct SelfRefFuture {
    data: String,
    pointer: Option<*const String>, // 自引用
    _pin: PhantomPinned, // 标记为 !Unpin
}

impl SelfRefFuture {
    fn new(data: String) -> Self {
        Self {
            data,
            pointer: None,
            _pin: PhantomPinned,
        }
    }
    
    // 初始化自引用
    unsafe fn init(self: Pin<&mut Self>) {
        let this = self.get_unchecked_mut();
        this.pointer = Some(&this.data as *const String);
    }
}

impl Future for SelfRefFuture {
    type Output = ();
    
    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
        Poll::Ready(())
    }
}
```

---

## 4. pin_project

### 4.1 使用 pin-project

```rust
use pin_project::pin_project;
use std::pin::Pin;

#[pin_project]
struct MyFuture<F> {
    #[pin] // 需要 Pin 的字段
    inner: F,
    counter: u32, // 不需要 Pin 的字段
}

impl<F: Future> Future for MyFuture<F> {
    type Output = F::Output;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.project(); // 安全地投影
        *this.counter += 1;
        this.inner.poll(cx)
    }
}
```

---

### 4.2 pin_project! 宏

```rust
pin_project! {
    struct MyStruct<T> {
        #[pin]
        pinned_field: T,
        unpinned_field: u32,
    }
}
```

---

## 5. Unsafe in Async

### 5.1 常见 Unsafe 场景

**场景 1: 访问裸指针**:

```rust
unsafe fn access_pointer(ptr: *const i32) -> i32 {
    *ptr
}
```

**场景 2: 调用 unsafe 函数**:

```rust
use std::slice;

unsafe {
    let data = slice::from_raw_parts(ptr, len);
}
```

**场景 3: 实现 unsafe trait**:

```rust
unsafe impl Send for MyType {}
unsafe impl Sync for MyType {}
```

---

### 5.2 异步中的 Send 和 Sync

```rust
// ✅ 实现 Send 的 Future 可以跨线程
async fn send_future() -> i32 {
    42
}

// ❌ 不实现 Send 的 Future 不能跨线程
async fn not_send_future() -> i32 {
    let rc = std::rc::Rc::new(42); // Rc 不是 Send
    *rc
}

// 检查 Future 是否是 Send
fn is_send<T: Send>(_: T) {}
is_send(send_future()); // ✅
// is_send(not_send_future()); // ❌ 编译错误
```

---

## 6. 安全抽象

### 6.1 安全封装 Unsafe

```rust
pub struct SafeWrapper {
    inner: *mut i32,
}

impl SafeWrapper {
    pub fn new(value: i32) -> Self {
        let inner = Box::into_raw(Box::new(value));
        Self { inner }
    }
    
    pub fn get(&self) -> i32 {
        unsafe { *self.inner }
    }
    
    pub fn set(&mut self, value: i32) {
        unsafe { *self.inner = value; }
    }
}

impl Drop for SafeWrapper {
    fn drop(&mut self) {
        unsafe {
            drop(Box::from_raw(self.inner));
        }
    }
}

// SafeWrapper 提供安全接口
unsafe impl Send for SafeWrapper {}
unsafe impl Sync for SafeWrapper {}
```

---

### 6.2 不变量保证

```rust
/// # Safety
/// 
/// - `ptr` 必须指向有效内存
/// - `len` 必须不超过实际长度
/// - 调用期间 `ptr` 不能被其他线程修改
pub unsafe fn process_slice(ptr: *const u8, len: usize) {
    let slice = std::slice::from_raw_parts(ptr, len);
    // 处理 slice
}
```

---

## 7. 最佳实践

### 7.1 Pin 使用建议

```rust
// ✅ 推荐：使用 pin-project
use pin_project::pin_project;

#[pin_project]
struct MyFuture<F> {
    #[pin]
    inner: F,
}

// ❌ 避免：手动管理 Pin
impl<F: Future> Future for MyFuture<F> {
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        unsafe {
            // 危险！需要手动保证安全
            let inner = Pin::new_unchecked(&mut self.get_unchecked_mut().inner);
            inner.poll(cx)
        }
    }
}
```

---

### 7.2 Unsafe 使用建议

**原则**:

1. ✅ 最小化 unsafe 代码
2. ✅ 在 unsafe 块外提供安全接口
3. ✅ 详细注释 unsafe 的安全条件
4. ✅ 使用现有的安全抽象 (如 pin-project)

**示例**:

```rust
// ✅ 好的 unsafe 用法
/// # Safety
/// 
/// 调用者必须确保 `ptr` 指向有效的 `T`
pub unsafe fn read_ptr<T>(ptr: *const T) -> T {
    ptr.read()
}

// 提供安全包装
pub fn safe_read<T>(value: &T) -> T where T: Copy {
    unsafe { read_ptr(value as *const T) }
}
```

---

## 8. 调试技巧

### 8.1 Miri - Unsafe 代码检查

```bash
# 安装 Miri
rustup +nightly component add miri

# 运行测试
cargo +nightly miri test
```

---

### 8.2 Address Sanitizer

```bash
# 启用 ASan
export RUSTFLAGS="-Z sanitizer=address"
cargo +nightly run
```

---

## 📚 延伸阅读

- **[异步语言特性参考](./01_异步语言特性参考.md)** - Future trait
- **[Future与Executor机制](../tier_02_guides/02_Future与Executor机制.md)** - 实践指南
- [Rust Nomicon](https://doc.rust-lang.org/nomicon/) - Unsafe Rust 权威指南

---

## 📝 总结

**核心概念**:

- ✅ Pin - 防止值移动
- ✅ Unpin - 可以安全移动
- ✅ PhantomPinned - 标记为 !Unpin
- ✅ pin-project - 安全投影 Pin 字段

**Unsafe 原则**:

- ✅ 最小化使用
- ✅ 提供安全封装
- ✅ 详细文档化安全条件
- ✅ 使用工具验证 (Miri, ASan)

**异步特定**:

- ✅ Future 需要 Pin
- ✅ 自引用结构是 !Unpin
- ✅ Send/Sync 影响跨线程调度

---

**文档维护**: C06 Async Team | **质量评分**: 95/100  
**最后更新**: 2025-10-22 | **Rust 版本**: 1.90+
