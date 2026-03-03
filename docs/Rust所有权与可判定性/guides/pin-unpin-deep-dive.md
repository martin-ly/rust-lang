# Pin 与 Unpin 深度分析

## 目录

- [Pin 与 Unpin 深度分析](#pin-与-unpin-深度分析)
  - [目录](#目录)
  - [概述](#概述)
  - [1. 为什么需要Pin？](#1-为什么需要pin)
    - [1.1 自引用结构的问题](#11-自引用结构的问题)
    - [1.2 移动问题](#12-移动问题)
  - [2. Pin的核心概念](#2-pin的核心概念)
    - [2.1 Pin的语义](#21-pin的语义)
    - [2.2 PhantomPinned](#22-phantompinned)
  - [3. Pin API详解](#3-pin-api详解)
    - [3.1 创建Pin](#31-创建pin)
    - [3.2 安全操作](#32-安全操作)
    - [3.3 Unsafe操作](#33-unsafe操作)
  - [4. 实际使用模式](#4-实际使用模式)
    - [4.1 安全的自引用结构](#41-安全的自引用结构)
    - [4.2 实现Future](#42-实现future)
    - [4.3 异步块中的Pin](#43-异步块中的pin)
  - [5. Unpin trait](#5-unpin-trait)
    - [5.1 自动派生](#51-自动派生)
    - [5.2 手动实现](#52-手动实现)
  - [6. Pin投影](#6-pin投影)
    - [6.1 什么是投影？](#61-什么是投影)
    - [6.2 安全投影模式](#62-安全投影模式)
    - [6.3 pin-project crate](#63-pin-project-crate)
  - [7. 常见陷阱](#7-常见陷阱)
    - [7.1 错误：在Pin后修改](#71-错误在pin后修改)
    - [7.2 错误：`Pin<Box<T>>`后解引用](#72-错误pinboxt后解引用)
    - [7.3 正确：通过投影访问](#73-正确通过投影访问)
  - [8. 形式化语义](#8-形式化语义)
    - [8.1 Pin契约](#81-pin契约)
    - [8.2 与Drop的交互](#82-与drop的交互)
  - [9. 总结](#9-总结)
  - [参考](#参考)

## 概述

`Pin`是Rust标准库中的一个重要类型，用于处理**自引用结构**和**异步Future**。
理解Pin/Unpin对于编写异步代码和unsafe Rust至关重要。

---

## 1. 为什么需要Pin？

### 1.1 自引用结构的问题

```rust
struct SelfReferential {
    data: String,
    // 我们希望pointer指向data
    pointer: *const String,
}

impl SelfReferential {
    fn new() -> Self {
        let mut s = Self {
            data: String::from("hello"),
            pointer: std::ptr::null(),
        };
        s.pointer = &s.data;  // 设置自引用
        s
    }
}

fn main() {
    let s = SelfReferential::new();
    let s2 = s;  // 移动！pointer现在指向无效内存
    // s.data被移动到s2，但pointer仍指向旧位置
}
```

### 1.2 移动问题

Rust中大多数值可以被**移动**：

```rust
let x = String::from("hello");
let y = x;  // x被移动到y，内存地址可能改变
```

对于自引用结构，移动会导致内部指针失效。

---

## 2. Pin的核心概念

### 2.1 Pin的语义

```rust
pub struct Pin<P> {
    pointer: P,
}

// P通常是Box<T>, &mut T, Rc<T>等指针类型
```

`Pin<P>`保证：

- **如果T: !Unpin**，则T不会被移动
- **如果T: Unpin**，则Pin行为与普通指针相同

### 2.2 PhantomPinned

```rust
use std::marker::PhantomPinned;

struct MustNotMove {
    data: String,
    _pin: PhantomPinned,  // 标记为!Unpin
}

impl MustNotMove {
    fn new() -> Pin<Box<Self>> {
        Box::pin(Self {
            data: String::from("pinned"),
            _pin: PhantomPinned,
        })
    }
}
```

---

## 3. Pin API详解

### 3.1 创建Pin

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

struct PinnedData {
    data: String,
    self_ptr: *const String,
    _pin: PhantomPinned,
}

// 方式1: Box::pin (堆分配)
let pinned: Pin<Box<PinnedData>> = Box::pin(PinnedData {
    data: String::from("hello"),
    self_ptr: std::ptr::null(),
    _pin: PhantomPinned,
});

// 方式2: Pin::new (仅用于Unpin类型)
let unpin_data = 42;
let pinned: Pin<&i32> = Pin::new(&unpin_data);

// 方式3: Pin::new_unchecked (unsafe)
let mut data = String::from("unsafe");
let pinned: Pin<&mut String> = unsafe { Pin::new_unchecked(&mut data) };
```

### 3.2 安全操作

```rust
impl<P: Deref> Pin<P> {
    // 获取引用（总是安全）
    pub fn as_ref(&self) -> Pin<&P::Target>;

    // 获取可变引用（要求Target: Unpin）
    pub fn as_mut(&mut self) -> Pin<&mut P::Target>
    where P: DerefMut;
}

// 对于Unpin类型，可以获取可变引用
impl<P: DerefMut<Target: Unpin>> Pin<P> {
    pub fn get_mut(self) -> P;
    pub fn get_ref(self) -> P::Target;
}
```

### 3.3 Unsafe操作

```rust
impl<P: DerefMut> Pin<P> {
    /// # Safety
    /// 调用者必须保证不移动数据
    pub unsafe fn get_unchecked_mut(self) -> P;

    /// # Safety
    /// 调用者必须保证不违反Pin契约
    pub unsafe fn map_unchecked_mut<F, T>(self, f: F) -> Pin<&mut T>
    where F: FnOnce(&mut P::Target) -> &mut T;
}
```

---

## 4. 实际使用模式

### 4.1 安全的自引用结构

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;
use std::ptr::NonNull;

struct SelfRef {
    data: String,
    // 使用NonNull而不是&str，因为生命周期无法表达
    slice: NonNull<str>,
    _pin: PhantomPinned,
}

impl SelfRef {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::new(Self {
            data,
            // 临时值，将在下面设置
            slice: NonNull::dangling(),
            _pin: PhantomPinned,
        });

        // 获取指向data的指针
        let slice: NonNull<str> = NonNull::from(&boxed.data[..]);
        boxed.slice = slice;

        // 转换为Pin，防止移动
        Pin::from(boxed)
    }

    fn slice(self: Pin<&Self>) -> &str {
        // 安全：我们知道slice有效，且Pin保证不会移动
        unsafe { self.slice.as_ref() }
    }

    fn data(&self) -> &str {
        &self.data
    }
}
```

### 4.2 实现Future

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct MyFuture {
    state: State,
    // 可能包含自引用
}

enum State {
    Init,
    Waiting { buffer: String, position: usize },
    Done,
}

impl Future for MyFuture {
    type Output = String;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = unsafe { self.get_unchecked_mut() };

        match &mut this.state {
            State::Init => {
                this.state = State::Waiting {
                    buffer: String::new(),
                    position: 0,
                };
                cx.waker().wake_by_ref();
                Poll::Pending
            }
            State::Waiting { buffer, position } => {
                // 处理...
                if *position >= 10 {
                    this.state = State::Done;
                    Poll::Ready(buffer.clone())
                } else {
                    *position += 1;
                    Poll::Pending
                }
            }
            State::Done => panic!("Future polled after completion"),
        }
    }
}
```

### 4.3 异步块中的Pin

```rust
async fn async_with_pin() {
    let local = String::from("pinned data");

    // async块被转换为Future，包含local
    let future = async {
        // local在这里被存储在Future中
        println!("{}", local);

        // .await时，Future可能被Pin在堆上
        tokio::time::sleep(Duration::from_secs(1)).await;

        // local仍然有效，因为Pin保证不会移动
        println!("{}", local);
    };

    future.await;
}
```

---

## 5. Unpin trait

### 5.1 自动派生

```rust
// 大多数类型自动实现Unpin
struct MyStruct {
    data: i32,
    vec: Vec<u8>,
}
// 自动: impl Unpin for MyStruct {}

// 包含PhantomPinned的类型不实现Unpin
struct PinnedType {
    _pin: PhantomPinned,
}
// !Unpin
```

### 5.2 手动实现

```rust
use std::marker::Unpin;

struct Wrapper<T> {
    data: T,
}

// 无论T是否Unpin，Wrapper都是Unpin
impl<T> Unpin for Wrapper<T> {}

// 条件实现
struct Conditional<T, U> {
    t: T,
    u: U,
}

impl<T: Unpin, U: Unpin> Unpin for Conditional<T, U> {}
```

---

## 6. Pin投影

### 6.1 什么是投影？

```rust
struct Container {
    pinned_field: PinnedData,
    unpinned_field: i32,
}

// 需要获取Pin<&mut PinnedData>从Pin<&mut Container>
// 这称为"Pin投影"
```

### 6.2 安全投影模式

```rust
struct Container {
    pinned: PinnedData,
    unpinned: i32,
}

impl Container {
    // 投影到Pinned字段
    fn pinned(self: Pin<&mut Self>) -> Pin<&mut PinnedData> {
        // 安全：pinned字段从不移动
        unsafe { self.map_unchecked_mut(|s| &mut s.pinned) }
    }

    // 获取unpinned字段的可变引用
    fn unpinned_mut(self: Pin<&mut Self>) -> &mut i32 {
        // 安全：unpinned是Unpin
        unsafe { &mut self.get_unchecked_mut().unpinned }
    }
}
```

### 6.3 pin-project crate

```rust
use pin_project::pin_project;

#[pin_project]
struct Container {
    #[pin]
    pinned: PinnedData,
    unpinned: i32,
}

impl Container {
    fn method(self: Pin<&mut Self>) {
        let this = self.project();
        let pinned: Pin<&mut PinnedData> = this.pinned;
        let unpinned: &mut i32 = this.unpinned;
    }
}
```

---

## 7. 常见陷阱

### 7.1 错误：在Pin后修改

```rust
fn wrong() {
    let mut data = String::from("hello");
    let pinned = Pin::new(&mut data);

    // ❌ 错误：不能获取可变引用
    // pinned.get_mut().push_str(" world");
}
```

### 7.2 错误：`Pin<Box<T>>`后解引用

```rust
fn also_wrong() {
    let pinned: Pin<Box<String>> = Box::pin(String::from("hello"));

    // ❌ 错误：不能移动出Pin
    // let s = *pinned;
}
```

### 7.3 正确：通过投影访问

```rust
fn correct() {
    let mut pinned: Pin<Box<PinnedData>> = PinnedData::new();

    // ✅ 通过方法访问
    println!("{}", pinned.as_ref().slice());
}
```

---

## 8. 形式化语义

### 8.1 Pin契约

```text
Pin<P<T>> 保证:
    如果 T: !Unpin:
        - T的内存地址不会改变
        - T不会被移动
        - 直到Drop完成

    如果 T: Unpin:
        - 与普通指针相同
```

### 8.2 与Drop的交互

```rust
impl Drop for PinnedType {
    fn drop(&mut self) {
        // 即使类型是!Unpin，drop(&mut self)接收非Pin引用
        // 这是安全的，因为值不会再被使用
    }
}
```

---

## 9. 总结

| 概念 | 含义 |
|------|------|
| `Pin<P>` | 保证P指向的数据不会被移动（如果!Unpin） |
| Unpin | 标记trait，表示类型可以安全移动 |
| PhantomPinned | 标记类型为!Unpin |
| 投影 | 从`Pin<Container>`获取`Pin<Field>`|

使用场景：

- 异步Future实现
- 自引用数据结构
- 与C代码交互的固定缓冲区

---

## 参考

1. [std::pin documentation](https://doc.rust-lang.org/std/pin/index.html)
2. [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)
3. [Pin and Suffering](https://fasterthanli.me/articles/pin-and-suffering)
4. [pin-project crate](https://docs.rs/pin-project/)
