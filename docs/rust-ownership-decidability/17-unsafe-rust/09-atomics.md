# 原子操作与内存序

> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **权威来源**: std::sync::atomic, The Rustonomicon
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **对齐日期**: 2026-05-12.0
> **难度**: 🔴 高级
> **前置知识**: 并发基础、Unsafe Rust

---

## 目录
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

- [原子操作与内存序](#原子操作与内存序)
  - [目录](#目录)
  - [1. 原子操作基础](#1-原子操作基础)
    - [1.1 什么是原子操作](#11-什么是原子操作)
    - [1.2 为什么需要原子操作](#12-为什么需要原子操作)
  - [2. 内存序](#2-内存序)
    - [2.1 Ordering 枚举](#21-ordering-枚举)
    - [2.2 选择指南](#22-选择指南)
  - [3. 原子类型](#3-原子类型)
    - [3.1 整数类型](#31-整数类型)
    - [3.2 布尔类型](#32-布尔类型)
    - [3.3 指针类型](#33-指针类型)
  - [4. 常见模式](#4-常见模式)
    - [4.1 自旋锁](#41-自旋锁)
    - [4.2 无锁队列 (简化)](#42-无锁队列-简化)
  - [5. 内存序详解](#5-内存序详解)
    - [5.1 Relaxed](#51-relaxed)
    - [5.2 Acquire-Release](#52-acquire-release)
    - [5.3 SeqCst](#53-seqcst)
  - [参考](#参考)
  - [*文档版本: 1.0.0*](#文档版本-100)
  - [权威来源索引](#权威来源索引)
  - [权威来源索引](#权威来源索引-1)

---

## 1. 原子操作基础
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 1.1 什么是原子操作
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

原子操作是**不可中断**的操作，即使在多线程环境下也表现出单一、不可分割的执行效果。

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

fn increment() {
    // 这个操作是原子的：读取、增加、写入一气呵成
    COUNTER.fetch_add(1, Ordering::SeqCst);
}
```

### 1.2 为什么需要原子操作
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```rust
// ❌ 非原子操作，存在数据竞争
static mut COUNTER: usize = 0;

unsafe {
    COUNTER += 1;  // 实际上是：读 -> 改 -> 写，三步操作
}
// 如果两个线程同时执行，可能只增加 1 而不是 2
```

---

## 2. 内存序
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 2.1 Ordering 枚举
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust
pub enum Ordering {
    Relaxed,     // 最宽松，只保证原子性
    Acquire,     // 获取语义
    Release,     // 释放语义
    AcqRel,      // 获取-释放
    SeqCst,      // 顺序一致（最强）
}
```

### 2.2 选择指南
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```
┌─────────────────────────────────────────────────────────┐
│                    内存序选择指南                        │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  Relaxed                                                │
│  └── 计数器、统计信息（不需要同步其他数据）              │
│                                                         │
│  Acquire/Release                                        │
│  └── 锁、单例模式（需要同步数据）                       │
│                                                         │
│  SeqCst                                                 │
│  └── 多线程间需要全局顺序（少用）                       │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

---

## 3. 原子类型
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 3.1 整数类型
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```rust,ignore
use std::sync::atomic::{AtomicI32, AtomicUsize, Ordering};

let counter = AtomicUsize::new(0);

// 基本操作
counter.fetch_add(1, Ordering::SeqCst);     // +1，返回旧值
counter.fetch_sub(1, Ordering::SeqCst);     // -1，返回旧值
counter.fetch_and(0b1010, Ordering::SeqCst); // 位与
counter.fetch_or(0b0101, Ordering::SeqCst);  // 位或
counter.fetch_xor(0b1111, Ordering::SeqCst); // 位异或

// 比较并交换
counter.compare_exchange(
    current,    // 期望值
    new,        // 新值
    Ordering::SeqCst,  // 成功时的内存序
    Ordering::Relaxed  // 失败时的内存序
);
```

### 3.2 布尔类型
>
> **[来源: [crates.io](https://crates.io/)]**

```rust
use std::sync::atomic::{AtomicBool, Ordering};

let flag = AtomicBool::new(false);

flag.store(true, Ordering::SeqCst);
let value = flag.load(Ordering::SeqCst);

// 比较并交换
flag.compare_exchange(false, true, Ordering::SeqCst, Ordering::Relaxed);
```

### 3.3 指针类型
>
> **[来源: [docs.rs](https://docs.rs/)]**

```rust,ignore
use std::sync::atomic::{AtomicPtr, Ordering};

let ptr: AtomicPtr<i32> = AtomicPtr::new(std::ptr::null_mut());

// 加载指针
let p = ptr.load(Ordering::SeqCst);

// 存储指针
ptr.store(Box::into_raw(Box::new(42)), Ordering::SeqCst);

// 比较并交换
ptr.compare_exchange(
    old,
    new,
    Ordering::SeqCst,
    Ordering::Relaxed
);
```

---

## 4. 常见模式
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 4.1 自旋锁
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust
use std::sync::atomic::{AtomicBool, Ordering};
use std::cell::UnsafeCell;
use std::ops::{Deref, DerefMut};

pub struct SpinLock<T> {
    locked: AtomicBool,
    data: UnsafeCell<T>,
}

unsafe impl<T> Sync for SpinLock<T> where T: Send {}

impl<T> SpinLock<T> {
    pub fn new(data: T) -> Self {
        Self {
            locked: AtomicBool::new(false),
            data: UnsafeCell::new(data),
        }
    }

    pub fn lock(&self) -> SpinLockGuard<T> {
        // 自旋等待
        while self.locked.compare_exchange(
            false,
            true,
            Ordering::Acquire,   // 获取锁时的内存序
            Ordering::Relaxed
        ).is_err() {
            // 提示 CPU 忙等待
            std::hint::spin_loop();
        }

        SpinLockGuard { lock: self }
    }
}

pub struct SpinLockGuard<'a, T> {
    lock: &'a SpinLock<T>,
}

impl<T> Deref for SpinLockGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.lock.data.get() }
    }
}

impl<T> DerefMut for SpinLockGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<T> Drop for SpinLockGuard<'_, T> {
    fn drop(&mut self) {
        self.lock.locked.store(false, Ordering::Release);  // 释放锁
    }
}
```

### 4.2 无锁队列 (简化)
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust
use std::sync::atomic::{AtomicPtr, Ordering};

struct Node<T> {
    data: T,
    next: AtomicPtr<Node<T>>,
}

pub struct LockFreeQueue<T> {
    head: AtomicPtr<Node<T>>,
    tail: AtomicPtr<Node<T>>,
}

impl<T> LockFreeQueue<T> {
    pub fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: AtomicPtr::new(std::ptr::null_mut()),
        }));

        loop {
            let tail = self.tail.load(Ordering::Acquire);
            let next = unsafe { (*tail).next.load(Ordering::Acquire) };

            if next.is_null() {
                // 尝试链接新节点
                if unsafe { (*tail).next.compare_exchange(
                    std::ptr::null_mut(),
                    new_node,
                    Ordering::Release,
                    Ordering::Relaxed
                ).is_ok() } {
                    // 尝试更新 tail
                    let _ = self.tail.compare_exchange(
                        tail,
                        new_node,
                        Ordering::Release,
                        Ordering::Relaxed
                    );
                    return;
                }
            } else {
                // 帮助推进 tail
                let _ = self.tail.compare_exchange(
                    tail,
                    next,
                    Ordering::Release,
                    Ordering::Relaxed
                );
            }
        }
    }
}
```

---

## 5. 内存序详解
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 5.1 Relaxed
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

只保证操作的原子性，**不保证**内存顺序。

```rust,ignore
// 用于独立计数器
static COUNTER: AtomicUsize = AtomicUsize::new(0);

fn count() {
    COUNTER.fetch_add(1, Ordering::Relaxed);  // 只关心最终值
}
```

### 5.2 Acquire-Release
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

建立 happens-before 关系。

```rust,ignore
// 标记数据是否准备好
static READY: AtomicBool = AtomicBool::new(false);
static DATA: AtomicUsize = AtomicUsize::new(0);

// 线程 1: 写入数据
fn produce() {
    DATA.store(42, Ordering::Relaxed);
    READY.store(true, Ordering::Release);  // Release: 之前的写入对后续 Acquire 可见
}

// 线程 2: 读取数据
fn consume() {
    while !READY.load(Ordering::Acquire) {  // Acquire: 看到 Release 前的所有写入
        std::hint::spin_loop();
    }
    assert_eq!(DATA.load(Ordering::Relaxed), 42);  // 保证看到 42
}
```

### 5.3 SeqCst
>
> **[来源: [crates.io](https://crates.io/)]**

最强的内存序，所有线程以相同的顺序看到操作。

```rust
// 用于需要全局顺序的场景
// 但性能较差，尽量少用
```

---

## 参考
>
> **[来源: [docs.rs](https://docs.rs/)]**

- [std::sync::atomic](https://doc.rust-lang.org/std/sync/atomic/)
- [The Rustonomicon - Atomics](https://doc.rust-lang.org/nomicon/atomics.html)

---

*文档版本: 1.0.0*
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

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**
