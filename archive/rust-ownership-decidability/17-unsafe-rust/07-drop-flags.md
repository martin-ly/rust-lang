# Drop 检查与析构安全

> **内容分级**: [归档级]
>
> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **Rust 版本**: 1.96.0+ (Edition 2024)
> **对齐日期**: 2026-05-12.0
> **难度**: 🔴 高级
> **前置知识**: 生命周期、泛型

---

## 目录
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

- [Drop 检查与析构安全](#drop-检查与析构安全)
  - [目录](#目录)
  - [1. Drop Trait 基础](#1-drop-trait-基础)
    - [1.1 什么是 Drop](#11-什么是-drop)
    - [1.2 Drop 顺序](#12-drop-顺序)
  - [2. Drop Check (dropck)](#2-drop-check-dropck)
    - [2.1 dropck 的目的](#21-dropck-的目的)
    - [2.2 规则解释](#22-规则解释)
    - [2.3 使用 PhantomData](#23-使用-phantomdata)
  - [3. 生命周期与 Drop](#3-生命周期与-drop)
    - [3.1 结构体生命周期](#31-结构体生命周期)
    - [3.2 泛型与 Drop](#32-泛型与-drop)
  - [4. 常见陷阱](#4-常见陷阱)
    - [4.1 双 Drop 风险](#41-双-drop-风险)
    - [4.2 遗忘 Drop](#42-遗忘-drop)
    - [4.3 循环引用与 Drop](#43-循环引用与-drop)
  - [5. 实战：实现安全容器](#5-实战实现安全容器)
  - [参考](#参考)
<a id="文档版本-100"></a>
  - [*文档版本: 1.0.0*](#文档版本-100)
  - [权威来源索引](#权威来源索引)

---

## 1. Drop Trait 基础
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

### 1.1 什么是 Drop
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

```rust
pub trait Drop {
    fn drop(&mut self);
}
```

Drop trait 在值离开作用域时自动调用。

```rust
struct HasDrop;

impl Drop for HasDrop {
    fn drop(&mut self) {
        println!("Dropping!");
    }
}

fn main() {
    let x = HasDrop;
    // x 在这里 drop，打印 "Dropping!"
}
```

### 1.2 Drop 顺序
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```rust
struct PrintOnDrop(&'static str);

impl Drop for PrintOnDrop {
    fn drop(&mut self) {
        println!("{}", self.0);
    }
}

fn main() {
    let _x = PrintOnDrop("last");
    let _y = PrintOnDrop("middle");
    let _z = PrintOnDrop("first");
    // 输出：
    // first
    // middle
    // last
}
```

**规则**: 与创建顺序相反（LIFO）。

---

## 2. Drop Check (dropck)
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 2.1 dropck 的目的
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

确保在 Drop 实现中访问的引用总是有效的。

```rust,ignore
struct Inspector<'a>(&'a u8);

impl<'a> Drop for Inspector<'a> {
    fn drop(&mut self) {
        println!("{}", self.0);  // 使用引用
    }
}

fn main() {
    let (inspector, num);
    num = 1;
    inspector = Inspector(&num);
    // 编译错误！num 先 drop，但 inspector 的 drop 需要它
}
```

### 2.2 规则解释
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```
dropck 规则：
- 如果类型实现了 Drop，它的生命周期必须严格包含它引用的数据
- 这确保 drop 时引用的数据仍然有效
```

### 2.3 使用 PhantomData
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```rust
use std::marker::PhantomData;

struct Inspector<'a> {
    pointer: *const u8,
    _marker: PhantomData<&'a u8>,  // 假装拥有 &'a u8
}

impl<'a> Drop for Inspector<'a> {
    fn drop(&mut self) {
        unsafe {
            println!("{}", *self.pointer);
        }
    }
}

fn main() {
    let num = 1;
    let inspector = Inspector {
        pointer: &num,
        _marker: PhantomData,
    };
    // 现在编译通过！
}
```

---

## 3. 生命周期与 Drop
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### 3.1 结构体生命周期
>
> **[来源: [crates.io](https://crates.io/)]**

```rust
// 有生命周期参数的结构体
struct Container<'a, T: 'a> {
    data: &'a T,
}

// 如果实现 Drop，需要确保 'a 有效
impl<'a, T> Drop for Container<'a, T> {
    fn drop(&mut self) {
        // 可以安全使用 self.data，因为 'a 保证有效
    }
}
```

### 3.2 泛型与 Drop
>
> **[来源: [docs.rs](https://docs.rs/)]**

```rust
struct GenericDrop<T>(T);

impl<T> Drop for GenericDrop<T> {
    fn drop(&mut self) {
        // 即使 T 实现 Drop，这里也不会自动调用 T 的 drop
        // 因为 self.0 的所有权已经...等等，实际上会调用！
    }
}
```

**注意**: 结构体字段的 Drop 会自动调用。

---

## 4. 常见陷阱
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 4.1 双 Drop 风险
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust
struct DoubleDrop<T>(T);

impl<T> Drop for DoubleDrop<T> {
    fn drop(&mut self) {
        unsafe {
            std::ptr::drop_in_place(&mut self.0);
        }
        // 错误！self.0 会被再次 drop！
    }
}
```

**修正**:

```rust,ignore
impl<T> Drop for DoubleDrop<T> {
    fn drop(&mut self) {
        // 不要手动 drop，让编译器处理
    }
}
```

### 4.2 遗忘 Drop
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust
struct MustDrop<T>(T);

impl<T> MustDrop<T> {
    fn into_inner(self) -> T {
        let val = unsafe { std::ptr::read(&self.0) };
        std::mem::forget(self);  // 防止 drop
        val
    }
}

impl<T> Drop for MustDrop<T> {
    fn drop(&mut self) {
        // 清理逻辑
        println!("Cleaning up...");
    }
}
```

### 4.3 循环引用与 Drop
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```rust
use std::cell::RefCell;
use std::rc::Rc;

struct Node {
    next: RefCell<Option<Rc<Node>>>,
}

// 循环引用导致内存泄漏
fn create_cycle() {
    let a = Rc::new(Node { next: RefCell::new(None) });
    let b = Rc::new(Node { next: RefCell::new(None) });

    *a.next.borrow_mut() = Some(b.clone());
    *b.next.borrow_mut() = Some(a.clone());

    // 循环引用，Drop 不会被调用！
}
```

**解决方案**: 使用 `Weak` 指针。

---

## 5. 实战：实现安全容器
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```rust
use std::alloc::{alloc, dealloc, Layout};
use std::marker::PhantomData;
use std::ptr::NonNull;

/// 一个安全的堆数组，正确处理 Drop
pub struct SafeArray<T> {
    ptr: NonNull<T>,
    len: usize,
    cap: usize,
    _marker: PhantomData<T>,
}

impl<T> SafeArray<T> {
    pub fn new() -> Self {
        Self {
            ptr: NonNull::dangling(),
            len: 0,
            cap: 0,
            _marker: PhantomData,
        }
    }

    pub fn push(&mut self, value: T) {
        if self.len == self.cap {
            self.grow();
        }

        unsafe {
            self.ptr.as_ptr().add(self.len).write(value);
        }
        self.len += 1;
    }

    fn grow(&mut self) {
        // 实现省略...
    }
}

// 关键：正确处理 Drop
impl<T> Drop for SafeArray<T> {
    fn drop(&mut self) {
        if self.cap == 0 {
            return;
        }

        // 1. 析构所有元素
        for i in 0..self.len {
            unsafe {
                std::ptr::drop_in_place(self.ptr.as_ptr().add(i));
            }
        }

        // 2. 释放内存
        unsafe {
            dealloc(
                self.ptr.as_ptr() as *mut u8,
                Layout::array::<T>(self.cap).unwrap()
            );
        }
    }
}

// 关键：正确标记 Send/Sync
unsafe impl<T: Send> Send for SafeArray<T> {}
unsafe impl<T: Sync> Sync for SafeArray<T> {}
```

---

## 参考
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [The Rustonomicon - Drop Check](https://doc.rust-lang.org/nomicon/dropck.html)
- [std::ops::Drop](https://doc.rust-lang.org/std/ops/trait.Drop.html)

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

- [README](../README.md)

---

## 权威来源索引

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
> **来源: [TRPL Ch. 4 - Ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)**
> **来源: [Rustonomicon - Ownership](https://doc.rust-lang.org/nomicon/ownership.html)**
> **来源: [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)**
> **来源: [Wikipedia - Undefined Behavior](https://en.wikipedia.org/wiki/Undefined_Behavior)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**
> **来源: [Rust Reference - Unsafe](https://doc.rust-lang.org/reference/unsafe-blocks.html)**
> **来源: [RFC 2585 - Unsafe Guidelines](https://rust-lang.github.io/rfcs/2585-unsafe-block-in-unsafe-fn.html)**

---
