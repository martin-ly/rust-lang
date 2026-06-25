# 实战：实现 `Vec<T>`

> **内容分级**: [归档级]
>
> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **难度**: 🔴 高级
> **前置知识**: 所有 Unsafe Rust 主题
> **目标**: 从零实现一个安全的动态数组

---

## 目录
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

- [实战：实现 `Vec<T>`](#实战实现-vect)
  - [目录](#目录)
  - [1. 设计目标](#1-设计目标)
  - [2. 基本实现](#2-基本实现)
    - [2.1 结构定义与创建](#21-结构定义与创建)
    - [2.2 Push 操作](#22-push-操作)
    - [2.3 Pop 操作](#23-pop-操作)
    - [2.4 索引访问](#24-索引访问)
  - [3. Drop 实现](#3-drop-实现)
  - [4. 迭代器实现](#4-迭代器实现)
  - [5. 测试与验证](#5-测试与验证)
  - [6. Miri 验证](#6-miri-验证)
  - [完整代码](#完整代码)
  - [*最后更新: 2026-03-07*](#最后更新-2026-03-07)
  - [权威来源索引](#权威来源索引)

---

## 1. 设计目标
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

实现一个功能类似 `std::vec::Vec` 的安全动态数组：

```rust
pub struct MyVec<T> {
    ptr: *mut T,      // 指向堆内存的原始指针
    len: usize,       // 当前元素数量
    cap: usize,       // 容量
}
```

**要求**:

- 内存安全（无 use-after-free, 无泄漏）
- 支持 push/pop/index
- 正确处理泛型类型 T

---

## 2. 基本实现
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

### 2.1 结构定义与创建
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```rust
use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
use std::mem::MaybeUninit;
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::ptr::NonNull;

pub struct MyVec<T> {
    ptr: NonNull<T>,  // 使用 NonNull 保证非空
    len: usize,
    cap: usize,
    _marker: std::marker::PhantomData<T>,
}

unsafe impl<T: Send> Send for MyVec<T> {}
unsafe impl<T: Sync> Sync for MyVec<T> {}

impl<T> MyVec<T> {
    pub fn new() -> Self {
        Self {
            ptr: NonNull::dangling(),  // 空指针优化
            len: 0,
            cap: 0,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        if capacity == 0 {
            return Self::new();
        }

        let layout = Layout::array::<T>(capacity).unwrap();
        let ptr = unsafe { alloc(layout) };

        if ptr.is_null() {
            handle_alloc_error(layout);
        }

        Self {
            ptr: unsafe { NonNull::new_unchecked(ptr as *mut T) },
            len: 0,
            cap: capacity,
            _marker: std::marker::PhantomData,
        }
    }
}
```

### 2.2 Push 操作
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust,ignore
impl<T> MyVec<T> {
    pub fn push(&mut self, value: T) {
        // 检查容量
        if self.len == self.cap {
            self.grow();
        }

        // 在末尾写入元素
        unsafe {
            let ptr = self.ptr.as_ptr().add(self.len);
            ptr.write(value);
        }

        self.len += 1;
    }

    fn grow(&mut self) {
        // 计算新容量
        let new_cap = if self.cap == 0 {
            4
        } else {
            self.cap * 2
        };

        // 创建新内存布局
        let new_layout = Layout::array::<T>(new_cap).unwrap();

        // 分配新内存
        let new_ptr = unsafe { alloc(new_layout) };
        if new_ptr.is_null() {
            handle_alloc_error(new_layout);
        }

        // 复制旧数据
        if self.len > 0 {
            unsafe {
                std::ptr::copy_nonoverlapping(
                    self.ptr.as_ptr(),
                    new_ptr as *mut T,
                    self.len
                );
            }

            // 释放旧内存
            let old_layout = Layout::array::<T>(self.cap).unwrap();
            unsafe { dealloc(self.ptr.as_ptr() as *mut u8, old_layout); }
        }

        self.ptr = unsafe { NonNull::new_unchecked(new_ptr as *mut T) };
        self.cap = new_cap;
    }
}
```

### 2.3 Pop 操作
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,ignore
impl<T> MyVec<T> {
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;

        // 读取并移动元素
        Some(unsafe {
            self.ptr.as_ptr().add(self.len).read()
        })
    }
}
```

### 2.4 索引访问
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```rust,ignore
impl<T> Index<usize> for MyVec<T> {
    type Output = T;

    fn index(&self, index: usize) -> &T {
        assert!(index < self.len, "index out of bounds");
        unsafe { &*self.ptr.as_ptr().add(index) }
    }
}

impl<T> IndexMut<usize> for MyVec<T> {
    fn index_mut(&mut self, index: usize) -> &mut T {
        assert!(index < self.len, "index out of bounds");
        unsafe { &mut *self.ptr.as_ptr().add(index) }
    }
}
```

---

## 3. Drop 实现
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```rust,ignore
impl<T> Drop for MyVec<T> {
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
        let layout = Layout::array::<T>(self.cap).unwrap();
        unsafe {
            dealloc(self.ptr.as_ptr() as *mut u8, layout);
        }
    }
}
```

---

## 4. 迭代器实现
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```rust,ignore
pub struct IntoIter<T> {
    ptr: NonNull<T>,
    cap: usize,
    start: *const T,
    end: *const T,
    _marker: std::marker::PhantomData<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.start == self.end {
            return None;
        }

        unsafe {
            let result = self.start.read();
            self.start = self.start.add(1);
            Some(result)
        }
    }
}

impl<T> IntoIterator for MyVec<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(mut self) -> IntoIter<T> {
        let ptr = self.ptr;
        let cap = self.cap;

        let start = ptr.as_ptr();
        let end = unsafe { ptr.as_ptr().add(self.len) };

        // 防止 Vec 被 drop
        self.len = 0;
        self.cap = 0;
        std::mem::forget(self);

        IntoIter {
            ptr,
            cap,
            start,
            end,
            _marker: std::marker::PhantomData,
        }
    }
}
```

---

## 5. 测试与验证
>
> **[来源: [crates.io](https://crates.io/)]**

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_push_pop() {
        let mut vec = MyVec::new();
        vec.push(1);
        vec.push(2);
        vec.push(3);

        assert_eq!(vec.pop(), Some(3));
        assert_eq!(vec.pop(), Some(2));
        assert_eq!(vec.pop(), Some(1));
        assert_eq!(vec.pop(), None);
    }

    #[test]
    fn test_index() {
        let mut vec = MyVec::new();
        vec.push(10);
        vec.push(20);

        assert_eq!(vec[0], 10);
        assert_eq!(vec[1], 20);

        vec[0] = 100;
        assert_eq!(vec[0], 100);
    }

    #[test]
    fn test_drop() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        struct DropCounter;
        impl Drop for DropCounter {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }

        {
            let mut vec: MyVec<DropCounter> = MyVec::new();
            vec.push(DropCounter);
            vec.push(DropCounter);
            vec.push(DropCounter);
            // vec 在这里 drop
        }

        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 3);
    }
}
```

---

## 6. Miri 验证
>
> **[来源: [docs.rs](https://docs.rs/)]**

```bash
cargo miri test
```

Miri 检查:

- 无未初始化内存读取
- 无悬垂指针解引用
- 无内存泄漏
- 正确调用 Drop

---

## 完整代码
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```rust
// src/lib.rs
use std::alloc::{alloc, dealloc, handle_alloc_error, Layout, realloc};
use std::ptr::NonNull;

pub struct MyVec<T> {
    ptr: NonNull<T>,
    len: usize,
    cap: usize,
    _marker: std::marker::PhantomData<T>,
}

// 实现... (见上文)
```

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
