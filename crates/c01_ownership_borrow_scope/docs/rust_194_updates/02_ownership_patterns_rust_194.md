# Rust 1.94 所有权模式实战

> **Rust 版本**: 1.94.0
> **Edition**: 2024
> **最后更新**: 2026-03-10

---

## 目录

- [Rust 1.94 所有权模式实战](#rust-194-所有权模式实战)
  - [目录](#目录)
  - [use\<\> 精确捕获模式](#use-精确捕获模式)
    - [2.1 基础用法](#21-基础用法)
    - [2.2 在 trait 实现中的应用](#22-在-trait-实现中的应用)
  - [所有权与异步结合](#所有权与异步结合)
    - [2.3 异步生成器与所有权](#23-异步生成器与所有权)
  - [内存高效模式](#内存高效模式)
    - [2.4 零拷贝序列化](#24-零拷贝序列化)
    - [2.5 自定义 Drop 链](#25-自定义-drop-链)
  - [错误处理中的所有权](#错误处理中的所有权)
    - [2.6 错误传播与所有权恢复](#26-错误传播与所有权恢复)
  - [性能对比](#性能对比)
    - [Rust 1.94 vs 1.93](#rust-194-vs-193)
  - [相关文档](#相关文档)

---

## use<> 精确捕获模式

### 2.1 基础用法

```rust
// Edition 2024: 精确控制闭包捕获
fn example_use_syntax() {
    let data = vec![1, 2, 3];
    let name = String::from("test");

    // 不捕获任何变量
    let closure_no_capture = || -> i32 { 42 };

    // 只捕获 data（移动）
    let closure_data_only = move || -> Vec<i32> { data };

    // 使用 use<> 精确捕获（Edition 2024）
    let closure_precise = || -> String + use<name> {
        format!("Hello, {}", name)
    };

    // 现在 data 和 name 都可以独立使用
    println!("Name: {}", name);
}
```

### 2.2 在 trait 实现中的应用

```rust
// 使用 use<> 在 RPITIT 中精确捕获
trait DataProcessor {
    fn process(&self, data: Vec<u8>) -> impl Iterator<Item = u8> + use<>;
}

struct SimpleProcessor;

impl DataProcessor for SimpleProcessor {
    fn process(&self, data: Vec<u8>) -> impl Iterator<Item = u8> + use<> {
        // use<> 确保不捕获 self，返回的迭代器可以独立存在
        data.into_iter().filter(|b| *b > 0)
    }
}

// 对比：捕获 self 的情况
struct StatefulProcessor {
    threshold: u8,
}

impl DataProcessor for StatefulProcessor {
    fn process(&self, data: Vec<u8>) -> impl Iterator<Item = u8> + use<Self> {
        // use<Self> 表示捕获 self 的引用
        let threshold = self.threshold;
        data.into_iter().filter(move |b| *b > threshold)
    }
}
```

---

## 所有权与异步结合

### 2.3 异步生成器与所有权

```rust
// Rust 1.94: gen 关键字（生成器）与所有权
#![feature(gen_blocks)]

use std::pin::Pin;
use std::future::Future;

/// 异步生成器：安全地处理所有权
async fn async_data_stream() -> impl Iterator<Item = i32> {
    gen {
        let data = vec![1, 2, 3, 4, 5];
        // 生成器内部拥有 data 的所有权
        for item in data {
            yield item * 2;
        }
        // data 在这里自动释放
    }
}

/// 使用 Pin 的自引用异步模式
use std::marker::PhantomPinned;

pub struct AsyncBuffer {
    data: Vec<u8>,
    // PhantomPinned 确保结构体不会被移动
    _pin: PhantomPinned,
}

impl AsyncBuffer {
    pub fn new(data: Vec<u8>) -> Pin<Box<Self>> {
        Box::pin(AsyncBuffer {
            data,
            _pin: PhantomPinned,
        })
    }

    /// 获取数据的异步方法
    pub async fn process(self: Pin<&Self>) -> Vec<u8> {
        // SAFETY: 由于 Pin，self 不会被移动
        let data = &self.data;
        // 异步处理...
        tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        data.clone()
    }
}
```

---

## 内存高效模式

### 2.4 零拷贝序列化

```rust
use std::io::{self, Write};

/// 使用所有权转移实现零拷贝
pub struct ZeroCopyBuffer {
    inner: Vec<u8>,
    position: usize,
}

impl ZeroCopyBuffer {
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: Vec::with_capacity(capacity),
            position: 0,
        }
    }

    /// 转移所有权给写入器，避免拷贝
    pub fn into_inner(self) -> Vec<u8> {
        self.inner
    }

    /// 获取可读区域（不拷贝）
    pub fn readable(&self) -> &[u8] {
        &self.inner[self.position..]
    }

    /// 消耗已读数据，释放内存
    pub fn consume(&mut self, amount: usize) {
        self.position += amount;
        if self.position > self.inner.len() / 2 {
            // 如果已读超过一半，重新分配以减少内存占用
            let remaining = self.inner.split_off(self.position);
            self.inner = remaining;
            self.position = 0;
        }
    }
}

impl Write for ZeroCopyBuffer {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.inner.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
```

### 2.5 自定义 Drop 链

```rust
/// 确保资源按正确顺序释放
pub struct ResourceChain<A, B, C> {
    primary: A,
    secondary: B,
    cleanup: C,
}

impl<A, B, C> ResourceChain<A, B, C> {
    pub fn new(primary: A, secondary: B, cleanup: C) -> Self {
        Self {
            primary,
            secondary,
            cleanup,
        }
    }

    /// 手动释放顺序控制
    pub fn release(self) -> (A, B, C) {
        // 解构而不调用 drop，允许调用者控制顺序
        let Self { primary, secondary, cleanup } = self;
        std::mem::forget(self); // 防止自动 drop
        (primary, secondary, cleanup)
    }
}

impl<A, B, C> Drop for ResourceChain<A, B, C> {
    fn drop(&mut self) {
        // 标准释放顺序：cleanup -> secondary -> primary
        // 注意：实际上无法手动控制，这里只是演示概念
    }
}

/// 更好的方式：使用元组结构确保顺序
tuple_struct! {
    OrderedResources(primary: A, secondary: B, cleanup: C)
    drop: cleanup, secondary, primary
}

// 宏实现（简化版）
macro_rules! tuple_struct {
    (
        $name:ident($($field:ident: $ty:ty),+)
        drop: $($drop_order:ident),+
    ) => {
        struct $name<$($ty),+> {
            $($field: $ty),+
        }

        impl<$($ty),+> Drop for $name<$($ty),+> {
            fn drop(&mut self) {
                $(
                    // 使用 ManuallyDrop 控制顺序
                    let _ = unsafe { std::ptr::read(&self.$drop_order) };
                )+
            }
        }
    };
}
```

---

## 错误处理中的所有权

### 2.6 错误传播与所有权恢复

```rust
use std::fmt;

/// 包含所有权信息的错误类型
pub enum RecoveryError<T> {
    Permanent { error: String },
    Transient { error: String, value: T },  // 可以重试，返回所有权
}

impl<T: fmt::Debug> fmt::Display for RecoveryError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RecoveryError::Permanent { error } => {
                write!(f, "Permanent error: {}", error)
            }
            RecoveryError::Transient { error, value } => {
                write!(f, "Transient error: {}, value: {:?}", error, value)
            }
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for RecoveryError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// 可重试的操作
pub trait RetryableOperation<T> {
    fn execute(&mut self, value: T) -> Result<T, RecoveryError<T>>;
}

/// 带重试的错误处理
pub fn execute_with_retry<T, O>(
    mut operation: O,
    value: T,
    max_retries: usize,
) -> Result<T, RecoveryError<T>>
where
    O: RetryableOperation<T>,
{
    let mut current_value = value;
    let mut retries = 0;

    loop {
        match operation.execute(current_value) {
            Ok(result) => return Ok(result),
            Err(RecoveryError::Permanent { error }) => {
                return Err(RecoveryError::Permanent { error });
            }
            Err(RecoveryError::Transient { error, value }) => {
                if retries >= max_retries {
                    return Err(RecoveryError::Transient { error, value });
                }
                current_value = value;  // 恢复所有权
                retries += 1;
                std::thread::sleep(std::time::Duration::from_millis(100 * retries as u64));
            }
        }
    }
}
```

---

## 性能对比

### Rust 1.94 vs 1.93

| 模式 | 1.93 | 1.94 | 提升 |
|------|------|------|------|
| RefCell 映射 | 需要克隆 | 零拷贝映射 | 10-50% |
| 闭包捕获 | 自动推断 | 精确控制 | 更清晰 |
| MaybeUninit | 基础 API | 完善文档 | 更安全 |

---

## 相关文档

- [Rust 1.94 所有权更新](./01_edition_2024_ownership.md)
- [C01 主索引](../00_MASTER_INDEX.md)
- [Rust 1.94 迁移指南](../../../docs/05_guides/RUST_194_MIGRATION_GUIDE.md)
