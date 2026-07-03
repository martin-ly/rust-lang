# Tier 4: 自引用结构

> **文档类型**: 高级主题
> **难度**: ⭐⭐⭐⭐⭐
> **适用版本**: Rust 1.96.1+

---

## 📊 目录

- [Tier 4: 自引用结构](#tier-4-自引用结构)
  - [📊 目录](#-目录)
  - [1. 自引用问题](#1-自引用问题)
  - [2. Pin 和 Unpin](#2-pin-和-unpin)
    - [Pin 的基本概念](#pin-的基本概念)
  - [3. 使用 ouroboros 库](#3-使用-ouroboros-库)
  - [4. Async 中的自引用](#4-async-中的自引用)

## 1. 自引用问题

```rust
// ❌ 无法编译 - 自引用
// struct SelfRef {
//     data: String,
//     ptr: &str, // 指向 data 的引用
// }
```

---

## 2. Pin 和 Unpin

### Pin 的基本概念

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SelfReferential {
    data: String,
    ptr: *const String,
    _pin: PhantomPinned,
}

impl SelfReferential {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::pin(SelfReferential {
            data,
            ptr: std::ptr::null(),
            _pin: PhantomPinned,
        });

        unsafe {
            let ptr = &boxed.data as *const String;
            let mut_ref = Pin::as_mut(&mut boxed);
            let inner = Pin::get_unchecked_mut(mut_ref);
            inner.ptr = ptr;
        }

        boxed
    }

    fn data(&self) -> &str {
        &self.data
    }

    fn ptr_data(&self) -> &str {
        unsafe { &*self.ptr }
    }
}
```

---

## 3. 使用 ouroboros 库

```rust
use ouroboros::self_referencing;

#[self_referencing]
struct MyStruct {
    data: String,
    #[borrows(data)]
    data_ref: &'this str,
}

let my_struct = MyStructBuilder {
    data: "Hello, world!".to_string(),
    data_ref_builder: |data| data.as_str(),
}.build();
```

---

## 4. Async 中的自引用

```rust
async fn async_self_ref() {
    let data = String::from("hello");
    let data_ref = &data;

    some_await().await; // Pin 确保安全

    println!("{}", data_ref);
}
```

---

**相关文档**:

- [C06 Async](../../../c06_async/README.md)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
