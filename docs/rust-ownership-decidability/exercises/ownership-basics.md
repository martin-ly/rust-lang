# 所有权基础练习

> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **难度**: 🟢 简单
> **目标**: 掌握 Rust 所有权系统基础

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [所有权基础练习](#所有权基础练习)
  - [📑 目录](#-目录)
  - [练习 1: 移动语义](#练习-1-移动语义)
    - [题目](#题目)
    - [答案](#答案)
  - [练习 2: 借用规则](#练习-2-借用规则)
    - [题目](#题目-1)
    - [答案](#答案-1)
  - [练习 3: 生命周期](#练习-3-生命周期)
    - [题目](#题目-2)
    - [答案](#答案-2)
  - [练习 4: 实现自定义智能指针](#练习-4-实现自定义智能指针)
    - [题目](#题目-3)
    - [答案](#答案-3)
  - [*更多练习持续添加中...*](#更多练习持续添加中)
  - [相关概念](#相关概念)

## 练习 1: 移动语义
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 题目
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```rust,ignore
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;

    println!("{}", s1);  // 这里会报错，为什么？
}
```

### 答案
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;  // s1 被移动到 s2

    // println!("{}", s1);  // 错误：s1 不再有效
    println!("{}", s2);     // 正确：s2 拥有数据
}
```

**解释**: String 不实现 Copy trait，赋值时发生所有权移动。

---

## 练习 2: 借用规则
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 题目
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

修复以下代码：

```rust,ignore
fn main() {
    let mut s = String::from("hello");

    let r1 = &s;
    let r2 = &mut s;

    println!("{} {}", r1, r2);
}
```

### 答案
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```rust
fn main() {
    let mut s = String::from("hello");

    let r1 = &s;
    println!("{}", r1);  // 在 r2 之前使用 r1

    let r2 = &mut s;      // 现在可以创建可变借用
    println!("{}", r2);
}
```

**解释**: 不能同时拥有不可变和可变借用。

---

## 练习 3: 生命周期
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 题目

实现一个函数，返回两个字符串切片中较长的一个。

```rust,ignore
fn longest(x: &str, y: &str) -> &str {
    // 实现这里
}
```

### 答案

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

fn main() {
    let string1 = String::from("long string is long");
    {
        let string2 = String::from("xyz");
        let result = longest(&string1, &string2);
        println!("The longest string is {}", result);
    }
}
```

---

## 练习 4: 实现自定义智能指针

### 题目

实现一个简单的 Box。

### 答案

```rust
use std::ops::Deref;

struct MyBox<T>(T);

impl<T> MyBox<T> {
    fn new(x: T) -> MyBox<T> {
        MyBox(x)
    }
}

impl<T> Deref for MyBox<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T> Drop for MyBox<T> {
    fn drop(&mut self) {
        println!("Dropping MyBox!");
    }
}
```

---

*更多练习持续添加中...*
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念

- [exercises 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
