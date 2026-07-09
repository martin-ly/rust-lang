# Pin 与自引用结构速查卡 {#pin-与自引用结构速查卡}

> **EN**: Pin Cheatsheet
> **Summary**: Pin 与自引用（Reference）结构速查卡 Pin Cheatsheet.
>
> **Rust 版本**: 1.96.1+ (Edition 2024)
>
> **受众**: [进阶] / [专家]
> **内容分级**: [专家级]
> **分级**: [A]
> **Bloom 层级**: L2 (理解)
> **适用场景**: 异步（Async） Future、自引用结构、侵入式数据结构
> **版本**: Rust 1.68+ (`pin!` 宏（Macro）稳定)

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Pin 与自引用结构速查卡 {#pin-与自引用结构速查卡}](#pin-与自引用结构速查卡-pin-与自引用结构速查卡)
  - [📑 目录 {#目录}](#-目录-目录)
  - [🎯 核心概念 {#核心概念}](#-核心概念-核心概念)
  - [⚡ 代码模式 {#代码模式}](#-代码模式-代码模式)
    - [栈固定 {#栈固定}](#栈固定-栈固定)
    - [堆固定 {#堆固定}](#堆固定-堆固定)
    - [自引用结构（概念） {#自引用结构概念}](#自引用结构概念-自引用结构概念)
    - [安全投影规则 {#安全投影规则}](#安全投影规则-安全投影规则)
  - [📊 Pin 使用决策树 {#pin-使用决策树}](#-pin-使用决策树-pin-使用决策树)
  - [🔗 参考 {#参考}](#-参考-参考)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 🎯 核心概念 {#核心概念}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```text
Pin<P> 的核心保证:
┌─────────────────────────────────────────┐
│  如果 T: !Unpin，则 Pin<&mut T> 保证:    │
│  1. T 的内存地址不会变（不被移动）        │
│  2. 直到 Drop 前，T 始终在同一位置         │
└─────────────────────────────────────────┘
```

| 概念 | 说明 | 典型类型 |
|------|------|---------|
| `Pin<P>` | 固定指针包装器 | `Pin<&mut T>`, `Pin<Box<T>>` |
| `Unpin` | Auto trait，99% 类型自动实现 | `i32`, `String`, `Vec<T>` |
| `!Unpin` | 显式 `PhantomPinned` 标记 | 自引用结构 |
| `pin!` | 栈固定宏（1.68+） | `let p = pin!(data);` |
| `Box::pin` | 堆固定 | `Pin<Box<T>>` |

---

## ⚡ 代码模式 {#代码模式}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 栈固定 {#栈固定}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
use std::pin::pin;

let data = MyStruct::new();
let pinned: Pin<&mut MyStruct> = pin!(data);
```

### 堆固定 {#堆固定}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust,ignore
let pinned: Pin<Box<MyStruct>> = Box::pin(MyStruct::new());
```

### 自引用结构（概念） {#自引用结构概念}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust
use std::marker::PhantomPinned;

struct SelfRef {
    data: String,
    // 这个字段指向 data，所以结构不能移动
    _pin: PhantomPinned,
}
```

### 安全投影规则 {#安全投影规则}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```rust,ignore
impl MyStruct {
    // ✅ 安全: 投影到不包含自引用的字段
    fn get_name(self: Pin<&Self>) -> &str {
        &self.name
    }

    // ❌ 不安全: 投影到包含自引用的字段
    // fn get_ptr(self: Pin<&Self>) -> &String { &self.data }
}
```

---

## 📊 Pin 使用决策树 {#pin-使用决策树}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```text
需要固定值?
├── 生命周期短（函数内）──→ pin! 宏（栈固定）
├── 需要长期存储 ─────────→ Box::pin（堆固定）
└── 不需要固定 ───────────→ 普通 &mut T

结构体包含自引用?
├── 是 ───────────────────→ PhantomPinned + Pin<&mut Self>
└── 否 ───────────────────→ 不需要 Pin
```

---

## 🔗 参考 {#参考}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [c01_pin_and_self_referential](../../../crates/c01_ownership_borrow_scope/src/pin_and_self_referential.rs)
- [Rust Pin 文档](https://doc.rust-lang.org/std/pin/)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-05-08

---

> **权威来源**: [Rust Standard Library](https://doc.rust-lang.org/std/), [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust 标准库、Rust Reference、TRPL 官方来源标注 [Authority Source Sprint Batch 8](../../../concept/00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](README.md)

---

## 相关概念 {#相关概念}
>
> **[来源: [crates.io](https://crates.io/)]**

- [quick_reference 目录](README.md)
- [速查表索引](README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

---
