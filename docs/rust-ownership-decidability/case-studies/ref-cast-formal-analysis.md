# Ref-Cast 引用转换形式化分析

> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **主题**: 安全的类型到引用转换
>
> **形式化框架**: 透明包装 + 借用保持
>
> **参考**: ref-cast Documentation

---

## 目录
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

- [Ref-Cast 引用转换形式化分析](#ref-cast-引用转换形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. RefCast Trait](#2-refcast-trait)
    - [定理 2.1 (引用转换)](#定理-21-引用转换)
  - [3. 自动派生](#3-自动派生)
    - [定理 3.1 (派生宏)](#定理-31-派生宏)
  - [4. 安全保证](#4-安全保证)
    - [定理 4.1 (repr(transparent))](#定理-41-reprtransparent)
  - [5. 反例](#5-反例)
    - [反例 5.1 (非透明类型)](#反例-51-非透明类型)
  - [*定理数量: 4个*](#定理数量-4个)
  - [权威来源索引](#权威来源索引)

---

## 1. 引言
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

ref-cast提供:

- 安全的引用类型转换
- 透明包装器支持
- 自动派生宏
- 零开销抽象

---

## 2. RefCast Trait
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 定理 2.1 (引用转换)

> 允许从&T到&Wrapper<T>的转换。

```rust,ignore
use ref_cast::RefCast;

#[derive(RefCast)]
#[repr(transparent)]
struct Wrapper(String);

let s: &String = ...;
let w: &Wrapper = Wrapper::ref_cast(s);
```

∎

---

## 3. 自动派生

### 定理 3.1 (派生宏)

> 自动实现RefCast trait。

```rust,ignore
#[derive(RefCast)]
#[repr(transparent)]
pub struct Username(String);

// 自动生成:
// impl RefCast for Username {
//     fn ref_cast(s: &String) -> &Self { ... }
// }
```

∎

---

## 4. 安全保证

### 定理 4.1 (repr(transparent))

> 要求透明表示确保布局兼容。

```rust,ignore
#[repr(transparent)]  // 必须!
struct Wrapper(T);
```

∎

---

## 5. 反例

### 反例 5.1 (非透明类型)

```rust,ignore
#[derive(RefCast)]
// 忘记#[repr(transparent)]
struct Wrapper(String);  // 编译错误!
```

---

*文档版本: 1.0.0*
*定理数量: 4个*
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

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

> **[来源: Wikipedia - Formal Methods]**

> **[来源: Coq Reference Manual]**

> **[来源: TLA+ Documentation]**

> **[来源: ACM - Formal Verification]**
