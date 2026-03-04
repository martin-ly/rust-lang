# Ref-Cast 引用转换形式化分析

> **主题**: 安全的类型到引用转换
>
> **形式化框架**: 透明包装 + 借用保持
>
> **参考**: ref-cast Documentation

---

## 目录

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

---

## 1. 引言

ref-cast提供:

- 安全的引用类型转换
- 透明包装器支持
- 自动派生宏
- 零开销抽象

---

## 2. RefCast Trait

### 定理 2.1 (引用转换)

> 允许从&T到&Wrapper<T>的转换。

```rust
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

```rust
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

```rust
#[repr(transparent)]  // 必须!
struct Wrapper(T);
```

∎

---

## 5. 反例

### 反例 5.1 (非透明类型)

```rust
#[derive(RefCast)]
// 忘记#[repr(transparent)]
struct Wrapper(String);  // 编译错误!
```

---

*文档版本: 1.0.0*
*定理数量: 4个*
