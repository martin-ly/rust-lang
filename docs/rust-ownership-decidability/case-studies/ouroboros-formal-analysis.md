# Ouroboros 自引用结构形式化分析

> **主题**: 安全的自引用struct
>
> **形式化框架**: 借用投影 + Pin保证
>
> **参考**: ouroboros Documentation

---

## 目录

- [Ouroboros 自引用结构形式化分析](#ouroboros-自引用结构形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 自引用构建](#2-自引用构建)
    - [定理 2.1 (宏生成安全)](#定理-21-宏生成安全)
  - [3. 借用投影](#3-借用投影)
    - [定理 3.1 (投影函数)](#定理-31-投影函数)
  - [4. 不变式保证](#4-不变式保证)
    - [定理 4.1 (不可移动)](#定理-41-不可移动)
  - [5. 反例](#5-反例)
    - [反例 5.1 (手动构建)](#反例-51-手动构建)

---

## 1. 引言

Ouroboros提供:

- 安全自引用结构
- 宏自动生成
- Pin兼容
- 无需unsafe

---

## 2. 自引用构建

### 定理 2.1 (宏生成安全)

> 宏生成不可移动结构。

```rust
use ouroboros::self_referencing;

#[self_referencing]
struct DataWithSlice {
    data: Vec<u8>,
    #[borrows(data)]
    slice: &'this [u8],
}

let data = DataWithSlice::new(
    vec![1, 2, 3],
    |data| &data[0..2],
);
```

∎

---

## 3. 借用投影

### 定理 3.1 (投影函数)

> 安全访问自引用字段。

```rust
// 自动生成的访问器
data.with_slice(|slice| {
    println!("{:?}", slice);
});
```

∎

---

## 4. 不变式保证

### 定理 4.1 (不可移动)

> 结构被Pin，防止破坏自引用。

```rust
// DataWithSlice是!Unpin
// 不能安全地移动
```

∎

---

## 5. 反例

### 反例 5.1 (手动构建)

```rust
// 危险: 手动构建自引用
struct Bad {
    data: Vec<u8>,
    slice: *const [u8],  // 原始指针
}
// 移动后slice悬垂!

// 正确: 使用Ouroboros
```

---

*文档版本: 1.0.0*
*定理数量: 4个*
