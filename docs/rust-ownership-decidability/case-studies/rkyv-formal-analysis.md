# Rkyv 零拷贝序列化形式化分析

> **主题**: 零拷贝反序列化
>
> **形式化框架**: 相对指针 + 验证
>
> **参考**: rkyv Documentation

---

## 目录

- [Rkyv 零拷贝序列化形式化分析](#rkyv-零拷贝序列化形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 相对指针](#2-相对指针)
    - [定理 2.1 (位置无关)](#定理-21-位置无关)
  - [3. 验证](#3-验证)
    - [定理 3.1 (字节检查)](#定理-31-字节检查)
  - [4. 安全性](#4-安全性)
    - [定理 4.1 (严格模式)](#定理-41-严格模式)
  - [5. 反例](#5-反例)
    - [反例 5.1 (修改存档)](#反例-51-修改存档)

---

## 1. 引言

rkyv提供:

- 零拷贝反序列化
- 相对指针
- 存档格式验证
- 跨平台支持

---

## 2. 相对指针

### 定理 2.1 (位置无关)

> 使用相对偏移而非绝对指针。

```rust
use rkyv::{Archive, Deserialize, Serialize};

#[derive(Archive, Deserialize, Serialize)]
struct Node {
    value: i32,
    children: Vec<Node>,
}
```

**存档格式**:

- 相对偏移存储
- 可mmap直接访问
- 无需解压

∎

---

## 3. 验证

### 定理 3.1 (字节检查)

> 验证存档格式有效性。

```rust
use rkyv::check_archived_root;

let archived = check_archived_root::<Node>(bytes)?;
// 返回错误如果格式无效
```

∎

---

## 4. 安全性

### 定理 4.1 (严格模式)

> 严格模式提供额外保证。

```rust
let archived = rkyv::from_bytes::<Node>(bytes)?;
// 验证所有指针边界
```

∎

---

## 5. 反例

### 反例 5.1 (修改存档)

```rust
// 危险: 修改存档字节后直接访问
bytes[0] = 0xFF;
let archived = unsafe { rkyv::archived_root::<Node>(&bytes) };
// 可能访问无效内存
```

---

*文档版本: 1.0.0*
*定理数量: 4个*
