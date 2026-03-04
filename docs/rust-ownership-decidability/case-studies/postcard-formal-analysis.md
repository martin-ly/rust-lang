# Postcard 嵌入式序列化形式化分析

> **主题**: 紧凑二进制序列化
>
> **形式化框架**: varint编码 + 大小优化
>
> **参考**: postcard Documentation

---

## 目录

- [Postcard 嵌入式序列化形式化分析](#postcard-嵌入式序列化形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 编码格式](#2-编码格式)
    - [定理 2.1 (紧凑编码)](#定理-21-紧凑编码)
  - [3. Varint编码](#3-varint编码)
    - [定理 3.1 (LEB128)](#定理-31-leb128)
  - [4. 嵌入式优化](#4-嵌入式优化)
    - [定理 4.1 (堆分配避免)](#定理-41-堆分配避免)
  - [5. 反例](#5-反例)
    - [反例 5.1 (大小限制)](#反例-51-大小限制)

---

## 1. 引言

postcard提供:

- 紧凑二进制格式
- varint编码
- 嵌入式友好
- Serde集成

---

## 2. 编码格式

### 定理 2.1 (紧凑编码)

> 无字段名、类型标记最小化。

```rust
let data = (42u32, "hello");
let bytes = postcard::to_allocvec(&data)?;
// 小尺寸: 整数varint编码
```

∎

---

## 3. Varint编码

### 定理 3.1 (LEB128)

> 小整数使用更少字节。

```rust
0..=127      -> 1 byte
128..=16383  -> 2 bytes
//  continuation bit标记
```

∎

---

## 4. 嵌入式优化

### 定理 4.1 (堆分配避免)

> 支持no_std，避免alloc。

```rust
use postcard::serialize_with_flavor;
let mut buf = [0u8; 32];
let used = postcard::serialize_with_flavor(&data, &mut buf)?;
```

∎

---

## 5. 反例

### 反例 5.1 (大小限制)

```rust
// 需预分配足够缓冲区
let mut buf = [0u8; 10];
// 数据太大可能失败
```

---

*文档版本: 1.0.0*
*定理数量: 4个*
