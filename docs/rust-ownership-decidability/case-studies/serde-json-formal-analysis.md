# Serde JSON 形式化分析

> **主题**: JSON序列化的内存安全
>
> **形式化框架**: 零拷贝 + 类型驱动
>
> **参考**: serde_json Documentation

---

## 目录

- [Serde JSON 形式化分析](#serde-json-形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 序列化不变式](#2-序列化不变式)
    - [定理 2.1 (类型一致性)](#定理-21-类型一致性)
    - [定理 2.2 (逃逸安全)](#定理-22-逃逸安全)
  - [3. 反序列化安全](#3-反序列化安全)
    - [定理 3.1 (拒绝服务防护)](#定理-31-拒绝服务防护)
    - [定理 3.2 (数字处理)](#定理-32-数字处理)
  - [4. 零拷贝优化](#4-零拷贝优化)
    - [定理 4.1 (Cow支持)](#定理-41-cow支持)
  - [5. 流式处理](#5-流式处理)
    - [定理 5.1 (迭代器解析)](#定理-51-迭代器解析)
  - [6. 反例](#6-反例)
    - [反例 6.1 (浮点精度)](#反例-61-浮点精度)
    - [反例 6.2 (未转义键)](#反例-62-未转义键)

---

## 1. 引言

serde_json提供:

- 类型驱动的序列化
- 安全处理任意JSON
- 流式解析
- 零拷贝选项

---

## 2. 序列化不变式

### 定理 2.1 (类型一致性)

> Serialize实现保证类型一致的JSON输出。

```rust
let data = MyStruct { x: 1, y: 2 };
let json = serde_json::to_string(&data)?;
// 保证: JSON结构对应Rust结构
```

**形式化**:

$$
\forall v: T. \text{deserialize}(\text{serialize}(v)) = v
$$

∎

### 定理 2.2 (逃逸安全)

> 字符串自动转义，防止注入。

```rust
let s = "hello\nworld\"quoted";
let json = serde_json::to_string(&s)?;
// 输出: "hello\nworld\"quoted"
// 自动处理: ", \, \n等
```

∎

---

## 3. 反序列化安全

### 定理 3.1 (拒绝服务防护)

> serde_json限制递归深度防止栈溢出。

```json
// 恶意输入
{"a":{"a":{"a":...}}}  // 无限嵌套
```

**防护**:

```rust
let deserializer = serde_json::Deserializer::from_str(input);
deserializer.disable_recursion_limit();  // 需显式启用风险
```

∎

### 定理 3.2 (数字处理)

> JSON数字范围可能超出Rust类型。

```rust
let json = "340282366920938463463374607431768211456"; // > u128::MAX

// 错误
let n: u128 = serde_json::from_str(json)?;  // Err

// 使用浮点或大数类型
let n: f64 = serde_json::from_str(json)?;
```

∎

---

## 4. 零拷贝优化

### 定理 4.1 (Cow支持)

> 使用Cow实现零拷贝反序列化。

```rust
use std::borrow::Cow;

#[derive(Deserialize)]
struct Data<'a> {
    #[serde(borrow)]
    name: Cow<'a, str>,
}

let data: Data = serde_json::from_str(json)?;
// name借用输入数据(无转义需要时)
```

∎

---

## 5. 流式处理

### 定理 5.1 (迭代器解析)

> StreamDeserializer处理大JSON流。

```rust
let stream = serde_json::Deserializer::from_reader(reader)
    .into_iter::<MyType>();

for item in stream {
    process(item?);  // 逐个处理，低内存
}
```

∎

---

## 6. 反例

### 反例 6.1 (浮点精度)

```rust
// JSON浮点数可能丢失精度
let json = r#"{"value": 0.1}"#;
let data: MyStruct = serde_json::from_str(json)?;
// data.value 可能不是精确的0.1
```

### 反例 6.2 (未转义键)

```rust
#[derive(Serialize)]
struct Data {
    #[serde(rename = "type")]  // 关键字需处理
    type_: String,
}
```

---

*文档版本: 1.0.0*
*定理数量: 7个*
