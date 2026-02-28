# C12 WASM - API 参考

> **文档类型**: Tier 3 - 参考层
> **文档定位**: wasm-bindgen API 完整参考
> **项目状态**: ✅ 完整完成
> **相关文档**: [Rust 编译 WASM](../tier_02_guides/02_rust_编译_wasm.md) | [JavaScript 互操作](../tier_02_guides/03_javascript_互操作.md)

**最后更新**: 2025-12-11
**适用版本**: Rust 1.92.0+ / Edition 2024, WASM 2.0 + WASI 0.2

---

## 📋 目录

- [C12 WASM - API 参考](#c12-wasm---api-参考)
  - [📋 目录](#-目录)
  - [📐 知识结构](#-知识结构)
    - [概念定义](#概念定义)
    - [属性特征](#属性特征)
    - [关系连接](#关系连接)
    - [思维导图](#思维导图)
  - [🎯 概述](#-概述)
  - [🔧 核心宏](#-核心宏)
    - [#\[wasm\_bindgen\]](#wasm_bindgen)
    - [#\[wasm\_bindgen(start)\]](#wasm_bindgenstart)
  - [📦 类型系统](#-类型系统)
    - [基本类型映射](#基本类型映射)
  - [🌐 Web API](#-web-api)
    - [console](#console)
    - [Fetch API](#fetch-api)
  - [📚 相关资源](#-相关资源)

---

## 📐 知识结构

### 概念定义

**WASM API 参考 (WASM API Reference)**:

- **定义**: wasm-bindgen API 的完整参考手册
- **类型**: API 参考文档
- **范畴**: WebAssembly、API 参考
- **版本**: Rust 1.92.0+, wasm-bindgen
- **相关概念**: wasm-bindgen、WebAssembly、JavaScript 互操作

### 属性特征

**核心属性**:

- **核心宏**: `#[wasm_bindgen]`、`#[wasm_bindgen(start)]`
- **类型系统**: 基本类型映射、复杂类型
- **Web API**: console、Fetch API
- **JavaScript 互操作**: 函数导出、类型转换

**性能特征**:

- **高效互操作**: 优化的 Rust-JavaScript 互操作
- **类型安全**: 类型映射保证类型安全
- **适用场景**: Web 应用、服务器应用、边缘计算

### 关系连接

**组合关系**:

- WASM API 参考 --[covers]--> wasm-bindgen API
- WASM 应用开发 --[uses]--> WASM API 参考

**依赖关系**:

- WASM API 参考 --[depends-on]--> wasm-bindgen
- WASM 开发 --[depends-on]--> WASM API 参考

### 思维导图

```text
WASM API 参考
│
├── 核心宏
│   └── #[wasm_bindgen]
├── 类型系统
│   └── 类型映射
├── Web API
│   └── console/Fetch
└── JavaScript 互操作
    └── 函数导出
```

---

## 🎯 概述

本文档提供 wasm-bindgen API 的完整参考。

---

## 🔧 核心宏

### #[wasm_bindgen]

**用途**: 导出函数、结构体、类等给 JavaScript。

**示例**:

```rust
#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}
```

### #[wasm_bindgen(start)]

**用途**: 标记 WASM 模块初始化时执行的函数。

**示例**:

```rust
#[wasm_bindgen(start)]
pub fn main() {
    console_log!("WASM module initialized");
}
```

---

## 📦 类型系统

### 基本类型映射

| Rust 类型      | JavaScript 类型  |
| :--- | :--- |
| `i32`, `u32`   | `number`         |
| `i64`, `u64`   | `BigInt`         |
| `f32`, `f64`   | `number`         |
| `bool`         | `boolean`        |
| `String`       | `string`         |
| `&str`         | `string`         |
| `Vec<T>`       | `Array`          |
| `Option<T>`    | `T \| undefined` |
| `Result<T, E>` | `Promise<T>`     |

---

## 🌐 Web API

### console

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}

pub fn log_message(msg: &str) {
    log(msg);
}
```

### Fetch API

```rust
use wasm_bindgen::prelude::*;
use wasm_bindgen_futures::JsFuture;
use web_sys::{Request, RequestInit, Response};

#[wasm_bindgen]
pub async fn fetch_data(url: &str) -> Result<JsValue, JsValue> {
    let mut opts = RequestInit::new();
    opts.set_method("GET");

    let request = Request::new_with_str_and_init(url, &opts)?;
    let window = web_sys::window().unwrap();
    let resp_value = JsFuture::from(window.fetch_with_request(&request)).await?;
    let resp: Response = resp_value.dyn_into()?;
    JsFuture::from(resp.json()?).await
}
```

---

## 📚 相关资源

- [wasm-bindgen Book](https://rustwasm.github.io/docs/wasm-bindgen/)
- [web-sys API](https://rustwasm.github.io/wasm-bindgen/web-sys/index.html)

---

**文档维护**: Documentation Team
**创建日期**: 2025-10-30
**适用版本**: Rust 1.92.0+ / Edition 2024, WASM 2.0 + WASI 0.2
