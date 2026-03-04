# wasm-bindgen形式化分析

> **主题**: Rust-WebAssembly互操作
> **形式化框架**: FFI边界 + JS类型映射 + 内存管理
> **参考**: wasm-bindgen Guide (<https://rustwasm.github.io/wasm-bindgen>)

---

## 目录

- [wasm-bindgen形式化分析](#wasm-bindgen形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 类型映射](#2-类型映射)
    - [定义 TYPEMAP-1 ( 基本类型 )](#定义-typemap-1--基本类型-)
    - [定义 TYPEMAP-2 ( 复杂类型 )](#定义-typemap-2--复杂类型-)
  - [3. 内存管理](#3-内存管理)
    - [定义 MEM-1 ( wasm内存模型 )](#定义-mem-1--wasm内存模型-)
    - [定义 MEM-2 ( 所有权转移 )](#定义-mem-2--所有权转移-)
    - [定理 MEM-T1 ( 无泄漏 )](#定理-mem-t1--无泄漏-)
  - [4. 导出函数](#4-导出函数)
    - [定义 EXPORT-1 ( 导出语法 )](#定义-export-1--导出语法-)
    - [定义 EXPORT-2 ( 异步导出 )](#定义-export-2--异步导出-)
  - [5. 导入JS](#5-导入js)
    - [定义 IMPORT-1 ( 内联导入 )](#定义-import-1--内联导入-)
    - [定义 IMPORT-2 ( 自定义类型 )](#定义-import-2--自定义类型-)
  - [6. 定理与证明](#6-定理与证明)
    - [定理 WBG-T1 ( 类型安全边界 )](#定理-wbg-t1--类型安全边界-)
    - [定理 WBG-T2 ( 零拷贝视图 )](#定理-wbg-t2--零拷贝视图-)
  - [7. 代码示例](#7-代码示例)
    - [示例1: 基础导出](#示例1-基础导出)
    - [示例2: DOM操作](#示例2-dom操作)
    - [示例3: 异步HTTP](#示例3-异步http)

---

## 1. 引言

wasm-bindgen功能：

- Rust ↔ JS类型自动转换
- wasm内存管理
- JS API绑定生成
- 异步支持

---

## 2. 类型映射

### 定义 TYPEMAP-1 ( 基本类型 )

| Rust | JavaScript | 传递方式 |
| :--- | :--- | :--- |
| i32/u32/f32/f64 | number | 值 |
| bool | boolean | 值 |
| String | string | 拷贝 |
| &str | string | 借用 |
| Vec<u8> | Uint8Array | 拷贝 |
| JsValue | any | 引用 |

### 定义 TYPEMAP-2 ( 复杂类型 )

```rust
#[wasm_bindgen]
pub struct Point { x: f64, y: f64 }
```

$$
\text{ExportedStruct} \to \text{JS prototype}
$$

---

## 3. 内存管理

### 定义 MEM-1 ( wasm内存模型 )

$$
\text{WasmMemory} = \text{linear\_memory}[0..2^{32})
$$

### 定义 MEM-2 ( 所有权转移 )

```rust
#[wasm_bindgen]
impl Point {
    #[wasm_bindgen(constructor)]
    pub fn new(x: f64, y: f64) -> Point { Point { x, y } }
}
```

### 定理 MEM-T1 ( 无泄漏 )

导出类型正确drop。

$$
\text{JS\_drop}(ptr) \to \text{Rust\_drop}(\text{Box}::\text{from\_raw}(ptr))
$$

---

## 4. 导出函数

### 定义 EXPORT-1 ( 导出语法 )

```rust
#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 { a + b }
```

### 定义 EXPORT-2 ( 异步导出 )

```rust
#[wasm_bindgen]
pub async fn fetch_data(url: String) -> Result<JsValue, JsValue> {
    // async operation
}
```

---

## 5. 导入JS

### 定义 IMPORT-1 ( 内联导入 )

```rust
#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}
```

### 定义 IMPORT-2 ( 自定义类型 )

```rust
#[wasm_bindgen]
extern "C" {
    pub type HTMLElement;

    #[wasm_bindgen(method, getter)]
    fn inner_html(this: &HTMLElement) -> String;
}
```

---

## 6. 定理与证明

### 定理 WBG-T1 ( 类型安全边界 )

FFI边界类型检查。

$$
\text{wasm\_bindgen} \to \text{generated\_glue\_code\_validates\_types}
$$

### 定理 WBG-T2 ( 零拷贝视图 )

&[u8]可零拷贝传递。

$$
\text{&[u8]} \to \text{Uint8Array\_view} \text{ (no copy)}
$$

---

## 7. 代码示例

### 示例1: 基础导出

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct Calculator {
    value: f64,
}

#[wasm_bindgen]
impl Calculator {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Calculator {
        Calculator { value: 0.0 }
    }

    pub fn add(&mut self, n: f64) {
        self.value += n;
    }

    pub fn result(&self) -> f64 {
        self.value
    }
}

#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}
```

### 示例2: DOM操作

```rust
use wasm_bindgen::prelude::*;
use web_sys::{Document, Element, HtmlElement, Window};

#[wasm_bindgen(start)]
pub fn run() -> Result<(), JsValue> {
    let window = web_sys::window().unwrap();
    let document = window.document().unwrap();
    let body = document.body().unwrap();

    let val = document.create_element("p")?;
    val.set_inner_html("Hello from Rust!");
    body.append_child(&val)?;

    Ok(())
}
```

### 示例3: 异步HTTP

```rust
use wasm_bindgen::prelude::*;
use wasm_bindgen_futures::JsFuture;
use web_sys::{Request, RequestInit, Response};

#[wasm_bindgen]
pub async fn fetch_json(url: String) -> Result<JsValue, JsValue> {
    let mut opts = RequestInit::new();
    opts.method("GET");

    let request = Request::new_with_str_and_init(&url, &opts)?;

    let window = web_sys::window().unwrap();
    let resp_value = JsFuture::from(window.fetch_with_request(&request)).await?;
    let resp: Response = resp_value.dyn_into()?;

    let json = JsFuture::from(resp.json()?).await?;
    Ok(json)
}
```

---

**维护者**: Rust WASM Formal Methods Team
**创建日期**: 2026-03-05
**wasm-bindgen版本**: 0.2+
**状态**: ✅ 已对齐
