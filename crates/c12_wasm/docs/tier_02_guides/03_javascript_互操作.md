# C12 WASM - JavaScript 互操作

> **文档类型**: Tier 2 - 实践层
> **文档定位**: WASM 与 JavaScript 集成指南
> **项目状态**: ✅ 完整完成
> **相关文档**: [Rust 编译 WASM](./02_rust_编译_wasm.md) | [性能优化指南](./04_性能优化指南.md)

**最后更新**: 2025-12-11
**适用版本**: Rust 1.92.0+ / Edition 2024, WASM 2.0 + WASI 0.2
**Rust 1.92.0 特性**: 本文档已集成 Rust 1.92.0 FFI 互操作特性

---

## 📋 目录

- [C12 WASM - JavaScript 互操作](#c12-wasm---javascript-互操作)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [📐 知识结构](#-知识结构)
    - [概念定义](#概念定义)
    - [属性特征](#属性特征)
    - [关系连接](#关系连接)
    - [思维导图](#思维导图)
  - [🔗 基础集成](#-基础集成)
    - [加载 WASM 模块](#加载-wasm-模块)
  - [⚛️ React 集成](#️-react-集成)
    - [基本用法](#基本用法)
    - [自定义 Hook](#自定义-hook)
  - [🎨 Vue 集成](#-vue-集成)
    - [Vue 基本用法](#vue-基本用法)
  - [🟢 Node.js 集成](#-nodejs-集成)
    - [Node.js 基本用法](#nodejs-基本用法)
    - [ES 模块](#es-模块)
  - [📦 TypeScript 类型](#-typescript-类型)
    - [使用类型](#使用类型)
  - [🌐 Web API 集成](#-web-api-集成)
    - [Fetch API](#fetch-api)
    - [Canvas API](#canvas-api)
  - [🚀 实践示例](#-实践示例)
    - [示例 1: 简单计算](#示例-1-简单计算)
    - [示例 2: 数组处理](#示例-2-数组处理)
  - [🔗 Rust 1.92.0 FFI 互操作 ⭐ NEW](#-rust-1920-ffi-互操作--new)
    - [使用联合体原始引用进行安全的 FFI 互操作](#使用联合体原始引用进行安全的-ffi-互操作)
  - [📚 相关资源](#-相关资源)

---

## 🎯 概述

本指南介绍如何在各种环境中集成 WASM 模块：

- 浏览器基础集成
- React/Vue/Angular 框架集成
- Node.js 运行时集成
- TypeScript 类型定义
- Web API 使用

## 📐 知识结构

### 概念定义

**JavaScript 互操作 (JavaScript Interop)**:

- **定义**: Rust WASM 模块与 JavaScript 代码之间的交互机制
- **类型**: 复合概念
- **范畴**: 跨语言编程
- **版本**: Rust 1.30+ (wasm-bindgen)
- **相关概念**: wasm-bindgen、类型转换、内存管理

**wasm-bindgen**:

- **定义**: Rust 与 JavaScript 的绑定工具，自动生成互操作代码
- **类型**: 工具/库
- **属性**: 类型转换、函数绑定、类型安全
- **关系**: 与 WASM、JavaScript 相关

### 属性特征

**核心属性**:

- **类型安全**: 编译时类型检查
- **自动转换**: 自动处理类型转换
- **内存管理**: 自动管理 WASM 内存
- **跨平台**: 支持浏览器和 Node.js

**性能特征**:

- **调用开销**: 最小化跨语言调用开销
- **内存效率**: 高效的内存共享机制
- **适用场景**: Web 应用、Node.js 应用、跨平台开发

### 关系连接

**组合关系**:

- WASM 模块 --[uses]--> wasm-bindgen
- wasm-bindgen --[generates]--> JavaScript 绑定

**依赖关系**:

- JavaScript 互操作 --[depends-on]--> WASM 模块
- JavaScript 互操作 --[depends-on]--> wasm-bindgen

### 思维导图

```text
JavaScript 互操作
│
├── 基础集成
│   ├── ES 模块
│   └── 动态导入
├── 框架集成
│   ├── React
│   ├── Vue
│   └── Angular
├── 运行时集成
│   ├── Node.js
│   └── Deno
├── 类型系统
│   ├── TypeScript
│   └── 类型定义
└── Web API
    ├── Fetch API
    └── Canvas API
```

---

## 🔗 基础集成

### 加载 WASM 模块

```javascript
// 方式 1: 使用 ES 模块
import init, { greet } from './pkg/hello_wasm';

async function loadWasm() {
  await init();
  const result = greet("World");
  console.log(result);
}

loadWasm();
```

```javascript
// 方式 2: 使用动态导入
const wasmModule = await import('./pkg/hello_wasm');
await wasmModule.default();
const result = wasmModule.greet("World");
```

---

## ⚛️ React 集成

### 基本用法

```jsx
import React, { useEffect, useState } from 'react';
import init, { greet } from './pkg/hello_wasm';

function App() {
  const [wasmReady, setWasmReady] = useState(false);

  useEffect(() => {
    init().then(() => {
      setWasmReady(true);
    });
  }, []);

  if (!wasmReady) {
    return <div>Loading WASM...</div>;
  }

  return (
    <div>
      <h1>{greet("React")}</h1>
    </div>
  );
}
```

### 自定义 Hook

```jsx
function useWasm() {
  const [wasm, setWasm] = useState(null);

  useEffect(() => {
    import('./pkg/hello_wasm').then(module => {
      module.default().then(() => {
        setWasm(module);
      });
    });
  }, []);

  return wasm;
}
```

---

## 🎨 Vue 集成

### Vue 基本用法

```vue
<template>
  <div>
    <h1>{{ message }}</h1>
  </div>
</template>

<script>
import init, { greet } from './pkg/hello_wasm';

export default {
  data() {
    return {
      message: 'Loading...'
    };
  },
  async mounted() {
    await init();
    this.message = greet('Vue');
  }
};
</script>
```

---

## 🟢 Node.js 集成

### Node.js 基本用法

```javascript
// 使用 wasm-pack 的 nodejs 目标
const wasm = require('./pkg/hello_wasm');

async function main() {
  await wasm.default();
  const result = wasm.greet("Node.js");
  console.log(result);
}

main();
```

### ES 模块

```javascript
import init, { greet } from './pkg/hello_wasm.js';

await init();
const result = greet("Node.js");
console.log(result);
```

---

## 📦 TypeScript 类型

wasm-pack 会自动生成 TypeScript 类型定义文件：

```typescript
// pkg/hello_wasm.d.ts
export function greet(name: string): string;
export class Counter {
  constructor();
  increment(): void;
  readonly value: number;
}
```

### 使用类型

```typescript
import init, { greet, Counter } from './pkg/hello_wasm';

await init();
const result: string = greet("TypeScript");
const counter = new Counter();
counter.increment();
```

---

## 🌐 Web API 集成

### Fetch API

```rust
use wasm_bindgen::prelude::*;
use wasm_bindgen_futures::JsFuture;
use web_sys::{Request, RequestInit, RequestMode, Response};

#[wasm_bindgen]
pub async fn fetch_url(url: &str) -> Result<JsValue, JsValue> {
    let mut opts = RequestInit::new();
    opts.set_method("GET");
    opts.set_mode(RequestMode::Cors);

    let request = Request::new_with_str_and_init(url, &opts)?;
    let window = web_sys::window().unwrap();
    let resp_value = JsFuture::from(window.fetch_with_request(&request)).await?;
    let resp: Response = resp_value.dyn_into()?;
    let json = JsFuture::from(resp.json()?).await?;
    Ok(json)
}
```

### Canvas API

```rust
use wasm_bindgen::prelude::*;
use web_sys::HtmlCanvasElement;

#[wasm_bindgen]
pub fn draw_circle(canvas: &HtmlCanvasElement, x: f64, y: f64, radius: f64) {
    let context = canvas
        .get_context("2d")
        .unwrap()
        .unwrap()
        .dyn_into::<web_sys::CanvasRenderingContext2d>()
        .unwrap();

    context.begin_path();
    context.arc(x, y, radius, 0.0, 2.0 * std::f64::consts::PI).unwrap();
    context.fill();
}
```

---

## 🚀 实践示例

### 示例 1: 简单计算

```rust
#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

```javascript
import { add } from './pkg/hello_wasm';
const result = add(2, 3); // 5
```

### 示例 2: 数组处理

```rust
#[wasm_bindgen]
pub fn sum_array(arr: &[i32]) -> i32 {
    arr.iter().sum()
}
```

```javascript
import { sum_array } from './pkg/hello_wasm';
const result = sum_array(new Int32Array([1, 2, 3, 4, 5])); // 15
```

---

## 🔗 Rust 1.92.0 FFI 互操作 ⭐ NEW

### 使用联合体原始引用进行安全的 FFI 互操作

Rust 1.92.0 允许在安全代码中使用原始引用访问联合体字段，特别适用于 FFI 互操作：

```rust
use c12_wasm::rust_192_features::WasmFFIUnion;

// 创建 FFI 联合体
let mut union = WasmFFIUnion::new();
union.set_integer(0x12345678);

// Rust 1.92.0: 允许在安全代码中使用原始引用
let raw_ref = union.get_integer_raw();
let mut_raw_ref = union.get_integer_mut_raw();

// 可以安全地传递给外部函数
// extern "C" {
//     fn process_union(ptr: *const u32);
// }
// unsafe {
//     process_union(raw_ref);
// }
```

**优势**:

- ✅ 允许在安全代码中使用原始引用
- ✅ 类型安全保证
- ✅ 更好的 FFI 互操作支持

**相关文档**: [Rust 1.92.0 WASM 改进文档](../RUST_192_WASM_IMPROVEMENTS.md)

---

## 📚 相关资源

- [Rust 编译 WASM](./02_rust_编译_wasm.md) - 学习编译流程
- [性能优化指南](./04_性能优化指南.md) - 学习优化
- [最佳实践](../tier_03_references/03_最佳实践.md) - 开发规范
- [Rust 1.92.0 WASM 改进文档](../RUST_192_WASM_IMPROVEMENTS.md) - Rust 1.92.0 特性

**外部资源**:

- [wasm-bindgen Book](https://rustwasm.github.io/docs/wasm-bindgen/)
- [Web APIs](https://rustwasm.github.io/wasm-bindgen/web-sys/index.html)

---

**文档维护**: Documentation Team
**创建日期**: 2025-10-30
**适用版本**: Rust 1.92.0+ / Edition 2024, WASM 2.0 + WASI 0.2
