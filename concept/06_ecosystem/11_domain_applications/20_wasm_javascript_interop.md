> **EN**: WebAssembly JavaScript Interop
> **Summary**: Authoritative concept page for `C12 WASM - JavaScript 互操作`. Content migrated from `crates/c12_wasm/docs/tier_02_guides/03_javascript_interop.md`.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [进阶]
> **内容分级**: [参考级]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **A+S** — Application + Structure
> **双维定位**: A×App — wasm/JS 互操作应用
> **前置依赖**: [WebAssembly](03_webassembly.md) · [Wasm FAQ](19_wasm_faq.md)
> **后置概念**: [Rust WebAssembly Advanced](17_webassembly_advanced.md) · [Web Frameworks](../04_web_and_networking/03_web_frameworks.md)
> **定理链**: wasm-bindgen ⟹ Type Mapping ⟹ Runtime Interaction
>
> **权威来源**: 本页为 `WebAssembly JavaScript Interop` 的权威概念页；crate 文档仅保留导航 stub。

# C12 WASM - JavaScript 互操作

> **文档类型**: Tier 2 - 实践层
> **文档定位**: WASM 与 JavaScript 集成指南
> **项目状态**: ✅ 完整完成
> **相关文档**: [Rust 编译 WASM](/crates/c12_wasm/docs/tier_02_guides/02_compiling_rust_to_wasm.md) | [性能优化指南](/crates/c12_wasm/docs/tier_02_guides/04_performance_optimization_guide.md)

**最后更新**: 2025-12-11
**适用版本**: Rust 1.97.0+ / Edition 2024, WASM 2.0 + WASI 0.2
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
  - [过渡段](#过渡段)
  - [定理链](#定理链)
  - [国际权威参考 / International Authority References（P1 学术 · P2 生态）](#国际权威参考--international-authority-referencesp1-学术--p2-生态)

---

## 🎯 概述

本指南介绍如何在各种环境中集成 WASM 模块（Module）：

- 浏览器基础集成
- React/Vue/Angular 框架集成
- Node.js 运行时（Runtime）集成
- TypeScript 类型定义
- Web API 使用

## 📐 知识结构

「知识结构」涉及概念定义、属性特征、关系连接与思维导图，本节逐一说明其要点。

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

WASM 模块的加载链路分四步，每步都有明确的失败模式：

1. **获取字节码**：`fetch('module.wasm')` 或打包器内联 base64；
2. **编译/实例化**：`WebAssembly.instantiateStreaming`（流式编译，首选）→ 返回 `{ module, instance }`；
3. **导入对象（imports）**：宿主向 WASM 注入 JS 函数、内存或全局变量——签名不匹配在此阶段抛 `LinkError`；
4. **调用导出函数**：`instance.exports.add(1, 2)`。

`wasm-bindgen` 的价值在于把 2–4 步的胶水代码（字符串编解码、结构体序列化）自动生成：`#[wasm_bindgen]` 标注的 Rust 函数会生成同名 JS 包装，`wasm-pack build --target web` 产出可直接 `import` 的 ES 模块。

判定依据：新项目一律用 `instantiateStreaming` + wasm-bindgen 生成胶水；手写 `WebAssembly.Memory` 互操作仅在调试 ABI 问题时必要。

### 加载 WASM 模块

```javascript
// 方式 1: 使用 ES 模块
import init, { greet } from "./pkg/hello_wasm"

async function loadWasm() {
  await init()
  const result = greet("World")
  console.log(result)
}

loadWasm()
```

```javascript
// 方式 2: 使用动态导入
const wasmModule = await import("./pkg/hello_wasm")
await wasmModule.default()
const result = wasmModule.greet("World")
```

---

## ⚛️ React 集成

React 集成 WASM 的推荐模式是**把 WASM 模块封装为自定义 Hook**，隔离异步初始化与组件生命周期：

```text
useWasm() → { ready, api }   // api 在 ready 前为 null
```

两个工程陷阱：

1. **初始化竞态**：`WebAssembly.instantiate` 是异步的，组件挂载期间多次触发会导致重复实例化——用模块级单例 Promise 去重；
2. **渲染热路径**：每次 React render 都跨 JS↔WASM 边界传字符串会造成 GC 压力，应把 WASM 调用收敛到 `useMemo`/`useEffect` 中，边界两侧优先传 `Float64Array` 视图而非 JSON。

判定依据：WASM 适合「一次性重计算」（图像滤镜、物理模拟），不适合「高频小调用」（每帧状态读取）——后者边界穿越成本会吞掉计算收益。

### 基本用法

```jsx
import React, { useEffect, useState } from "react"
import init, { greet } from "./pkg/hello_wasm"

function App() {
  const [wasmReady, setWasmReady] = useState(false)

  useEffect(() => {
    init().then(() => {
      setWasmReady(true)
    })
  }, [])

  if (!wasmReady) {
    return <div>Loading WASM...</div>
  }

  return (
    <div>
      <h1>{greet("React")}</h1>
    </div>
  )
}
```

### 自定义 Hook

```jsx
function useWasm() {
  const [wasm, setWasm] = useState(null)

  useEffect(() => {
    import("./pkg/hello_wasm").then(module => {
      module.default().then(() => {
        setWasm(module)
      })
    })
  }, [])

  return wasm
}
```

---

## 🎨 Vue 集成

「Vue 集成」部分的核心主题是 Vue 基本用法，本节展开说明。

### Vue 基本用法

```vue
<template>
  <div>
    <h1>{{ message }}</h1>
  </div>
</template>

<script>
import init, { greet } from "./pkg/hello_wasm"

export default {
  data() {
    return {
      message: "Loading...",
    }
  },
  async mounted() {
    await init()
    this.message = greet("Vue")
  },
}
</script>
```

---

## 🟢 Node.js 集成

Node.js 集成与浏览器的核心差异是**加载方式与目标三元组**：

- Node 侧用 `fs.readFileSync` + `WebAssembly.instantiate`，或（Node ≥16）直接 `import` WASM 模块（需 `--experimental-wasm-modules`）；
- `wasm-pack build --target nodejs` 产出 CommonJS 胶水，`--target bundler` 产出给 webpack 的 ESM；选错目标是「`__wbindgen_placeholder__` 未定义」类错误的头号原因；
- 需要文件系统/网络时，浏览器走 `--target web` + JS shim，Node 可编 `wasm32-wasip1` 目标获得 WASI 系统接口。

判定依据：纯计算模块选 `--target nodejs`；既跑浏览器又跑 Node 的库应发双产物（两个 target 各一份），不要试图用单一产物兼容两侧。

### Node.js 基本用法

```javascript
// 使用 wasm-pack 的 nodejs 目标
const wasm = require("./pkg/hello_wasm")

async function main() {
  await wasm.default()
  const result = wasm.greet("Node.js")
  console.log(result)
}

main()
```

### ES 模块

```javascript
import init, { greet } from "./pkg/hello_wasm.js"

await init()
const result = greet("Node.js")
console.log(result)
```

---

## 📦 TypeScript 类型

wasm-pack 会自动生成 TypeScript 类型定义文件：

```typescript
// pkg/hello_wasm.d.ts
export function greet(name: string): string
export class Counter {
  constructor()
  increment(): void
  readonly value: number
}
```

### 使用类型

```typescript
import init, { greet, Counter } from "./pkg/hello_wasm"

await init()
const result: string = greet("TypeScript")
const counter = new Counter()
counter.increment()
```

---

## 🌐 Web API 集成

本节从 Fetch API 与  Canvas API 两个层面剖析「Web API 集成」。

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

「实践示例」部分包含示例 1: 简单计算 与 示例 2: 数组处理 两条主线，本节依次说明。

### 示例 1: 简单计算

```rust
#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

```javascript
import { add } from "./pkg/hello_wasm"
const result = add(2, 3) // 5
```

### 示例 2: 数组处理

```rust
#[wasm_bindgen]
pub fn sum_array(arr: &[i32]) -> i32 {
    arr.iter().sum()
}
```

```javascript
import { sum_array } from "./pkg/hello_wasm"
const result = sum_array(new Int32Array([1, 2, 3, 4, 5])) // 15
```

---

## 🔗 Rust 1.92.0 FFI 互操作 ⭐ NEW

本节专门讨论「Rust 1.92.0 FFI 互操作 ⭐ NEW」下的使用联合体原始引用进行安全的 FFI 互操作。

### 使用联合体原始引用进行安全的 FFI 互操作

Rust 1.92.0 允许在安全代码中使用原始引用（Reference）访问联合体字段，特别适用于 FFI 互操作：

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

**相关文档**: [Rust 1.92.0 WASM 改进文档](/crates/c12_wasm/docs/15_rust_192_wasm_improvements.md)

---

## 📚 相关资源

- [Rust 编译 WASM](/crates/c12_wasm/docs/tier_02_guides/02_compiling_rust_to_wasm.md) - 学习编译流程
- [性能优化指南](/crates/c12_wasm/docs/tier_02_guides/04_performance_optimization_guide.md) - 学习优化
- [最佳实践](/crates/c12_wasm/docs/tier_03_references/03_best_practices.md) - 开发规范
- [Rust 1.92.0 WASM 改进文档](/crates/c12_wasm/docs/15_rust_192_wasm_improvements.md) - Rust 1.92.0 特性

**外部资源**:

- [wasm-bindgen Book](https://rustwasm.github.io/docs/wasm-bindgen/)
- [Web APIs](https://rustwasm.github.io/wasm-bindgen/web-sys/index.html)

---

**文档维护**: Documentation Team
**创建日期**: 2025-10-30
**适用版本**: Rust 1.97.0+ / Edition 2024, WASM 2.0 + WASI 0.2

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

> **向下引用**: 参见 [08_rust_vs_javascript](../../05_comparative/02_managed_languages/03_rust_vs_javascript.md)

## 过渡段

> **过渡**: 从原始 wasm 模块过渡到 wasm-bindgen，可以理解绑定生成器如何简化 JS 互操作。
>
> **过渡**: 从类型映射过渡到内存所有权（Ownership），可以建立安全共享数据的责任边界。
>
> **过渡**: 从运行时（Runtime）交互过渡到错误处理（Error Handling），可以形成健壮的跨语言调用模式。
>

## 定理链

| 定理 | 前提 | 结论 |
|:---|:---|:---|
| wasm-bindgen ⟹ 人体工学绑定 | 自动生成 JS/TS 胶水代码 | 大幅减少手写样板 |
| 显式内存所有权（Ownership） ⟹ 安全性 | Rust 管理 wasm 线性内存 | 避免 use-after-free |
| 类型化接口 ⟹ 更少 bug | 强类型绑定替代动态调用 | 编译期捕获接口错误 |

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/wasm-bindgen — 生态权威 API 文档](https://docs.rs/wasm-bindgen) · [docs.rs/wasmtime — 生态权威 API 文档](https://docs.rs/wasmtime)
- **P1 学术/形式化**: [Haas et al.: Bringing the Web up to Speed with WebAssembly (PLDI 2017)](https://dl.acm.org/doi/10.1145/3062341.3062363)
