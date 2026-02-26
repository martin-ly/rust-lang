> **快速参考** | [完整文档](../../../crates/c12_wasm/docs/) | [代码示例](../../../crates/c12_wasm/examples/)
> **创建日期**: 2026-01-27
> **最后更新**: 2026-01-27
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

# WASM 快速参考卡片

---

## 📋 目录 {#-目录}

- [WASM 快速参考卡片](#wasm-快速参考卡片)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [🚀 快速开始 {#-快速开始}](#-快速开始--快速开始)
    - [基本设置](#基本设置)
    - [基本函数](#基本函数)
  - [📋 常用 API {#-常用-api}](#-常用-api--常用-api)
    - [JavaScript 互操作](#javascript-互操作)
    - [处理对象](#处理对象)
    - [异步函数](#异步函数)
  - [🔧 编译配置 {#-编译配置}](#-编译配置--编译配置)
    - [Cargo.toml](#cargotoml)
    - [编译命令](#编译命令)
  - [🌐 在浏览器中使用 {#-在浏览器中使用}](#-在浏览器中使用--在浏览器中使用)
  - [⚡ 性能优化 {#-性能优化}](#-性能优化--性能优化)
    - [减小二进制大小](#减小二进制大小)
    - [使用 wasm-opt](#使用-wasm-opt)
  - [🚫 反例速查 {#-反例速查}](#-反例速查--反例速查)
    - [反例 1: 在 wasm 中使用阻塞 API](#反例-1-在-wasm-中使用阻塞-api)
    - [反例 2: 忽略 JS 边界开销](#反例-2-忽略-js-边界开销)
  - [📚 相关文档 {#-相关文档}](#-相关文档--相关文档)
  - [🧩 相关示例代码 {#-相关示例代码}](#-相关示例代码--相关示例代码)
  - [📚 相关资源 {#-相关资源}](#-相关资源--相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
  - [🎯 使用场景 {#-使用场景}](#-使用场景--使用场景)
    - [场景 1: 浏览器图像处理器](#场景-1-浏览器图像处理器)
    - [场景 2: 实时数据可视化](#场景-2-实时数据可视化)
    - [场景 3: Web Worker 计算密集型任务](#场景-3-web-worker-计算密集型任务)
  - [📐 形式化方法链接 {#-形式化方法链接}](#-形式化方法链接--形式化方法链接)
    - [理论基础](#理论基础)
    - [形式化定理](#形式化定理)
    - [相关速查卡](#相关速查卡)

---

## 🚀 快速开始 {#-快速开始}

### 基本设置

```bash
# 安装 wasm-pack
cargo install wasm-pack

# 创建项目
wasm-pack new my-wasm-project
```

### 基本函数

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

---

## 📋 常用 API {#-常用-api}

### JavaScript 互操作

```rust
#[wasm_bindgen]
extern "C" {
    fn alert(s: &str);

    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}
```

### 处理对象

```rust
#[wasm_bindgen]
pub struct Person {
    name: String,
    age: u32,
}

#[wasm_bindgen]
impl Person {
    #[wasm_bindgen(constructor)]
    pub fn new(name: String, age: u32) -> Person {
        Person { name, age }
    }
}
```

### 异步函数

```rust
use wasm_bindgen_futures::JsFuture;

#[wasm_bindgen]
pub async fn fetch_data(url: &str) -> Result<JsValue, JsValue> {
    let window = web_sys::window().unwrap();
    let resp = JsFuture::from(window.fetch_with_str(url)).await?;
    // ...
}
```

---

## 🔧 编译配置 {#-编译配置}

### Cargo.toml

```toml
[lib]
crate-type = ["cdylib", "rlib"]

[dependencies]
wasm-bindgen = "0.2"
wasm-bindgen-futures = "0.4"
js-sys = "0.3"
web-sys = { version = "0.3", features = ["Window"] }
```

### 编译命令

```bash
# Web 目标
wasm-pack build --target web

# Node.js 目标
wasm-pack build --target nodejs

# Bundler 目标
wasm-pack build --target bundler
```

---

## 🌐 在浏览器中使用 {#-在浏览器中使用}

```html
<script type="module">
  import init, { add } from "./pkg/my_project.js"

  await init()
  console.log(add(2, 3)) // 5
</script>
```

---

## ⚡ 性能优化 {#-性能优化}

### 减小二进制大小

```toml
[profile.release]
opt-level = "z"
lto = true
codegen-units = 1
panic = "abort"
strip = true
```

### 使用 wasm-opt

```bash
wasm-opt -Os pkg/my_project_bg.wasm -o pkg/my_project_optimized.wasm
```

---

## 🚫 反例速查 {#-反例速查}

### 反例 1: 在 wasm 中使用阻塞 API

**错误示例**:

```rust
#[cfg(target_arch = "wasm32")]
fn bad() {
    std::thread::sleep(Duration::from_secs(1));  // ❌ wasm 无线程
}
```

**原因**: wasm 单线程，`thread::sleep` 等会阻塞主线程。

**修正**: 使用 `wasm-bindgen-futures`、`gloo-timers` 等异步定时。

---

### 反例 2: 忽略 JS 边界开销

**错误示例**:

```rust
for i in 0..10000 {
    js_sys::Reflect::get(&obj, &i.into());  // ❌ 每次跨 JS 边界
}
```

**原因**: Rust↔JS 调用有开销，频繁调用会显著影响性能。

**修正**: 批量传递数据，减少跨边界调用次数。

---

## 📚 相关文档 {#-相关文档}

- [WASM 完整文档](../../../crates/c12_wasm/docs/)
- [WASM README](../../../crates/c12_wasm/README.md)

## 🧩 相关示例代码 {#-相关示例代码}

以下示例位于 `crates/c12_wasm/examples/`，可直接运行（例如：`cargo run -p c12_wasm --example 01_basic_add`）。

- [基础加法与导出](../../../crates/c12_wasm/examples/01_basic_add.rs)
- [字符串与数组](../../../crates/c12_wasm/examples/02_string_operations.rs)、[03_array_processing.rs](../../../crates/c12_wasm/examples/03_array_processing.rs)
- [计数器与 WASI](../../../crates/c12_wasm/examples/04_counter_class.rs)、[05_wasi_file_processor.rs](../../../crates/c12_wasm/examples/05_wasi_file_processor.rs)
- [异步 fetch、设计模式、微服务](../../../crates/c12_wasm/examples/06_async_fetch.rs)、[07_design_patterns.rs](../../../crates/c12_wasm/examples/07_design_patterns.rs)、[08_container_microservice.rs](../../../crates/c12_wasm/examples/08_container_microservice.rs)
- [Rust 1.91/1.92 特性演示](../../../crates/c12_wasm/examples/rust_191_features_demo.rs)、[rust_192_features_demo.rs](../../../crates/c12_wasm/examples/rust_192_features_demo.rs)

---

## 📚 相关资源 {#-相关资源}

### 官方文档

- [wasm-bindgen 文档](https://rustwasm.github.io/wasm-bindgen/)
- [wasm-pack 文档](https://rustwasm.github.io/wasm-pack/)
- [WebAssembly 官方文档](https://webassembly.org/)

### 项目内部文档

- [完整文档](../../../crates/c12_wasm/README.md)
- [WASM 使用指南](../../05_guides/WASM_USAGE_GUIDE.md)
- [JavaScript 互操作](../../../crates/c12_wasm/docs/tier_02_guides/03_javascript_互操作.md)

## 🎯 使用场景 {#-使用场景}

### 场景 1: 浏览器图像处理器

```rust
use wasm_bindgen::prelude::*;
use web_sys::{CanvasRenderingContext2d, HtmlCanvasElement, ImageData};

#[wasm_bindgen]
pub struct ImageProcessor {
    width: u32,
    height: u32,
}

#[wasm_bindgen]
impl ImageProcessor {
    #[wasm_bindgen(constructor)]
    pub fn new(width: u32, height: u32) -> Self {
        Self { width, height }
    }

    pub fn grayscale(&self, data: &[u8]) -> Vec<u8> {
        let mut result = data.to_vec();
        for chunk in result.chunks_exact_mut(4) {
            let gray = (0.299 * chunk[0] as f32 +
                       0.587 * chunk[1] as f32 +
                       0.114 * chunk[2] as f32) as u8;
            chunk[0] = gray;
            chunk[1] = gray;
            chunk[2] = gray;
            // chunk[3] is alpha, unchanged
        }
        result
    }

    pub fn blur(&self, data: &[u8], radius: u32) -> Vec<u8> {
        // 简化的盒式模糊算法
        let mut result = data.to_vec();
        // ... 模糊处理逻辑
        result
    }
}
```

### 场景 2: 实时数据可视化

```rust
use wasm_bindgen::prelude::*;
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
pub struct DataPoint {
    x: f64,
    y: f64,
    label: String,
}

#[wasm_bindgen]
pub struct ChartRenderer {
    canvas_id: String,
}

#[wasm_bindgen]
impl ChartRenderer {
    #[wasm_bindgen(constructor)]
    pub fn new(canvas_id: String) -> Self {
        Self { canvas_id }
    }

    pub fn render_line_chart(&self, data_json: &str) -> Result<(), JsValue> {
        let data: Vec<DataPoint> = serde_json::from_str(data_json)
            .map_err(|e| JsValue::from_str(&e.to_string()))?;

        // 获取 canvas 上下文
        let window = web_sys::window().unwrap();
        let document = window.document().unwrap();
        let canvas = document
            .get_element_by_id(&self.canvas_id)
            .ok_or("Canvas not found")?
            .dyn_into::<web_sys::HtmlCanvasElement>()?;

        let context = canvas
            .get_context("2d")?
            .unwrap()
            .dyn_into::<web_sys::CanvasRenderingContext2d>()?;

        // 绘制折线图
        context.clear_rect(0.0, 0.0, canvas.width() as f64, canvas.height() as f64);
        context.begin_path();

        for (i, point) in data.iter().enumerate() {
            let x = (point.x / 100.0) * canvas.width() as f64;
            let y = canvas.height() as f64 - (point.y / 100.0) * canvas.height() as f64;

            if i == 0 {
                context.move_to(x, y);
            } else {
                context.line_to(x, y);
            }
        }

        context.stroke();
        Ok(())
    }
}
```

### 场景 3: Web Worker 计算密集型任务

```rust
// worker.rs
use wasm_bindgen::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Deserialize)]
struct ComputeTask {
    task_id: u32,
    data: Vec<f64>,
}

#[derive(Serialize)]
struct ComputeResult {
    task_id: u32,
    result: f64,
}

#[wasm_bindgen]
pub fn process_task(task_json: &str) -> String {
    let task: ComputeTask = serde_json::from_str(task_json).unwrap();

    // 计算密集型操作（如 FFT、矩阵运算）
    let result = task.data.iter().map(|x| x * x).sum();

    let output = ComputeResult {
        task_id: task.task_id,
        result,
    };

    serde_json::to_string(&output).unwrap()
}
```

---

## 📐 形式化方法链接 {#-形式化方法链接}

### 理论基础

| 概念 | 形式化文档 | 描述 |
| :--- | :--- | :--- |
| **所有权模型** | [ownership_model](../../research_notes/formal_methods/ownership_model.md) | WASM 内存安全保证 |
| **生命周期** | [lifetime_formalization](../../research_notes/formal_methods/lifetime_formalization.md) | JS 互操作引用有效性 |
| **Send/Sync** | [send_sync_formalization](../../research_notes/formal_methods/send_sync_formalization.md) | Web Worker 安全 |
| **类型系统** | [type_system_foundations](../../research_notes/type_theory/type_system_foundations.md) | JS 绑定类型安全 |

### 形式化定理

**定理 WASM-T1（JS 边界安全）**: 若 WASM 模块满足所有权规则，则 JS 互操作无内存不安全。

*证明*: 由 [ownership_model](../../research_notes/formal_methods/ownership_model.md) 定理 T2/T3，wasm-bindgen 生成的绑定保持所有权语义，JS 侧无法直接访问 Rust 内存。∎

---

### 相关速查卡

- [异步编程速查卡](./async_patterns.md) - WASM 异步
- [类型系统速查卡](./type_system.md) - WASM 类型
- [错误处理速查卡](./error_handling_cheatsheet.md) - WASM 错误处理
- [测试速查卡](./testing_cheatsheet.md) - WASM 测试
- [反模式速查卡](./ANTI_PATTERN_TEMPLATE.md) - WASM 反模式

---

**最后更新**: 2026-02-20
**Rust 版本**: 1.93.0+ (Edition 2024)
**提示**: 使用 `cargo doc --open` 查看完整 API 文档
