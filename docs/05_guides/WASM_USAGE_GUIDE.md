# WASM 使用指南

**模块**: C12 WASM
**创建日期**: 2025-12-11
**最后更新**: 2026-02-15
**Rust 版本**: 1.94.0+ (Edition 2024)
**状态**: ✅ 已完成

---

## 📋 目录 {#-目录}

- [WASM 使用指南](#wasm-使用指南)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [📋 概述 {#-概述}](#-概述--概述)
  - [🚀 快速开始 {#-快速开始}](#-快速开始--快速开始)
    - [安装工具链](#安装工具链)
    - [创建 WASM 项目](#创建-wasm-项目)
  - [📊 核心功能 {#-核心功能}](#-核心功能--核心功能)
    - [1. 基本 WASM 函数](#1-基本-wasm-函数)
    - [2. 与 JavaScript 互操作](#2-与-javascript-互操作)
    - [3. 处理 JavaScript 对象](#3-处理-javascript-对象)
    - [4. 异步函数](#4-异步函数)
  - [🔧 编译配置 {#-编译配置}](#-编译配置--编译配置)
    - [1. Cargo.toml](#1-cargotoml)
    - [2. 编译命令](#2-编译命令)
  - [🌐 在浏览器中使用 {#-在浏览器中使用}](#-在浏览器中使用--在浏览器中使用)
    - [1. HTML 示例](#1-html-示例)
    - [2. Node.js 示例](#2-nodejs-示例)
  - [🧪 测试 {#-测试}](#-测试--测试)
    - [1. 单元测试](#1-单元测试)
    - [2. 运行测试](#2-运行测试)
  - [⚡ 性能优化 {#-性能优化}](#-性能优化--性能优化)
    - [1. 减小二进制大小](#1-减小二进制大小)
    - [2. 使用 wasm-opt](#2-使用-wasm-opt)
    - [3. 避免不必要的分配](#3-避免不必要的分配)
  - [使用场景](#使用场景)
    - [场景1: Web 前端开发](#场景1-web-前端开发)
    - [场景2: 跨平台桌面应用](#场景2-跨平台桌面应用)
    - [场景3: 服务端 WASM (Edge Computing)](#场景3-服务端-wasm-edge-computing)
    - [场景4: 插件系统](#场景4-插件系统)
  - [形式化链接](#形式化链接)
  - [📚 相关文档 {#-相关文档}](#-相关文档--相关文档)

---

## 📋 概述 {#-概述}

本指南介绍如何使用 Rust 编译到 WebAssembly (WASM)，包括项目设置、编译配置、与 JavaScript 互操作等。

**形式化引用**：T-ASYNC1 (Future 安全性)、[async_state_machine](../research_notes/formal_methods/async_state_machine.md) T6.1-T6.3。WASM 异步与 Rust 异步模型一致。

---

## 🚀 快速开始 {#-快速开始}

### 安装工具链

```bash
# 安装 wasm-pack
curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh

# 或使用 cargo install
cargo install wasm-pack

# 安装 wasm-bindgen
cargo install wasm-bindgen-cli
```

### 创建 WASM 项目

```bash
# 使用 wasm-pack 创建新项目
wasm-pack new my-wasm-project

# 或手动创建
cargo new --lib my-wasm-project
cd my-wasm-project
```

---

## 📊 核心功能 {#-核心功能}

### 1. 基本 WASM 函数

```rust
// src/lib.rs
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}
```

### 2. 与 JavaScript 互操作

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
extern "C" {
    fn alert(s: &str);

    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}

#[wasm_bindgen]
pub fn show_alert(message: &str) {
    alert(message);
}

#[wasm_bindgen]
pub fn log_message(message: &str) {
    log(message);
}
```

### 3. 处理 JavaScript 对象

```rust
use wasm_bindgen::prelude::*;

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

    #[wasm_bindgen(getter)]
    pub fn name(&self) -> String {
        self.name.clone()
    }

    #[wasm_bindgen(getter)]
    pub fn age(&self) -> u32 {
        self.age
    }
}
```

### 4. 异步函数

```rust
use wasm_bindgen::prelude::*;
use wasm_bindgen_futures::JsFuture;
use js_sys::Promise;

#[wasm_bindgen]
pub async fn fetch_data(url: &str) -> Result<JsValue, JsValue> {
    let window = web_sys::window().unwrap();
    let resp_value = JsFuture::from(
        window.fetch_with_str(url)
    ).await?;

    let resp: web_sys::Response = resp_value.dyn_into()?;
    let json = JsFuture::from(resp.json()?).await?;

    Ok(json)
}
```

---

## 🔧 编译配置 {#-编译配置}

### 1. Cargo.toml

```toml
[package]
name = "my-wasm-project"
version = "0.1.0"
edition = "2024"

[lib]
crate-type = ["cdylib", "rlib"]

[dependencies]
wasm-bindgen = "0.2"
wasm-bindgen-futures = "0.4"
js-sys = "0.3"
web-sys = { version = "0.3", features = [
    "Window",
    "Document",
    "Element",
    "HtmlElement",
] }

[dev-dependencies]
wasm-bindgen-test = "0.3"
```

### 2. 编译命令

```bash
# 使用 wasm-pack 编译
wasm-pack build --target web

# 或指定其他目标
wasm-pack build --target nodejs
wasm-pack build --target bundler
wasm-pack build --target no-modules
```

---

## 🌐 在浏览器中使用 {#-在浏览器中使用}

### 1. HTML 示例

```html
<!DOCTYPE html>
<html>
  <head>
    <meta charset="utf-8" />
    <title>WASM Example</title>
  </head>
  <body>
    <script type="module">
      import init, { add, greet } from "./pkg/my_wasm_project.js"

      async function run() {
        await init()

        console.log(add(2, 3)) // 5
        console.log(greet("World")) // "Hello, World!"
      }

      run()
    </script>
  </body>
</html>
```

### 2. Node.js 示例

```javascript
const wasm = require("./pkg/my_wasm_project.js")

wasm.init().then(() => {
  console.log(wasm.add(2, 3)) // 5
  console.log(wasm.greet("World")) // "Hello, World!"
})
```

---

## 🧪 测试 {#-测试}

### 1. 单元测试

```rust
use wasm_bindgen_test::*;

wasm_bindgen_test_configure!(run_in_browser);

#[wasm_bindgen_test]
fn test_add() {
    assert_eq!(add(2, 3), 5);
}
```

### 2. 运行测试

```bash
wasm-pack test --headless --firefox
wasm-pack test --headless --chrome
wasm-pack test --headless --safari
```

---

## ⚡ 性能优化 {#-性能优化}

### 1. 减小二进制大小

```toml
[profile.release]
opt-level = "z"      # 优化大小
lto = true
codegen-units = 1
panic = "abort"
strip = true
```

### 2. 使用 wasm-opt

```bash
# 安装 wasm-opt
npm install -g wasm-opt

# 优化 WASM 文件
wasm-opt -Os pkg/my_wasm_project_bg.wasm -o pkg/my_wasm_project_optimized.wasm
```

### 3. 避免不必要的分配

```rust
// ❌ 不好：多次分配
pub fn process(data: &str) -> String {
    data.to_uppercase()
        .trim()
        .to_string()
}

// ✅ 好：减少分配
pub fn process(data: &str) -> String {
    data.trim().to_uppercase()
}
```

---

## 使用场景

### 场景1: Web 前端开发

在浏览器中使用 Rust 替代 JavaScript：

```rust
// 使用 wasm-bindgen 导出函数给 JS 调用
// 使用 web-sys 操作 DOM
// 适用于：计算密集型任务、游戏引擎、图像处理
```

### 场景2: 跨平台桌面应用

使用 WASM 构建跨平台应用：

- 使用 Tauri 或 Electron 包装 WASM 模块
- 共享 Rust 核心逻辑
- 参考 [C12 WASM 完整文档](../../crates/c12_wasm/README.md)

### 场景3: 服务端 WASM (Edge Computing)

在边缘节点运行 WASM：

- 轻量级、快速启动
- 安全的沙箱环境
- 结合 [EMBEDDED_RUST_GUIDE.md](./EMBEDDED_RUST_GUIDE.md) 进行边缘部署

### 场景4: 插件系统

构建支持 WASM 插件的应用：

- 宿主程序使用 Rust/C++/其他语言
- 插件使用 Rust 编译为 WASM
- 安全的插件隔离机制

---

## 形式化链接

| 链接类型 | 目标文档 |
| :--- | :--- |
| **核心模块** | [C12 WASM](../../crates/c12_wasm/docs/tier_01_foundations/02_主索引导航.md) |
| :--- | :--- |
| :--- | :--- |
| **C12 详细文档** | [WASM 基础指南](../../crates/c12_wasm/docs/tier_02_guides/01_wasm_基础指南.md) |
| :--- | :--- |
| **相关指南** | [EMBEDDED_RUST_GUIDE.md](./EMBEDDED_RUST_GUIDE.md) |
| :--- | :--- |
| :--- | :--- |
| **外部资源** | [wasm-bindgen 文档](https://rustwasm.github.io/wasm-bindgen/) |
| :--- | :--- |

---

## 📚 相关文档 {#-相关文档}

- [完整文档](../../crates/c12_wasm/README.md)
- [WASM 指南](../../crates/c12_wasm/docs/tier_02_guides/01_wasm_基础指南.md)
- [JavaScript 互操作](../../crates/c12_wasm/docs/tier_02_guides/03_javascript_互操作.md)

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 完整实现
**最后更新**: 2026-01-26
