# WASM 快速参考卡片

**模块**: C12 WASM
**Rust 版本**: 1.93.0+
**最后更新**: 2026-01-27

---

## 📋 目录

- [WASM 快速参考卡片](#wasm-快速参考卡片)
  - [📋 目录](#-目录)
  - [🚀 快速开始](#-快速开始)
    - [基本设置](#基本设置)
    - [基本函数](#基本函数)
  - [📋 常用 API](#-常用-api)
    - [JavaScript 互操作](#javascript-互操作)
    - [处理对象](#处理对象)
    - [异步函数](#异步函数)
  - [🔧 编译配置](#-编译配置)
    - [Cargo.toml](#cargotoml)
    - [编译命令](#编译命令)
  - [🌐 在浏览器中使用](#-在浏览器中使用)
  - [⚡ 性能优化](#-性能优化)
    - [减小二进制大小](#减小二进制大小)
    - [使用 wasm-opt](#使用-wasm-opt)
  - [📚 相关文档](#-相关文档)
  - [🧩 相关示例代码](#-相关示例代码)
  - [📚 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [相关速查卡](#相关速查卡)

---

## 🚀 快速开始

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

## 📋 常用 API

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

## 🔧 编译配置

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

## 🌐 在浏览器中使用

```html
<script type="module">
  import init, { add } from "./pkg/my_project.js"

  await init()
  console.log(add(2, 3)) // 5
</script>
```

---

## ⚡ 性能优化

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

## 📚 相关文档

- [WASM 完整文档](../../crates/c12_wasm/docs/)
- [WASM README](../../crates/c12_wasm/README.md)

## 🧩 相关示例代码

以下示例位于 `crates/c12_wasm/examples/`，可直接运行（例如：`cargo run -p c12_wasm --example 01_basic_add`）。

- [基础加法与导出](../../crates/c12_wasm/examples/01_basic_add.rs)
- [字符串与数组](../../crates/c12_wasm/examples/02_string_operations.rs)、[03_array_processing.rs](../../crates/c12_wasm/examples/03_array_processing.rs)
- [计数器与 WASI](../../crates/c12_wasm/examples/04_counter_class.rs)、[05_wasi_file_processor.rs](../../crates/c12_wasm/examples/05_wasi_file_processor.rs)
- [异步 fetch、设计模式、微服务](../../crates/c12_wasm/examples/06_async_fetch.rs)、[07_design_patterns.rs](../../crates/c12_wasm/examples/07_design_patterns.rs)、[08_container_microservice.rs](../../crates/c12_wasm/examples/08_container_microservice.rs)
- [Rust 1.91/1.92 特性演示](../../crates/c12_wasm/examples/rust_191_features_demo.rs)、[rust_192_features_demo.rs](../../crates/c12_wasm/examples/rust_192_features_demo.rs)

---

## 📚 相关资源

### 官方文档

- [wasm-bindgen 文档](https://rustwasm.github.io/wasm-bindgen/)
- [wasm-pack 文档](https://rustwasm.github.io/wasm-pack/)
- [WebAssembly 官方文档](https://webassembly.org/)

### 项目内部文档

- [完整文档](../../crates/c12_wasm/README.md)
- [WASM 使用指南](../../docs/WASM_USAGE_GUIDE.md)
- [JavaScript 互操作](../../crates/c12_wasm/docs/tier_02_guides/03_javascript_互操作.md)

### 相关速查卡

- [异步编程速查卡](./async_patterns.md) - WASM 异步
- [类型系统速查卡](./type_system.md) - WASM 类型
- [错误处理速查卡](./error_handling_cheatsheet.md) - WASM 错误处理
- [测试速查卡](./testing_cheatsheet.md) - WASM 测试

---

**最后更新**: 2026-01-27
**Rust 版本**: 1.93.0+ (Edition 2024)
**提示**: 使用 `cargo doc --open` 查看完整 API 文档
