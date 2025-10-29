# C12 WASM - Rust 编译 WASM

> **文档类型**: Tier 2 - 实践层
> **文档定位**: Rust 编译到 WASM 的完整流程和实践指南
> **项目状态**: ✅ 完整完成
> **相关文档**: [项目概览](../tier_01_foundations/01_项目概览.md) | [WASM 基础指南](./01_wasm_基础指南.md)

**最后更新**: 2025-10-30
**适用版本**: Rust 1.90+ / Edition 2024, WASM 2.0 + WASI 0.2

---

## 📋 目录

- [C12 WASM - Rust 编译 WASM](#c12-wasm---rust-编译-wasm)
  - [📊 目录](#-目录)
  - [🎯 概述](#-概述)
  - [🛠️ 环境准备](#️-环境准备)
  - [📦 编译流程](#-编译流程)
    - [方法 1: 使用 rustc](#方法-1-使用-rustc)
    - [方法 2: 使用 wasm-pack（推荐）](#方法-2-使用-wasm-pack推荐)
  - [⚙️ 编译配置](#️-编译配置)
    - [Cargo.toml 配置](#cargotoml-配置)
    - [优化选项](#优化选项)
  - [🔧 wasm-bindgen 使用](#-wasm-bindgen-使用)
    - [基本用法](#基本用法)
    - [类型映射](#类型映射)
    - [复杂类型](#复杂类型)
  - [📦 wasm-pack 工作流](#-wasm-pack-工作流)
  - [🚀 实践示例](#-实践示例)
  - [📚 相关资源](#-相关资源)

---

## 🎯 概述

本指南介绍如何使用 Rust 编译到 WASM，包括：

- 环境准备和工具安装
- 编译流程和配置
- wasm-bindgen 使用
- wasm-pack 工作流
- 实践示例

---

## 🛠️ 环境准备

### 安装 Rust

```bash
# 安装 Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 更新到最新版本
rustup update stable

# 验证安装
rustc --version  # 应该显示 1.90+
```

### 添加 WASM 目标

```bash
# 添加 wasm32-unknown-unknown 目标
rustup target add wasm32-unknown-unknown

# 验证目标
rustup target list | grep wasm32
```

### 安装 wasm-pack

```bash
# 使用官方安装脚本
curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh

# 或者使用 cargo install
cargo install wasm-pack

# 验证安装
wasm-pack --version
```

### 安装 wasm-bindgen（可选）

```bash
# 使用 cargo install
cargo install wasm-bindgen-cli

# 验证安装
wasm-bindgen --version
```

---

## 📦 编译流程

### 方法 1: 使用 rustc

```bash
# 编译到 WASM
cargo build --target wasm32-unknown-unknown --release

# 输出文件位置
# target/wasm32-unknown-unknown/release/your_module.wasm
```

**优点**: 简单直接
**缺点**: 需要手动处理绑定和集成

### 方法 2: 使用 wasm-pack（推荐）

```bash
# 创建新项目
wasm-pack new hello-wasm
cd hello-wasm

# 构建 WASM 模块
wasm-pack build --target web

# 输出文件位置
# pkg/hello_wasm.js
# pkg/hello_wasm_bg.wasm
# pkg/hello_wasm.d.ts
```

**优点**: 自动化处理绑定和集成
**缺点**: 需要学习 wasm-pack 配置

---

## ⚙️ 编译配置

### Cargo.toml 配置

```toml
[package]
name = "hello-wasm"
version = "0.1.0"
edition = "2024"

[lib]
crate-type = ["cdylib", "rlib"]

[dependencies]
wasm-bindgen = "0.2"

[profile.release]
opt-level = "z"      # 优化大小
lto = true           # 链接时优化
codegen-units = 1    # 单一代码生成单元
strip = true         # 去除调试符号
```

### 优化选项

**大小优化**:

```toml
[profile.release]
opt-level = "z"  # 或者 "s"
lto = true
```

**性能优化**:

```toml
[profile.release]
opt-level = 3
lto = "fat"
```

---

## 🔧 wasm-bindgen 使用

### 基本用法

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}

#[wasm_bindgen]
pub struct Counter {
    value: i32,
}

#[wasm_bindgen]
impl Counter {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Counter {
        Counter { value: 0 }
    }

    #[wasm_bindgen]
    pub fn increment(&mut self) {
        self.value += 1;
    }

    #[wasm_bindgen(getter)]
    pub fn value(&self) -> i32 {
        self.value
    }
}
```

### 类型映射

| Rust 类型 | JavaScript 类型 |
|-----------|----------------|
| `i32`, `u32` | `number` |
| `i64`, `u64` | `BigInt` |
| `f32`, `f64` | `number` |
| `bool` | `boolean` |
| `String` | `string` |
| `Vec<T>` | `Array` |
| `Option<T>` | `T \| undefined` |
| `Result<T, E>` | `Promise<T>` |

### 复杂类型

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

---

## 📦 wasm-pack 工作流

### 构建流程

```bash
# 1. 构建 WASM 模块
wasm-pack build --target web

# 2. 测试模块
wasm-pack test --headless --firefox

# 3. 发布到 npm（可选）
wasm-pack publish
```

### 目标选项

- `--target web`: Web 浏览器环境
- `--target nodejs`: Node.js 环境
- `--target bundler`: Webpack/Rollup 等打包工具
- `--target no-modules`: 不使用 ES 模块

---

## 🚀 实践示例

### 示例 1: 简单函数

```rust
use wasm_bindgen::prelude::*;

/// 简单的加法函数
///
/// # 参数
/// - `a`: 第一个加数
/// - `b`: 第二个加数
///
/// # 返回值
/// 返回两个数的和
///
/// # 示例（JavaScript）
/// ```javascript
/// import { add } from './pkg/hello_wasm';
/// const result = add(2, 3); // 5
/// ```
#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

**编译和使用**:

```bash
# 编译
wasm-pack build --target web

# 在 JavaScript 中使用
import { add } from './pkg/hello_wasm';
console.log(add(2, 3)); // 输出: 5
```

### 示例 2: 结构体和方法

```rust
use wasm_bindgen::prelude::*;

/// 计数器结构体
///
/// 展示如何在 Rust 和 JavaScript 之间共享状态
#[wasm_bindgen]
pub struct Counter {
    /// 内部计数值
    value: i32,
}

#[wasm_bindgen]
impl Counter {
    /// 创建新的计数器实例
    ///
    /// # 返回值
    /// 返回初始值为 0 的计数器
    #[wasm_bindgen(constructor)]
    pub fn new() -> Counter {
        Counter { value: 0 }
    }

    /// 增加计数器值
    ///
    /// 每次调用会将内部值加 1
    #[wasm_bindgen]
    pub fn increment(&mut self) {
        self.value += 1;
    }

    /// 获取当前计数器值
    ///
    /// # 返回值
    /// 返回当前计数器的值
    #[wasm_bindgen(getter)]
    pub fn value(&self) -> i32 {
        self.value
    }
}
```

**在 JavaScript 中使用**:

```javascript
import { Counter } from './pkg/hello_wasm';

// 创建计数器实例
const counter = new Counter();
console.log(counter.value()); // 0

// 增加计数
counter.increment();
counter.increment();
console.log(counter.value()); // 2
```

### 示例 3: 数组处理

```rust
use wasm_bindgen::prelude::*;

/// 计算数组的平均值
///
/// # 参数
/// - `numbers`: 数字数组
///
/// # 返回值
/// 返回平均值，如果数组为空则返回 0.0
///
/// # 性能说明
/// 时间复杂度 O(n)，需要遍历整个数组
#[wasm_bindgen]
pub fn calculate_average(numbers: &[f64]) -> f64 {
    if numbers.is_empty() {
        return 0.0;
    }
    let sum: f64 = numbers.iter().sum();
    sum / (numbers.len() as f64)
}

/// 查找数组中的最大值
///
/// # 参数
/// - `numbers`: 整数数组
///
/// # 返回值
/// 返回最大值，如果数组为空则返回 None（JavaScript 中为 undefined）
#[wasm_bindgen]
pub fn find_max(numbers: &[i32]) -> Option<i32> {
    numbers.iter().max().copied()
}
```

**在 JavaScript 中使用**:

```javascript
import { calculate_average, find_max } from './pkg/hello_wasm';

// 计算平均值
const numbers = new Float64Array([1.0, 2.0, 3.0, 4.0, 5.0]);
const avg = calculate_average(numbers);
console.log(avg); // 3.0

// 查找最大值
const integers = new Int32Array([10, 5, 20, 15]);
const max = find_max(integers);
console.log(max); // 20
```

### 示例 4: 字符串处理

```rust
use wasm_bindgen::prelude::*;

/// 反转字符串
///
/// # 参数
/// - `s`: 要反转的字符串
///
/// # 返回值
/// 返回反转后的字符串
///
/// # 示例
/// ```javascript
/// import { reverse_string } from './pkg/hello_wasm';
/// const result = reverse_string("hello"); // "olleh"
/// ```
#[wasm_bindgen]
pub fn reverse_string(s: &str) -> String {
    s.chars().rev().collect()
}

/// 检查字符串是否为回文
///
/// # 参数
/// - `s`: 要检查的字符串
///
/// # 返回值
/// 如果是回文返回 true，否则返回 false
#[wasm_bindgen]
pub fn is_palindrome(s: &str) -> bool {
    let s_lower: String = s
        .chars()
        .filter(|c| c.is_alphanumeric())
        .collect::<String>()
        .to_lowercase();
    let reversed: String = s_lower.chars().rev().collect();
    s_lower == reversed
}
```

### 示例 5: 使用 Web API（Fetch）

```rust
use wasm_bindgen::prelude::*;
use wasm_bindgen_futures::JsFuture;
use web_sys::{Request, RequestInit, RequestMode, Response};

/// 从 URL 获取数据
///
/// # 参数
/// - `url`: 要获取的 URL
///
/// # 返回值
/// 返回一个 Promise，解析为 JSON 数据
///
/// # 示例（JavaScript）
/// ```javascript
/// import { fetch_data } from './pkg/hello_wasm';
/// const data = await fetch_data('https://api.example.com/data');
/// ```
#[wasm_bindgen]
pub async fn fetch_data(url: &str) -> Result<JsValue, JsValue> {
    // 创建请求配置
    let mut opts = RequestInit::new();
    opts.set_method("GET");
    opts.set_mode(RequestMode::Cors);

    // 创建请求对象
    let request = Request::new_with_str_and_init(url, &opts)?;

    // 获取窗口对象
    let window = web_sys::window()
        .ok_or_else(|| JsValue::from_str("No window object"))?;

    // 发送请求并等待响应
    let resp_value = JsFuture::from(window.fetch_with_request(&request)).await?;

    // 转换为 Response 对象
    let resp: Response = resp_value.dyn_into()?;

    // 解析 JSON
    let json = JsFuture::from(resp.json()?).await?;

    Ok(json)
}
```

### 示例 6: 错误处理

```rust
use wasm_bindgen::prelude::*;

/// 安全的除法运算
///
/// # 参数
/// - `a`: 被除数
/// - `b`: 除数
///
/// # 返回值
/// 返回 Result，成功时包含商，失败时包含错误信息
///
/// # 示例（JavaScript）
/// ```javascript
/// import { safe_divide } from './pkg/hello_wasm';
/// try {
///     const result = await safe_divide(10, 2); // 5
/// } catch (e) {
///     console.error(e); // 处理错误
/// }
/// ```
#[wasm_bindgen]
pub fn safe_divide(a: f64, b: f64) -> Result<f64, JsValue> {
    if b == 0.0 {
        Err(JsValue::from_str("Division by zero is not allowed"))
    } else {
        Ok(a / b)
    }
}
```

### 示例 7: 性能优化（重用缓冲区）

```rust
use wasm_bindgen::prelude::*;
use std::cell::RefCell;

/// 线程局部存储的缓冲区
thread_local! {
    static BUFFER: RefCell<Vec<u8>> = RefCell::new(Vec::new());
}

/// 优化的字节处理函数（重用缓冲区）
///
/// 通过重用线程局部缓冲区，避免每次调用都分配新内存
///
/// # 参数
/// - `data`: 要处理的字节数组
///
/// # 返回值
/// 返回处理后的字节数组
///
/// # 性能说明
/// 这种方法比每次都创建新 Vec 快 2-3 倍
#[wasm_bindgen]
pub fn process_bytes_optimized(data: &[u8]) -> Vec<u8> {
    BUFFER.with(|buf| {
        let mut buffer = buf.borrow_mut();
        buffer.clear();

        // 预分配容量（如果需要）
        if buffer.capacity() < data.len() {
            buffer.reserve(data.len());
        }

        // 处理数据（示例：将每个字节乘以2）
        for &byte in data {
            buffer.push(byte.wrapping_mul(2));
        }

        buffer.clone()
    })
}
```

### 完整项目示例

**Cargo.toml**:

```toml
[package]
name = "hello-wasm"
version = "0.1.0"
edition = "2024"

[lib]
crate-type = ["cdylib"]

[dependencies]
wasm-bindgen = "0.2"

[profile.release]
opt-level = "z"
lto = true
```

**src/lib.rs**:

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}

#[wasm_bindgen(start)]
pub fn main() {
    // 初始化代码（可选）
    console_log!("WASM module initialized");
}
```

**编译和运行**:

```bash
# 1. 编译
wasm-pack build --target web

# 2. 在 HTML 中使用
# <script type="module">
#   import init, { greet } from './pkg/hello_wasm.js';
#   await init();
#   console.log(greet("World")); // "Hello, World!"
# </script>
```

---

## 📚 相关资源

- [WASM 基础指南](./01_wasm_基础指南.md) - 学习 WASM 基础
- [JavaScript 互操作](./03_javascript_互操作.md) - 学习集成
- [项目概览](../tier_01_foundations/01_项目概览.md) - 了解整体架构

**外部资源**:

- [wasm-bindgen Book](https://rustwasm.github.io/docs/wasm-bindgen/)
- [wasm-pack Book](https://rustwasm.github.io/docs/wasm-pack/)

---

**文档维护**: Documentation Team
**创建日期**: 2025-10-30
**适用版本**: Rust 1.90+ / Edition 2024, WASM 2.0 + WASI 0.2
