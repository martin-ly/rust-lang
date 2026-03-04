# WebAssembly (WASM) 开发指南

> Rust是构建WebAssembly应用的首选语言

---

## 目录

- [WebAssembly (WASM) 开发指南](#webassembly-wasm-开发指南)
  - [目录](#目录)
  - [1. WebAssembly概述](#1-webassembly概述)
    - [1.1 什么是WebAssembly](#11-什么是webassembly)
    - [1.2 WASM内存模型](#12-wasm内存模型)
    - [1.3 Rust为什么适合WASM](#13-rust为什么适合wasm)
  - [2. Rust与WASM](#2-rust与wasm)
    - [2.1 wasm-bindgen](#21-wasm-bindgen)
    - [2.2 wasm-pack](#22-wasm-pack)
    - [2.3 项目结构](#23-项目结构)
  - [3. 开发环境搭建](#3-开发环境搭建)
    - [3.1 创建项目](#31-创建项目)
    - [3.2 Cargo.toml配置](#32-cargotoml配置)
    - [3.3 基本模板代码](#33-基本模板代码)
  - [4. 与JavaScript互操作](#4-与javascript互操作)
    - [4.1 类型映射](#41-类型映射)
    - [4.2 复杂类型传递](#42-复杂类型传递)
    - [4.3 回调函数](#43-回调函数)
  - [5. 内存管理](#5-内存管理)
    - [5.1 WASM线性内存](#51-wasm线性内存)
    - [5.2 所有权与WASM内存](#52-所有权与wasm内存)
    - [5.3 内存泄漏预防](#53-内存泄漏预防)
  - [6. 性能优化](#6-性能优化)
    - [6.1 编译优化](#61-编译优化)
    - [6.2 减少WASM体积](#62-减少wasm体积)
    - [6.3 避免边界检查](#63-避免边界检查)
    - [6.4 批量数据处理](#64-批量数据处理)
  - [7. 实际案例](#7-实际案例)
    - [7.1 图像处理](#71-图像处理)
    - [7.2 加密运算](#72-加密运算)
    - [7.3 物理模拟](#73-物理模拟)
  - [8. 调试与测试](#8-调试与测试)
    - [8.1 浏览器调试](#81-浏览器调试)
    - [8.2 单元测试](#82-单元测试)
    - [8.3 性能分析](#83-性能分析)
  - [9. 部署策略](#9-部署策略)
    - [9.1 作为npm包发布](#91-作为npm包发布)
    - [9.2 在Web应用中使用](#92-在web应用中使用)
    - [9.3 与现有框架集成](#93-与现有框架集成)
  - [总结](#总结)

---

## 1. WebAssembly概述

### 1.1 什么是WebAssembly

WebAssembly (WASM) 是一种**低级别字节码格式**，设计用于在现代Web浏览器中以接近原生的性能运行。

**核心特性**:

- 高性能: 接近原生代码的执行速度
- 安全: 沙箱化执行环境
- 开放: 跨平台、跨语言
- 紧凑: 二进制格式，体积小

### 1.2 WASM内存模型

```
┌─────────────────────────────────────────────────────┐
│                  JavaScript 环境                     │
│  ┌─────────────────────────────────────────────┐   │
│  │           WebAssembly 实例                   │   │
│  │  ┌─────────────────────────────────────┐   │   │
│  │  │          Linear Memory               │   │   │
│  │  │  ┌─────┬─────┬─────┬─────┬─────┐   │   │   │
│  │  │  │Stack│Heap │Data │     │     │   │   │   │
│  │  │  └─────┴─────┴─────┴─────┴─────┘   │   │   │
│  │  │          (ArrayBuffer)              │   │   │
│  │  └─────────────────────────────────────┘   │   │
│  │                                             │   │
│  │  ┌─────────────────────────────────────┐   │   │
│  │  │          Function Table              │   │   │
│  │  │  ┌─────┬─────┬─────┬─────┬─────┐   │   │   │
│  │  │  │func0│func1│func2│ ... │funcN│   │   │   │
│  │  │  └─────┴─────┴─────┴─────┴─────┘   │   │   │
│  │  └─────────────────────────────────────┘   │   │
│  └─────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────┘
```

### 1.3 Rust为什么适合WASM

| 特性 | Rust优势 | 对WASM的意义 |
|------|----------|--------------|
| 无GC | 无运行时 | WASM体积小 |
| 零成本抽象 | 高性能 | 接近原生速度 |
| 内存安全 | 无UB | 沙箱更安全 |
| FFI友好 | 易与JS交互 | 无缝集成 |

---

## 2. Rust与WASM

### 2.1 wasm-bindgen

`wasm-bindgen` 是Rust与JavaScript之间的桥梁。

**工作原理**:

```rust
use wasm_bindgen::prelude::*;

// 导出一个函数到JavaScript
#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

// 导入JavaScript函数
#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}

// 使用
pub fn greet(name: &str) {
    log(&format!("Hello, {}!", name));
}
```

### 2.2 wasm-pack

`wasm-pack` 是构建、测试和发布WASM的CLI工具。

```bash
# 安装
cargo install wasm-pack

# 构建
wasm-pack build --target web

# 运行测试
wasm-pack test --headless --firefox

# 发布到npm
wasm-pack publish
```

### 2.3 项目结构

```
my-wasm-project/
├── Cargo.toml
├── src/
│   └── lib.rs
├── pkg/              # 生成的WASM包
│   ├── my_wasm_project.js
│   ├── my_wasm_project_bg.wasm
│   └── package.json
└── www/              # 前端代码
    ├── index.html
    └── index.js
```

---

## 3. 开发环境搭建

### 3.1 创建项目

```bash
# 使用cargo generate
cargo generate --git https://github.com/rustwasm/wasm-pack-template

# 或手动创建
cargo new --lib my-wasm-project
cd my-wasm-project
```

### 3.2 Cargo.toml配置

```toml
[package]
name = "my-wasm-project"
version = "0.1.0"
edition = "2021"
authors = ["Your Name <you@example.com>"]
license = "MIT/Apache-2.0"

[lib]
crate-type = ["cdylib"]

[dependencies]
wasm-bindgen = "0.2.87"
js-sys = "0.3.64"
web-sys = "0.3.64"

# 可选：WASM友好的库
serde = { version = "1.0", features = ["derive"] }
wasm-bindgen-futures = "0.4.37"

[dependencies.web-sys]
version = "0.3.64"
features = [
    "console",
    "Document",
    "Element",
    "HtmlElement",
    "Window",
    "CanvasRenderingContext2d",
]

[profile.release]
opt-level = 3
lto = true
```

### 3.3 基本模板代码

```rust
use wasm_bindgen::prelude::*;

// 当WASM模块加载时调用
#[wasm_bindgen(start)]
pub fn main() {
    console_error_panic_hook::set_once();
    wasm_logger::init(wasm_logger::Config::default());
}

#[wasm_bindgen]
pub struct Calculator {
    value: f64,
}

#[wasm_bindgen]
impl Calculator {
    #[wasm_bindgen(constructor)]
    pub fn new(initial: f64) -> Calculator {
        Calculator { value: initial }
    }

    pub fn add(&mut self, n: f64) {
        self.value += n;
    }

    pub fn get_value(&self) -> f64 {
        self.value
    }
}
```

---

## 4. 与JavaScript互操作

### 4.1 类型映射

| Rust类型 | JavaScript类型 | 说明 |
|----------|----------------|------|
| `i32`, `i64` | `number`, `bigint` | 整数 |
| `f32`, `f64` | `number` | 浮点数 |
| `bool` | `boolean` | 布尔 |
| `String` | `string` | 字符串（拷贝） |
| `&str` | `string` | 字符串（借用） |
| `Vec<T>` | `Array` | 数组 |
| `JsValue` | 任意 | 通用JS值 |

### 4.2 复杂类型传递

**使用Serde进行序列化**:

```rust
use serde::{Serialize, Deserialize};
use wasm_bindgen::prelude::*;

#[derive(Serialize, Deserialize)]
pub struct User {
    name: String,
    age: u32,
    email: String,
}

#[wasm_bindgen]
pub fn process_user(data: &str) -> Result<JsValue, JsValue> {
    let user: User = serde_json::from_str(data)
        .map_err(|e| e.to_string())?;

    // 处理...

    Ok(serde_wasm_bindgen::to_value(&user)?)
}
```

### 4.3 回调函数

```rust
use wasm_bindgen::prelude::*;
use js_sys::Function;

#[wasm_bindgen]
pub fn with_callback(callback: &Function) {
    let this = JsValue::NULL;
    let args = JsValue::from_str("Hello from Rust!");

    callback.call1(&this, &args).unwrap();
}

// 使用Promise
use wasm_bindgen_futures::JsFuture;
use web_sys::Response;

#[wasm_bindgen]
pub async fn fetch_data(url: String) -> Result<JsValue, JsValue> {
    let window = web_sys::window().unwrap();
    let resp_value = JsFuture::from(window.fetch_with_str(&url)).await?;
    let resp: Response = resp_value.dyn_into()?;

    let json = JsFuture::from(resp.json()?).await?;
    Ok(json)
}
```

---

## 5. 内存管理

### 5.1 WASM线性内存

```text
┌────────────────────────────────────────┐
│              Linear Memory             │
│  (大小: 初始16MB, 最大2GB或4GB)         │
├────────────────────────────────────────┤
│  0x0000                                │
│     ┌──────────────┐                   │
│     │    Stack     │ 向下增长           │
│     │              │                   │
│     ├──────────────┤                   │
│     │     ...      │                   │
│     │              │                   │
│     ├──────────────┤                   │
│     │    Heap      │ 向上增长           │
│     │              │                   │
│     └──────────────┘                   │
│                                0xFFFF  │
└────────────────────────────────────────┘
```

### 5.2 所有权与WASM内存

```rust
use wasm_bindgen::prelude::*;

// 值在WASM堆上分配
#[wasm_bindgen]
pub fn create_buffer(size: usize) -> Vec<u8> {
    vec![0u8; size]
}

// 值传递：所有权转移
#[wasm_bindgen]
pub fn process_buffer(mut data: Vec<u8>) -> Vec<u8> {
    for byte in &mut data {
        *byte = byte.wrapping_add(1);
    }
    data  // 所有权返回给JS
}

// 借用：避免拷贝
#[wasm_bindgen]
pub fn sum_buffer(data: &[u8]) -> u32 {
    data.iter().map(|&b| b as u32).sum()
}
```

### 5.3 内存泄漏预防

```rust
use wasm_bindgen::prelude::*;

// 使用Box管理生命周期
#[wasm_bindgen]
pub struct Resource {
    data: Vec<u8>,
}

#[wasm_bindgen]
impl Resource {
    #[wasm_bindgen(constructor)]
    pub fn new(size: usize) -> Resource {
        Resource { data: vec![0; size] }
    }

    // 显式释放（Drop会自动调用）
}

// 确保Drop被调用
impl Drop for Resource {
    fn drop(&mut self) {
        log::info!("Resource freed: {} bytes", self.data.len());
    }
}
```

---

## 6. 性能优化

### 6.1 编译优化

```toml
[profile.release]
opt-level = 3           # 最高优化
lto = true              # 链接时优化
panic = "abort"         # 移除panic处理代码
codegen-units = 1       # 单代码生成单元

# 或使用wee_alloc减少体积
[dependencies]
wee_alloc = "0.4.5"

# 入口设置
#[global_allocator]
#static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;
```

### 6.2 减少WASM体积

```bash
# 使用wasm-opt优化
wasm-opt -Oz -o output.wasm input.wasm

# 使用twiggy分析
wasm-pack build && twiggy pkg/*.wasm

# 使用wasm-snip移除panic
wasm-snip pkg/*.wasm -o snipped.wasm
```

### 6.3 避免边界检查

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn sum_array(data: &[f64]) -> f64 {
    // Rust会自动添加边界检查
    // 使用迭代器避免检查
    data.iter().sum()

    // 或使用unsafe（谨慎使用）
    // unsafe {
    //     data.get_unchecked(0)
    // }
}
```

### 6.4 批量数据处理

```rust
use wasm_bindgen::prelude::*;
use js_sys::Float64Array;

#[wasm_bindgen]
pub fn process_array(input: &Float64Array) -> Float64Array {
    let len = input.length() as usize;
    let mut result = vec![0.0; len];

    // 批量拷贝到Rust内存
    input.copy_to(&mut result);

    // 处理...
    for (i, val) in result.iter_mut().enumerate() {
        *val = val.sqrt() + i as f64;
    }

    // 返回
    Float64Array::from(&result[..])
}
```

---

## 7. 实际案例

### 7.1 图像处理

```rust
use wasm_bindgen::prelude::*;
use web_sys::{CanvasRenderingContext2d, ImageData};

#[wasm_bindgen]
pub struct ImageProcessor {
    width: u32,
    height: u32,
    data: Vec<u8>,
}

#[wasm_bindgen]
impl ImageProcessor {
    pub fn from_image_data(image_data: &ImageData) -> ImageProcessor {
        let width = image_data.width();
        let height = image_data.height();
        let data = image_data.data().to_vec();

        ImageProcessor { width, height, data }
    }

    pub fn grayscale(&mut self) {
        for chunk in self.data.chunks_exact_mut(4) {
            let r = chunk[0] as f32;
            let g = chunk[1] as f32;
            let b = chunk[2] as f32;

            let gray = (0.299 * r + 0.587 * g + 0.114 * b) as u8;

            chunk[0] = gray;
            chunk[1] = gray;
            chunk[2] = gray;
            // chunk[3] 是alpha，保持不变
        }
    }

    pub fn to_image_data(&self) -> ImageData {
        ImageData::new_with_u8_clamped_array_and_sh(
            wasm_bindgen::Clamped(&self.data),
            self.width,
            self.height,
        ).unwrap()
    }
}
```

### 7.2 加密运算

```rust
use wasm_bindgen::prelude::*;
use sha2::{Sha256, Digest};

#[wasm_bindgen]
pub fn sha256_hash(input: &[u8]) -> Vec<u8> {
    let mut hasher = Sha256::new();
    hasher.update(input);
    hasher.finalize().to_vec()
}

// 与原生JS实现对比：
// JS SHA-256: ~5MB/s
// Rust WASM:  ~50MB/s
```

### 7.3 物理模拟

```rust
use wasm_bindgen::prelude::*;
use nalgebra::{Vector2, Vector3};

#[wasm_bindgen]
pub struct ParticleSystem {
    positions: Vec<Vector2<f32>>,
    velocities: Vec<Vector2<f32>>,
    masses: Vec<f32>,
}

#[wasm_bindgen]
impl ParticleSystem {
    pub fn new(count: usize) -> ParticleSystem {
        ParticleSystem {
            positions: vec![Vector2::zeros(); count],
            velocities: vec![Vector2::zeros(); count],
            masses: vec![1.0; count],
        }
    }

    pub fn update(&mut self, dt: f32) {
        for i in 0..self.positions.len() {
            // 简单的欧拉积分
            self.positions[i] += self.velocities[i] * dt;

            // 重力
            self.velocities[i].y += 9.8 * dt;
        }
    }
}
```

---

## 8. 调试与测试

### 8.1 浏览器调试

```bash
# 启用source map
wasm-pack build --dev

# 使用wasm-bindgen-rayon进行多线程调试
```

### 8.2 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use wasm_bindgen_test::*;

    wasm_bindgen_test_configure!(run_in_browser);

    #[wasm_bindgen_test]
    fn test_add() {
        assert_eq!(add(1, 2), 3);
    }
}
```

### 8.3 性能分析

```rust
use web_sys::console;

#[wasm_bindgen]
pub fn profiled_function() {
    console::time_with_label("operation");

    // 执行操作...

    console::time_end_with_label("operation");
}
```

---

## 9. 部署策略

### 9.1 作为npm包发布

```bash
wasm-pack build --scope my-org
wasm-pack publish
```

### 9.2 在Web应用中使用

```html
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>Rust WASM App</title>
</head>
<body>
    <script type="module">
        import init, { greet } from './pkg/my_wasm_project.js';

        async function run() {
            await init();
            greet('WebAssembly');
        }

        run();
    </script>
</body>
</html>
```

### 9.3 与现有框架集成

**React**:

```javascript
import React, { useEffect, useState } from 'react';
import init, { Calculator } from '../pkg';

function App() {
    const [calc, setCalc] = useState(null);

    useEffect(() => {
        init().then(() => {
            setCalc(new Calculator(0));
        });
    }, []);

    const handleAdd = () => {
        if (calc) {
            calc.add(5);
            console.log(calc.get_value());
        }
    };

    return <button onClick={handleAdd}>Add 5</button>;
}
```

---

## 总结

WebAssembly + Rust 提供了：

1. **高性能**: 接近原生速度
2. **小体积**: 无GC运行时
3. **安全性**: 内存安全和沙箱
4. **互操作性**: 与JS无缝集成

适用场景：图像处理、加密、游戏、科学计算等计算密集型任务。
