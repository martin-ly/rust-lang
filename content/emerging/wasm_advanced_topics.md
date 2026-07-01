# WebAssembly 高级主题

> **定位**: Rust WASM 前沿技术深度解析
> **覆盖**: WASI Preview 2、组件模型、WASM GC、WASM 线程
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: 🔄 持续跟踪

---

## 📋 目录

- [WebAssembly 高级主题](#webassembly-高级主题)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [🏗️ WASI Preview 2 与组件模型](#️-wasi-preview-2-与组件模型)
    - [核心概念](#核心概念)
    - [WIT 接口定义](#wit-接口定义)
    - [wit-bindgen 绑定生成](#wit-bindgen-绑定生成)
  - [🧬 WASM GC](#-wasm-gc)
    - [语言互操作](#语言互操作)
    - [Rust 注意事项](#rust-注意事项)
  - [🧵 WASM 线程](#-wasm-线程)
    - [共享线性内存](#共享线性内存)
    - [Rust 中的 WASM 线程](#rust-中的-wasm-线程)
  - [⚡ 性能优化技巧](#-性能优化技巧)
    - [编译优化](#编译优化)
    - [运行时优化](#运行时优化)
  - [🔧 Rust → WASM 构建工具链](#-rust--wasm-构建工具链)
    - [wasm-pack](#wasm-pack)
    - [wasm-bindgen](#wasm-bindgen)
    - [wasm-tools](#wasm-tools)
    - [工具链对比](#工具链对比)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 概述

WebAssembly (WASM) 已从浏览器的"快速 JavaScript 替代"演进为通用字节码格式。
Rust 是 WASM 生态中最成熟的生产语言之一，本指南深入解析四大前沿方向：

```text
WASM 技术演进路线:
WASM 1.0 (2017)
    │
    ├── WASM MVP ──→ 浏览器计算密集型任务
    │
    ├── WASI Preview 1 ──→ 模块级系统调用
    │
    ├── WASM SIMD ──→ 向量运算加速
    │
    └── WASM Threads ──→ 共享内存并发
            │
            └── WASI Preview 2 / 组件模型 (当前重点)
                    │
                    ├── WIT 接口定义
                    ├── 组件组合
                    └── 跨语言互操作
```
> 项目内相关代码请见 [`crates/c12_wasm/src/component_model.rs`](../../crates/c12_wasm/src/component_model.rs)
> 和 [`content/ecosystem/web_frameworks/`](../ecosystem/web_frameworks)。

---

## 🏗️ WASI Preview 2 与组件模型

WASI Preview 2 引入了**组件模型 (Component Model)**，将 WASM 从低级模块提升到类型安全的组件抽象。

### 核心概念

| 概念 | 说明 | 类比 |
|------|------|------|
| **World** | 组件的完整接口签名 | Rust 中的 `trait` 集合 |
| **Interface** | 命名空间化的函数和类型 | 模块的公共 API |
| **Component** | 实现了 World 的 WASM 二进制 | 编译后的 crate |
| **WIT** | 接口定义语言 | 跨语言的 `.h` / `.proto` |

```rust
// 使用 cargo-component 构建
// 目标: wasm32-wasip2

// 生成的绑定通过 wit-bindgen 宏实现
wit_bindgen::generate!({
    world: "calculator",
    path: "wit",
});

struct Calculator;

impl Guest for Calculator {
    fn eval(a: f64, b: f64, op: Op) -> Result<f64, String> {
        match op {
            Op::Add => Ok(a + b),
            Op::Sub => Ok(a - b),
            Op::Mul => Ok(a * b),
            Op::Div => {
                if b == 0.0 {
                    Err("division by zero".to_string())
                } else {
                    Ok(a / b)
                }
            }
        }
    }
}

export!(Calculator);
```
### WIT 接口定义

```wit
// wit/calculator.wit
package example:calculator@0.1.0;

interface ops {
    record point {
        x: f64,
        y: f64,
    }

    enum op {
        add,
        sub,
        mul,
        div,
    }

    eval: func(a: f64, b: f64, op: op) -> result<f64, string>;
}

world calculator {
    export ops;
}
```
### wit-bindgen 绑定生成

```bash
# 安装工具链
cargo install cargo-component
rustup target add wasm32-wasip2

# 初始化组件项目
cargo component new --reactor my-calculator

# 构建
cargo component build --target wasm32-wasip2

# 输出: target/wasm32-wasip2/debug/my-calculator.wasm
```
---

## 🧬 WASM GC

WASM GC 提案为 WebAssembly 添加了托管对象和垃圾回收支持，使得 Java、Kotlin、Dart 等 GC 语言无需携带重型运行时即可编译到 WASM。

### 语言互操作

```text
WASM GC 带来的变化:

Before (WASM MVP):
  Java/Kotlin ──→ 重型运行时 (~10MB) ──→ WASM
  Dart ──→ 重型运行时 ──→ WASM

After (WASM GC):
  Java/Kotlin ──→ 原生 WASM GC ──→ 轻量级 WASM
  Dart ──→ 原生 WASM GC ──→ 轻量级 WASM
```
### Rust 注意事项

Rust **不使用** WASM GC（因为 Rust 有所有权系统），但 Rust 编译的 WASM 模块可以与 WASM GC 模块共存：

```rust
// Rust 侧：通过引用类型与 WASM GC 对象交互
// 需要启用 reference-types 和 gc 特性

#[wasm_bindgen]
pub fn process_external_object(obj: JsValue) -> Result<JsValue, JsValue> {
    // obj 是外部 WASM GC 对象的引用
    // 在 Rust 中表现为 JsValue，不拥有所有权
    let doc: web_sys::Document = obj.dyn_into()?;
    Ok(doc.create_element("div")?.into())
}
```
| 特性 | Rust WASM | GC 语言 WASM |
|------|-----------|--------------|
| 运行时开销 | 零 (无 GC) | GC 周期开销 |
| 对象模型 | 线性内存 + 手动布局 | 结构化 GC 对象 |
| 与 JS 互操作 | wasm-bindgen | 直接映射 |
| 二进制体积 | 极小 (~KB 级) | 依赖语言 |
| 适用场景 | 计算密集型、库 | UI 框架、业务逻辑 |

---

## 🧵 WASM 线程

WASM 线程提案允许 WebAssembly 实例共享线性内存，实现真正的多线程并行。

### 共享线性内存

```rust
// 启用 wasm-bindgen-rayon 进行并行计算
use rayon::prelude::*;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn parallel_sum(data: &[i32]) -> i32 {
    data.par_iter().sum()
}
```
**必要的 HTTP 响应头**：

```text
Cross-Origin-Opener-Policy: same-origin
Cross-Origin-Embedder-Policy: require-corp
```
### Rust 中的 WASM 线程

```toml
# Cargo.toml
[dependencies]
wasm-bindgen = "0.2"
wasm-bindgen-rayon = "1.2"
rayon = "1"

[package.metadata.wasm-pack.profile.release]
wasm-opt = ["-O4", "--enable-threads"]
```
```rust
use wasm_bindgen_rayon::init_thread_pool;

#[wasm_bindgen(start)]
pub fn main() {
    // 初始化线程池（浏览器中的 Web Workers）
    init_thread_pool(4);
}

#[wasm_bindgen]
pub fn matrix_multiply(a: Vec<f64>, b: Vec<f64>, n: usize) -> Vec<f64> {
    use rayon::prelude::*;

    (0..n).into_par_iter().flat_map(|i| {
        (0..n).map(move |j| {
            (0..n).map(|k| a[i * n + k] * b[k * n + j]).sum()
        })
    }).collect()
}
```
---

## ⚡ 性能优化技巧

### 编译优化

```toml
# Cargo.toml — WASM 专用优化配置
[package.metadata.wasm-pack.profile.release]
wasm-opt = ["-O4"]          # Binaryen 最高优化

[profile.wasm-release]
inherits = "release"
opt-level = 3               # 速度优先
lto = true                  # 链接时优化
codegen-units = 1
panic = "abort"
strip = true
```
| 优化选项 | 效果 | 适用场景 |
|----------|------|----------|
| `wasm-opt -O4` | -30% 体积 + 加速 | 所有发布构建 |
| `wee_alloc` | -10% 体积 | 替代默认分配器 |
| `console_error_panic_hook` | 调试友好 | 开发环境 |
| `-C target-feature=+simd128` | 向量加速 4x | 图像/音频处理 |

### 运行时优化

```rust
// ✅ 预分配线性内存，避免运行时增长
#[wasm_bindgen]
pub struct ImageProcessor {
    buffer: Vec<u8>,
}

#[wasm_bindgen]
impl ImageProcessor {
    #[wasm_bindgen(constructor)]
    pub fn new(size: usize) -> Self {
        Self {
            buffer: Vec::with_capacity(size), // 预分配
        }
    }

    pub fn process(&mut self, input: &[u8]) -> &[u8] {
        self.buffer.clear();
        self.buffer.extend_from_slice(input);
        // 就地处理，零额外分配
        for pixel in self.buffer.chunks_exact_mut(4) {
            pixel[0] = pixel[0].saturating_add(10);
        }
        &self.buffer
    }
}
```
---

## 🔧 Rust → WASM 构建工具链

### wasm-pack

```bash
# 安装
cargo install wasm-pack

# 构建 (浏览器)
wasm-pack build --target web --release

# 构建 (Node.js)
wasm-pack build --target nodejs --release

# 构建 (Bundler / Webpack)
wasm-pack build --target bundler --release
```
### wasm-bindgen

```rust
use wasm_bindgen::prelude::*;

// 导出函数到 JS
#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}

// 导出结构体
#[wasm_bindgen]
pub struct Point {
    x: f64,
    y: f64,
}

#[wasm_bindgen]
impl Point {
    #[wasm_bindgen(constructor)]
    pub fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }

    pub fn distance(&self, other: &Point) -> f64 {
        ((self.x - other.x).powi(2) + (self.y - other.y).powi(2)).sqrt()
    }
}
```
### wasm-tools

```bash
# 安装
cargo install wasm-tools

# 验证 WASM/组件格式
wasm-tools validate module.wasm

# Core Module → Component
wasm-tools component new module.wasm \
    --adapt wasi_snapshot_preview1=reactor.wasm \
    -o component.wasm

# 静态组合组件
wasm-tools compose app.wasm -d lib.wasm -o combined.wasm

# 提取 WIT 接口
wasm-tools component wit component.wasm

# 反汇编查看
wasm-tools print module.wasm > module.wat
```
### 工具链对比

| 工具 | 定位 | 输入 | 输出 | 关键特性 |
|------|------|------|------|----------|
| **wasm-pack** | 项目构建 | Rust 项目 | npm 包 | 一站式，集成 wasm-bindgen |
| **wasm-bindgen** | 绑定生成 | Rust 属性宏 | JS/TS 胶水 | 类型安全的 JS 互操作 |
| **wasm-tools** | 底层工具 | WASM 二进制 | WASM/组件 | 验证、组合、WIT 提取 |
| **cargo-component** | 组件开发 | Rust + WIT | WASM 组件 | WASI Preview 2 原生支持 |
| **jco** | JS 组件消费 | WASM 组件 | JS + WASM | 组件模型 → JS 转译 |

```text
典型工作流:

Rust 源码
    │
    ├── wasm-pack build ──→ npm 包 ──→ 浏览器/Node.js 直接使用
    │
    ├── cargo-component build ──→ WASM 组件 ──→ wasm-tools compose
    │                                            │
    │                                            ├── wasmtime run (服务端)
    │                                            └── jco transpile → JS 消费
    │
    └── rustc --target wasm32-unknown-unknown ──→ wasm-tools validate
```
---

## 🔗 参考资源

- [WebAssembly 组件模型规范](https://component-model.bytecodealliance.org/)
- [WASI Preview 2 提案](https://github.com/WebAssembly/WASI/blob/main/preview2/)
- [wasm-bindgen 指南](https://rustwasm.github.io/wasm-bindgen/)
- [wasm-pack 文档](https://rustwasm.github.io/wasm-pack/)
- [Bytecode Alliance 工具链](https://bytecodealliance.org/)
- [项目内 component_model.rs](../../crates/c12_wasm/src/component_model.rs)
- [项目内 web_frameworks 文档](../ecosystem/web_frameworks)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
