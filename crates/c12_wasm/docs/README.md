# C12 WebAssembly - 文档中心

> **创建日期**: 2025-10-30
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.94.0+ (Edition 2024)
> **WASM 版本**: WASM 2.0 + WASI 0.2
> **状态**: ✅ 100% 完成
> **概念说明**: WebAssembly 是一种可移植、高性能的二进制指令格式，本文档提供 Rust 编译到 WASM 的完整指南，涵盖 wasm-bindgen、WASI、性能优化和实战应用。

---

## 快速示例

```rust
// 基础 WASM 函数
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

// 字符串操作
#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}

// 复杂类型
#[wasm_bindgen]
#[derive(Clone)]
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

---

## 文档结构导航

### 核心文档

| 文档 | 描述 | 难度 |
| :--- | :--- | :--- |
| [ONE_PAGE_SUMMARY.md](./ONE_PAGE_SUMMARY.md) | 一页纸总结 | ⭐⭐ |
| [代码示例索引.md](./代码示例索引.md) | 完整示例索引 | ⭐⭐ |
| [WASM_MIND_MAPS.md](./WASM_MIND_MAPS.md) | 思维导图集合 | ⭐⭐ |
| [WASM_CONCEPT_MATRIX.md](./WASM_CONCEPT_MATRIX.md) | 概念对比矩阵 | ⭐⭐⭐ |
| [WASM_DECISION_TREE.md](./WASM_DECISION_TREE.md) | 决策树图 | ⭐⭐⭐ |
| [WASM_PROOF_TREE.md](./WASM_PROOF_TREE.md) | 证明树图 | ⭐⭐⭐⭐ |

### Rust 版本特性文档

| 文档 | 描述 | 难度 |
| :--- | :--- | :--- |
| [RUST_193_WASM_IMPROVEMENTS.md](./RUST_193_WASM_IMPROVEMENTS.md) | Rust 1.93.0 WASM 改进 | ⭐⭐⭐ |
| [RUST_192_WASM_IMPROVEMENTS.md](./RUST_192_WASM_IMPROVEMENTS.md) | Rust 1.92.0 WASM 改进 | ⭐⭐⭐ |
| [RUST_192_COMPLETE_GUIDE.md](./RUST_192_COMPLETE_GUIDE.md) | 完整指南 | ⭐⭐⭐ |
| [RUST_192_QUICK_REFERENCE.md](./RUST_192_QUICK_REFERENCE.md) | 快速参考 | ⭐⭐ |
| [RUST_192_MIGRATION_GUIDE.md](./RUST_192_MIGRATION_GUIDE.md) | 迁移指南 | ⭐⭐⭐ |
| [RUST_192_BEST_PRACTICES.md](./RUST_192_BEST_PRACTICES.md) | 最佳实践 | ⭐⭐⭐ |
| [RUST_192_PERFORMANCE_BENCHMARKS.md](./RUST_192_PERFORMANCE_BENCHMARKS.md) | 性能基准 | ⭐⭐⭐ |
| [RUST_192_TROUBLESHOOTING.md](./RUST_192_TROUBLESHOOTING.md) | 故障排除 | ⭐⭐ |
| [RUST_192_FEATURE_ROADMAP.md](./RUST_192_FEATURE_ROADMAP.md) | 特性路线图 | ⭐⭐⭐ |
| [RUST_192_FEATURE_COMPARISON.md](./RUST_192_FEATURE_COMPARISON.md) | 特性对比 | ⭐⭐⭐ |
| [RUST_192_CODE_EXAMPLES_COLLECTION.md](./RUST_192_CODE_EXAMPLES_COLLECTION.md) | 代码示例集 | ⭐⭐⭐ |
| [RUST_192_INDEX.md](./RUST_192_INDEX.md) | 完整索引 | ⭐ |
| [RUST_191_WASM_IMPROVEMENTS.md](./RUST_191_WASM_IMPROVEMENTS.md) | Rust 1.91 WASM 改进 | ⭐⭐⭐ |

---

## 核心概念概览

### 1. WASM 基础

```rust
// WASM 内存模型
// - 线性内存: 连续的内存块
// - 栈: 用于函数调用
// - 堆: 通过 Rust 分配器管理

#[wasm_bindgen]
pub fn process_data(data: &[u8]) -> Vec<u8> {
    // 数据处理...
    data.iter().map(|b| b * 2).collect()
}
```

### 2. wasm-bindgen 集成

```rust
use wasm_bindgen::prelude::*;
use web_sys::console;

#[wasm_bindgen(start)]
pub fn main() {
    console::log_1(&"WASM module loaded!".into());
}

// 导入 JavaScript 函数
#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}

// 导出 Rust 函数
#[wasm_bindgen]
pub fn calculate(x: f64) -> f64 {
    x.sin() * x.cos()
}
```

### 3. WASI 开发

```rust
// WASI: WebAssembly System Interface
// 允许 WASM 模块访问系统功能

use std::fs::File;
use std::io::{Read, Write};

pub fn read_file(path: &str) -> Result<String, std::io::Error> {
    let mut file = File::open(path)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    Ok(contents)
}

pub fn write_file(path: &str, data: &str) -> Result<(), std::io::Error> {
    let mut file = File::create(path)?;
    file.write_all(data.as_bytes())?;
    Ok(())
}
```

### 4. 性能优化

```toml
# Cargo.toml 优化配置
[profile.release]
opt-level = 3        # 优化级别
lto = true           # 链接时优化
strip = true         # 去除符号
panic = "abort"      #  panic 处理
```

```rust
// 使用 wee_alloc 减少二进制大小
#[cfg(target_arch = "wasm32")]
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

// 避免不必要的克隆
#[wasm_bindgen]
pub fn process_large_data(data: &[u8]) -> Result<(), JsValue> {
    // 直接操作切片，避免分配
    let sum: u32 = data.iter().map(|&b| b as u32).sum();
    Ok(())
}
```

---

## 学习路径指引

### 路径 A: 快速入门 (1-2周)

**第1周: 环境搭建与基础**:

```bash
# 1. 安装 WASM 目标
rustup target add wasm32-unknown-unknown

# 2. 安装 wasm-pack
curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh

# 3. 创建新项目
wasm-pack new hello-wasm
cd hello-wasm
wasm-pack build
```

- 学习 WASM 核心概念
- 理解线性内存模型
- 掌握基本数据类型映射

**第2周: wasm-bindgen 实践**:

- 学习 Rust/JS 类型转换
- 掌握字符串和数组处理
- 理解内存管理

### 路径 B: 中级进阶 (3-4周)

**第3周: WASI 与系统编程**:

- 学习 WASI 接口
- 掌握文件系统操作
- 理解环境变量和命令行参数

**第4周: 前端集成**:

- 学习 Webpack/Vite 集成
- 掌握 React/Vue 中使用 WASM
- 理解异步加载

### 路径 C: 高级应用 (5-8周)

**第5-6周: 性能优化**:

- 二进制大小优化技术
- 运行时性能调优
- SIMD 和并行计算

**第7-8周: 实战项目**:

- 图像处理库
- 科学计算模块
- 游戏引擎组件

---

## 文档层级结构

### Tier 1: 基础层 (2-4小时)

- [项目概览](./tier_01_foundations/01_项目概览.md) - WASM 与 Rust 概览
- [主索引导航](./tier_01_foundations/02_主索引导航.md) - 完整文档导航
- [术语表](./tier_01_foundations/03_术语表.md) - WASM 核心术语
- [常见问题](./tier_01_foundations/04_常见问题.md) - FAQ 解答

### Tier 2: 实践层 (10-20小时)

- [WASM 基础指南](./tier_02_guides/01_wasm_基础指南.md) - 入门与实践
- [Rust 编译 WASM](./tier_02_guides/02_rust_编译_wasm.md) - 编译流程
- [JavaScript 互操作](./tier_02_guides/03_javascript_互操作.md) - wasm-bindgen
- [性能优化指南](./tier_02_guides/04_性能优化指南.md) - 大小与性能优化

### Tier 3: 参考层 (按需查阅)

- [API 参考](./tier_03_references/01_api_参考.md) - wasm-bindgen API
- [工具链参考](./tier_03_references/02_工具链参考.md) - 工具使用手册
- [最佳实践](./tier_03_references/03_最佳实践.md) - 开发规范

### Tier 4: 高级层 (20-30小时)

- [WASI 深入](./tier_04_advanced/01_wasi_深入.md) - WASI 系统接口
- [性能分析与优化](./tier_04_advanced/02_性能分析与优化.md) - 高级优化
- [生产级部署](./tier_04_advanced/03_生产级部署.md) - 部署与监控
- [容器技术深度集成](./tier_04_advanced/06_容器技术深度集成.md) - Docker/K8s
- [云原生 CI/CD 实践](./tier_04_advanced/07_云原生CI_CD实践.md) - GitHub Actions
- [监控与可观测性实践](./tier_04_advanced/08_监控与可观测性实践.md) - Prometheus

---

## 思维表征工具

### 可视化资源

- **[WASM 思维导图](./WASM_MIND_MAPS.md)** - 8 个核心思维导图
- **[多维概念对比矩阵](./WASM_CONCEPT_MATRIX.md)** - 10+ 对比矩阵
- **[决策树图](./WASM_DECISION_TREE.md)** - 5 个决策树
- **[证明树图](./WASM_PROOF_TREE.md)** - 5 个证明路径

### 外部知识结构

- **[知识结构框架](../../docs/KNOWLEDGE_STRUCTURE_FRAMEWORK.md)** - 完整知识体系
- **[多维概念矩阵](../../docs/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md)** - WASM 对比矩阵
- **[思维导图集合](../../docs/MIND_MAP_COLLECTION.md)** - 可视化知识结构

---

## 形式化理论

深入学习 WASM 的形式化理论基础：

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| WASM 形式化规范 | 官方规范 | [WebAssembly Spec](https://webassembly.github.io/spec/) |
| 类型系统理论 | 类型安全 | [../../docs/rust-formal-engineering-system/01_theoretical_foundations/01_type_system/README.md](../../docs/rust-formal-engineering-system/01_theoretical_foundations/01_type_system/README.md) |
| 内存安全语义 | 线性内存 | [../../docs/rust-formal-engineering-system/01_theoretical_foundations/02_memory_safety/README.md](../../docs/rust-formal-engineering-system/01_theoretical_foundations/02_memory_safety/README.md) |

---

## 相关资源

### 代码示例

```bash
# 运行示例
cargo run --example 01_basic_add
cargo run --example 02_string_operations
cargo run --example 03_array_processing
cargo run --example 04_counter_class
cargo run --example 05_wasi_file_processor
cargo run --example 06_async_fetch
cargo run --example 07_design_patterns
cargo run --example 08_container_microservice
```

### 工具链

| 工具 | 用途 | 链接 |
| :--- | :--- | :--- |
| wasm-pack | 构建和发布 | [wasm-pack](https://rustwasm.github.io/wasm-pack/) |
| wasm-bindgen | JS 互操作 | [wasm-bindgen](https://rustwasm.github.io/wasm-bindgen/) |
| wasmtime | WASM 运行时 | [wasmtime](https://wasmtime.dev/) |
| wasmer | WASM 运行时 | [wasmer](https://wasmer.io/) |
| wasm-opt | 优化工具 | [binaryen](https://github.com/WebAssembly/binaryen) |

### 外部资源

- [WebAssembly 官方文档](https://webassembly.org/)
- [Rust and WebAssembly 书籍](https://rustwasm.github.io/book/)
- [MDN WebAssembly 指南](https://developer.mozilla.org/en-US/docs/WebAssembly)

---

## 快速开始

```bash
# 1. 安装依赖
rustup target add wasm32-unknown-unknown
wasm-pack --version  # 确保已安装

# 2. 运行示例
cd crates/c12_wasm
cargo build --target wasm32-wasi --release
wasmedge target/wasm32-wasi/release/wasi-app.wasm input.txt

# 3. 运行测试
cargo test -p c12_wasm
```

---

[返回模块主页](../README.md) | [返回文档中心](../../docs/README.md)
