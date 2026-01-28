# WASI 0.2 组件模型深度指南

> **文档状态**: ✅ 完成
> **更新日期**: 2025-10-30
> **对标版本**: WASI 0.2 (Preview 2)
> **难度等级**: ⭐⭐⭐⭐⭐

---

## 📋 目录

- [WASI 0.2 组件模型深度指南](#wasi-02-组件模型深度指南)
  - [📋 目录](#-目录)
  - [📐 知识结构](#-知识结构)
    - [概念定义](#概念定义)
    - [属性特征](#属性特征)
    - [关系连接](#关系连接)
    - [思维导图](#思维导图)
    - [多维概念对比矩阵](#多维概念对比矩阵)
    - [决策树图](#决策树图)
  - [概述](#概述)
    - [什么是 WASI 0.2](#什么是-wasi-02)
    - [主要改进](#主要改进)
    - [为什么要升级到 WASI 0.2](#为什么要升级到-wasi-02)
  - [WASI 0.2 核心概念](#wasi-02-核心概念)
    - [1. 组件 (Component)](#1-组件-component)
    - [2. 接口 (Interface)](#2-接口-interface)
    - [3. 资源 (Resources)](#3-资源-resources)
    - [4. WIT 类型系统](#4-wit-类型系统)
  - [组件模型 (Component Model)](#组件模型-component-model)
    - [架构概览](#架构概览)
    - [组件组合](#组件组合)
      - [1. 链式组合 (Chaining)](#1-链式组合-chaining)
      - [2. 并行组合 (Parallel)](#2-并行组合-parallel)
      - [3. 嵌套组合 (Nested)](#3-嵌套组合-nested)
    - [生命周期管理](#生命周期管理)
  - [WIT (Wasm Interface Types)](#wit-wasm-interface-types)
    - [WIT 语法完整指南](#wit-语法完整指南)
      - [1. 包和版本控制](#1-包和版本控制)
      - [2. 接口定义](#2-接口定义)
      - [3. 世界定义](#3-世界定义)
      - [4. 完整示例：HTTP 客户端](#4-完整示例http-客户端)
  - [实战示例](#实战示例)
    - [示例 1：简单的 WASI 0.2 组件](#示例-1简单的-wasi-02-组件)
      - [WIT 接口定义](#wit-接口定义)
      - [Rust 实现](#rust-实现)
    - [示例 2：资源管理](#示例-2资源管理)
      - [WIT 定义](#wit-定义)
      - [Rust 实现](#rust-实现-1)
    - [示例 3：组件组合](#示例-3组件组合)
      - [主机侧组合代码](#主机侧组合代码)
  - [迁移指南](#迁移指南)
    - [从 WASI 0.1 迁移到 0.2](#从-wasi-01-迁移到-02)
      - [1. 工具链更新](#1-工具链更新)
      - [2. 代码迁移步骤](#2-代码迁移步骤)
      - [3. API 映射表](#3-api-映射表)
  - [最佳实践](#最佳实践)
    - [1. 接口设计原则](#1-接口设计原则)
      - [✅ 好的实践](#-好的实践)
      - [❌ 避免的实践](#-避免的实践)
    - [2. 版本控制策略](#2-版本控制策略)
    - [3. 性能优化](#3-性能优化)
    - [4. 错误处理模式](#4-错误处理模式)
    - [5. 资源管理最佳实践](#5-资源管理最佳实践)
    - [6. 测试策略](#6-测试策略)
  - [工具和生态系统](#工具和生态系统)
    - [核心工具](#核心工具)
    - [常用命令](#常用命令)
  - [总结](#总结)
    - [关键要点](#关键要点)
    - [下一步行动](#下一步行动)
    - [参考资源](#参考资源)

---

## 📐 知识结构

### 概念定义

**WASI 0.2 组件模型深度指南 (WASI 0.2 Component Model Deep Guide)**:

- **定义**: Rust 1.92.0 WASI 0.2 组件模型深度指南，包括 WASI 0.2 核心概念（组件、接口、资源、WIT 类型系统）、组件模型（架构概览、组件组合、生命周期管理）、WIT（Wasm Interface Types）语法完整指南、实战示例、迁移指南、最佳实践等
- **类型**: 高级主题文档
- **范畴**: WASM、WASI、组件模型
- **版本**: Rust 1.92.0+ / Edition 2024, WASI 0.2 (Preview 2)
- **相关概念**: WASI 0.2、组件模型、WIT、组件、接口、资源

### 属性特征

**核心属性**:

- **WASI 0.2 核心概念**: 组件（Component）、接口（Interface）、资源（Resources）、WIT 类型系统
- **组件模型**: 架构概览、组件组合（链式组合、并行组合、嵌套组合）、生命周期管理
- **WIT（Wasm Interface Types）**: 语法完整指南（包和版本控制、接口定义、世界定义、完整示例）
- **实战示例**: 简单的 WASI 0.2 组件、资源管理、组件组合
- **迁移指南**: 从 WASI 0.1 迁移到 0.2（工具链更新、代码迁移步骤、API 映射表）
- **最佳实践**: 组件设计、接口设计、资源管理

**Rust 1.92.0 新特性**:

- **改进的 WASI 0.2**: 更好的 WASI 0.2 支持
- **增强的组件模型**: 更好的组件模型支持
- **优化的性能**: 更高效的组件性能

**性能特征**:

- **高性能**: 高效的组件性能
- **可组合性**: 良好的组件组合能力
- **适用场景**: 组件化应用、模块化系统、WASI 应用

### 关系连接

**组合关系**:

- WASI 0.2 组件模型深度指南 --[covers]--> WASI 0.2 完整内容
- WASI 应用 --[uses]--> WASI 0.2 组件模型深度指南

**依赖关系**:

- WASI 0.2 组件模型深度指南 --[depends-on]--> WASM 基础
- WASI 应用 --[depends-on]--> WASI 0.2 组件模型深度指南

### 思维导图

```text
WASI 0.2 组件模型深度指南
│
├── WASI 0.2 核心概念
│   ├── 组件
│   ├── 接口
│   └── 资源
├── 组件模型
│   ├── 架构概览
│   └── 组件组合
├── WIT
│   ├── 语法完整指南
│   └── 接口定义
├── 实战示例
│   ├── 简单组件
│   └── 资源管理
├── 迁移指南
│   └── WASI 0.1 → 0.2
└── 最佳实践
    └── 组件设计
```

### 多维概念对比矩阵

| WASI 0.2 技术 | 功能 | 性能 | 复杂度 | 适用场景   | Rust 1.92.0 |
| ------------- | ---- | ---- | ------ | ---------- | ----------- |
| **组件**      | 高   | 高   | 中     | 组件化应用 | ✅          |
| **接口**      | 高   | 高   | 低     | 接口定义   | ✅          |
| **资源**      | 高   | 高   | 中     | 资源管理   | ✅          |
| **WIT**       | 高   | 高   | 中     | 类型系统   | ✅          |
| **组件组合**  | 高   | 高   | 高     | 组件组合   | ✅          |

### 决策树图

```text
选择 WASI 0.2 技术
│
├── 需要什么能力？
│   ├── 组件化 → 组件
│   ├── 接口定义 → 接口
│   ├── 资源管理 → 资源
│   ├── 类型系统 → WIT
│   └── 组件组合 → 组件组合
```

---

## 概述

### 什么是 WASI 0.2

WASI 0.2 (也称为 Preview 2) 是 WebAssembly System Interface 的第二个预览版本，引入了革命性的**组件模型 (Component Model)**，实现了真正的语言无关的模块化和组合。

### 主要改进

| 特性             | WASI 0.1 (Preview 1) | WASI 0.2 (Preview 2)                  |
| ---------------- | -------------------- | ------------------------------------- |
| **接口定义**     | 函数级导入/导出      | WIT 声明式接口                        |
| **类型系统**     | 基础类型             | 丰富类型（variant、record、resource） |
| **模块组合**     | 链接时绑定           | 组件模型动态组合                      |
| **多语言互操作** | 有限                 | 完整支持                              |
| **版本管理**     | 无                   | 语义化版本控制                        |
| **资源管理**     | 手动                 | 自动生命周期管理                      |

### 为什么要升级到 WASI 0.2

```text
优势:
├─ 🎯 语言无关：任何语言编译的组件都能互操作
├─ 🔌 可组合性：像乐高一样组合不同的组件
├─ 🛡️ 类型安全：编译时类型检查
├─ 🚀 性能优化：零开销抽象
└─ 📦 标准化：统一的接口定义语言（WIT）
```

---

## WASI 0.2 核心概念

### 1. 组件 (Component)

组件是 WASI 0.2 的基本单元，它是一个自包含的、可组合的 Wasm 模块。

```text
组件结构:
┌─────────────────────────────────┐
│         Component               │
│  ┌──────────────────────────┐   │
│  │  Imports (依赖接口)      │   │
│  │  - wasi:io/streams       │   │
│  │  - wasi:http/types       │   │
│  └──────────────────────────┘   │
│  ┌──────────────────────────┐   │
│  │  Core Module (核心逻辑)  │   │
│  │  - Wasm 字节码           │   │
│  └──────────────────────────┘   │
│  ┌──────────────────────────┐   │
│  │  Exports (提供接口)      │   │
│  │  - process-request       │   │
│  │  - handle-event          │   │
│  └──────────────────────────┘   │
└─────────────────────────────────┘
```

### 2. 接口 (Interface)

接口定义了组件之间的契约，使用 WIT (Wasm Interface Types) 语言描述。

```wit
// example.wit
package example:hello@1.0.0;

// 定义接口
interface greet {
    // 导出函数
    greet: func(name: string) -> string;

    // 资源类型
    resource user {
        constructor(name: string);
        get-name: func() -> string;
        greet: func() -> string;
    }
}

// 定义世界（组件的完整接口规约）
world greeter {
    export greet;
}
```

### 3. 资源 (Resources)

资源是 WASI 0.2 引入的新概念，用于表示有状态的对象。

```wit
// 资源定义示例
resource file {
    // 构造函数
    constructor(path: string);

    // 方法
    read: func() -> result<list<u8>, error>;
    write: func(data: list<u8>) -> result<_, error>;
    close: func();

    // 静态方法
    static open: func(path: string) -> result<file, error>;
}
```

### 4. WIT 类型系统

WASI 0.2 提供了丰富的类型系统：

```wit
// 基础类型
u8, u16, u32, u64
s8, s16, s32, s64
f32, f64
bool, char, string

// 复合类型
record point {
    x: f64,
    y: f64,
}

// 变体类型（枚举）
variant color {
    rgb(u8, u8, u8),
    rgba(u8, u8, u8, u8),
    name(string),
}

// 可选类型
option<T>

// 结果类型
result<T, E>

// 列表类型
list<T>

// 元组类型
tuple<T1, T2, ...>

// 标志位类型
flags permissions {
    read,
    write,
    execute,
}
```

---

## 组件模型 (Component Model)

### 架构概览

```text
组件模型层次结构:

┌──────────────────────────────────────────────┐
│            Application Layer                 │
│  ┌────────────┐  ┌────────────┐              │
│  │ Component A│  │ Component B│              │
│  └─────┬──────┘  └──────┬─────┘              │
└────────┼─────────────────┼────────────────────┘
         │                 │
┌────────▼─────────────────▼────────────────────┐
│         Component Runtime Layer              │
│  ┌───────────────────────────────────────┐   │
│  │    Component Model Runtime            │   │
│  │  - Instance Management                │   │
│  │  - Type Checking                      │   │
│  │  - Resource Lifecycle                 │   │
│  └───────────────────────────────────────┘   │
└──────────────────┬───────────────────────────┘
                   │
┌──────────────────▼───────────────────────────┐
│           Core Wasm Layer                    │
│  ┌───────────────────────────────────────┐   │
│  │    WebAssembly Core Specification     │   │
│  └───────────────────────────────────────┘   │
└──────────────────────────────────────────────┘
```

### 组件组合

WASI 0.2 支持多种组件组合模式：

#### 1. 链式组合 (Chaining)

```text
Component A → Component B → Component C
(输出)         (处理)         (输出)
```

#### 2. 并行组合 (Parallel)

```text
        ┌→ Component B →┐
Input →─┤                ├→ Aggregator → Output
        └→ Component C →┘
```

#### 3. 嵌套组合 (Nested)

```text
┌─────────────────────────────┐
│      Component A            │
│  ┌───────────────────────┐  │
│  │   Component B         │  │
│  │  ┌─────────────────┐  │  │
│  │  │  Component C    │  │  │
│  │  └─────────────────┘  │  │
│  └───────────────────────┘  │
└─────────────────────────────┘
```

### 生命周期管理

组件模型自动管理资源的生命周期：

```wit
// WIT 定义
resource connection {
    constructor(url: string);
    send: func(data: list<u8>) -> result<_, error>;
    close: func();
}

// 使用时的生命周期
interface session {
    use connection;

    // 自动管理资源生命周期
    process: func(url: string) -> result<string, error>;
}
```

---

## WIT (Wasm Interface Types)

### WIT 语法完整指南

#### 1. 包和版本控制

```wit
// 包声明（遵循语义化版本）
package wasi:http@2.0.0;

// 导入其他包
use wasi:io/streams@2.0.0.{input-stream, output-stream};
```

#### 2. 接口定义

```wit
interface logger {
    // 枚举类型
    enum log-level {
        debug,
        info,
        warning,
        error,
    }

    // 记录类型
    record log-entry {
        level: log-level,
        message: string,
        timestamp: u64,
    }

    // 函数
    log: func(entry: log-entry);

    // 带结果的函数
    flush: func() -> result<_, string>;
}
```

#### 3. 世界定义

世界 (World) 定义了一个组件的完整接口规约：

```wit
world http-handler {
    // 导入的接口
    import wasi:io/streams@2.0.0;
    import wasi:http/types@2.0.0;

    // 导出的接口
    export handler;
}

interface handler {
    handle-request: func(request: request) -> response;
}
```

#### 4. 完整示例：HTTP 客户端

```wit
package example:http-client@1.0.0;

// 导入标准 WASI 接口
use wasi:io/streams@2.0.0.{input-stream, output-stream};
use wasi:http/types@2.0.0.{
    request,
    response,
    method,
    headers,
};

interface http-client {
    // HTTP 方法
    enum http-method {
        get,
        post,
        put,
        delete,
        patch,
    }

    // 请求配置
    record request-config {
        url: string,
        method: http-method,
        headers: list<tuple<string, string>>,
        body: option<list<u8>>,
        timeout-ms: option<u32>,
    }

    // 响应
    record http-response {
        status: u16,
        headers: list<tuple<string, string>>,
        body: list<u8>,
    }

    // 错误类型
    variant http-error {
        network-error(string),
        timeout,
        invalid-url(string),
        status-error(u16),
    }

    // 主要 API
    fetch: func(config: request-config) -> result<http-response, http-error>;

    // 流式 API
    resource stream-request {
        constructor(config: request-config);
        write-chunk: func(data: list<u8>) -> result<_, http-error>;
        finish: func() -> result<http-response, http-error>;
    }
}

world http-client-world {
    import wasi:io/streams@2.0.0;
    import wasi:http/types@2.0.0;
    export http-client;
}
```

---

## 实战示例

### 示例 1：简单的 WASI 0.2 组件

#### WIT 接口定义

```wit
// calculator.wit
package example:calculator@1.0.0;

interface calculator {
    // 基础操作
    add: func(a: f64, b: f64) -> f64;
    subtract: func(a: f64, b: f64) -> f64;
    multiply: func(a: f64, b: f64) -> f64;
    divide: func(a: f64, b: f64) -> result<f64, string>;

    // 高级操作
    variant operation {
        add(f64, f64),
        subtract(f64, f64),
        multiply(f64, f64),
        divide(f64, f64),
    }

    calculate: func(op: operation) -> result<f64, string>;
}

world calculator-world {
    export calculator;
}
```

#### Rust 实现

```rust
// 使用 wit-bindgen 生成绑定
wit_bindgen::generate!({
    world: "calculator-world",
    path: "wit",
});

struct Calculator;

impl Guest for Calculator {
    fn add(a: f64, b: f64) -> f64 {
        a + b
    }

    fn subtract(a: f64, b: f64) -> f64 {
        a - b
    }

    fn multiply(a: f64, b: f64) -> f64 {
        a * b
    }

    fn divide(a: f64, b: f64) -> Result<f64, String> {
        if b == 0.0 {
            Err("Division by zero".to_string())
        } else {
            Ok(a / b)
        }
    }

    fn calculate(op: Operation) -> Result<f64, String> {
        match op {
            Operation::Add(a, b) => Ok(Self::add(a, b)),
            Operation::Subtract(a, b) => Ok(Self::subtract(a, b)),
            Operation::Multiply(a, b) => Ok(Self::multiply(a, b)),
            Operation::Divide(a, b) => Self::divide(a, b),
        }
    }
}

export!(Calculator);
```

### 示例 2：资源管理

#### WIT 定义

```wit
// file-handler.wit
package example:file@1.0.0;

interface file-handler {
    // 文件资源
    resource file {
        // 打开文件
        static open: func(path: string, mode: file-mode) -> result<file, io-error>;

        // 读取
        read: func(size: u64) -> result<list<u8>, io-error>;

        // 写入
        write: func(data: list<u8>) -> result<u64, io-error>;

        // 关闭（自动调用）
        close: func();

        // 获取元数据
        size: func() -> result<u64, io-error>;
        position: func() -> result<u64, io-error>;
        seek: func(pos: u64) -> result<_, io-error>;
    }

    enum file-mode {
        read,
        write,
        append,
        read-write,
    }

    variant io-error {
        not-found,
        permission-denied,
        already-exists,
        other(string),
    }
}

world file-handler-world {
    export file-handler;
}
```

#### Rust 实现

```rust
use std::fs;
use std::io::{Read, Write, Seek, SeekFrom};

wit_bindgen::generate!({
    world: "file-handler-world",
    path: "wit",
});

struct FileHandler;

struct FileResource {
    handle: fs::File,
}

impl GuestFile for FileResource {
    fn read(&mut self, size: u64) -> Result<Vec<u8>, IoError> {
        let mut buffer = vec![0u8; size as usize];
        match self.handle.read(&mut buffer) {
            Ok(n) => {
                buffer.truncate(n);
                Ok(buffer)
            }
            Err(e) => Err(map_io_error(e)),
        }
    }

    fn write(&mut self, data: Vec<u8>) -> Result<u64, IoError> {
        self.handle.write(&data)
            .map(|n| n as u64)
            .map_err(map_io_error)
    }

    fn close(&mut self) {
        // 资源自动清理
    }

    fn size(&self) -> Result<u64, IoError> {
        self.handle.metadata()
            .map(|m| m.len())
            .map_err(map_io_error)
    }

    fn position(&mut self) -> Result<u64, IoError> {
        self.handle.stream_position()
            .map_err(map_io_error)
    }

    fn seek(&mut self, pos: u64) -> Result<(), IoError> {
        self.handle.seek(SeekFrom::Start(pos))
            .map(|_| ())
            .map_err(map_io_error)
    }
}

impl GuestFileHandler for FileHandler {
    fn open(path: String, mode: FileMode) -> Result<FileResource, IoError> {
        let file = match mode {
            FileMode::Read => fs::File::open(path),
            FileMode::Write => fs::File::create(path),
            FileMode::Append => fs::OpenOptions::new()
                .append(true)
                .open(path),
            FileMode::ReadWrite => fs::OpenOptions::new()
                .read(true)
                .write(true)
                .open(path),
        };

        file.map(|handle| FileResource { handle })
            .map_err(map_io_error)
    }
}

fn map_io_error(e: std::io::Error) -> IoError {
    use std::io::ErrorKind;
    match e.kind() {
        ErrorKind::NotFound => IoError::NotFound,
        ErrorKind::PermissionDenied => IoError::PermissionDenied,
        ErrorKind::AlreadyExists => IoError::AlreadyExists,
        _ => IoError::Other(e.to_string()),
    }
}

export!(FileHandler);
```

### 示例 3：组件组合

#### 主机侧组合代码

```rust
use wasmtime::component::*;
use wasmtime::{Config, Engine, Store};

// 加载和链接多个组件
fn compose_components() -> anyhow::Result<()> {
    let mut config = Config::new();
    config.wasm_component_model(true);
    let engine = Engine::new(&config)?;

    // 加载组件
    let logger_component = Component::from_file(&engine, "logger.wasm")?;
    let processor_component = Component::from_file(&engine, "processor.wasm")?;

    // 创建链接器
    let mut linker = Linker::new(&engine);

    // 链接组件
    linker.instance("logger")?.component(&logger_component)?;
    linker.instance("processor")?.component(&processor_component)?;

    // 实例化
    let mut store = Store::new(&engine, ());
    let instance = linker.instantiate(&mut store, &processor_component)?;

    // 调用导出函数
    let func = instance.get_typed_func::<(&str,), (String,)>(&mut store, "process")?;
    let result = func.call(&mut store, ("input data",))?;

    println!("Result: {}", result.0);

    Ok(())
}
```

---

## 迁移指南

### 从 WASI 0.1 迁移到 0.2

#### 1. 工具链更新

```bash
# 安装最新的工具链
rustup update

# 安装 wasm32-wasip2 target (WASI 0.2)
rustup target add wasm32-wasip2

# 安装 wit-bindgen
cargo install wit-bindgen-cli

# 更新依赖
cargo add wit-bindgen
```

#### 2. 代码迁移步骤

**步骤 1: 编写 WIT 接口定义**:

```wit
// 新建 wit/world.wit
package my-app:main@1.0.0;

world app {
    // 导入 WASI 0.2 标准接口
    import wasi:cli/environment@2.0.0;
    import wasi:filesystem/types@2.0.0;

    // 导出应用接口
    export run;
}

interface run {
    execute: func() -> result<_, string>;
}
```

**步骤 2: 更新 Rust 代码**:

```rust
// 旧代码 (WASI 0.1)
fn main() {
    let args: Vec<String> = std::env::args().collect();
    println!("Args: {:?}", args);
}

// 新代码 (WASI 0.2)
wit_bindgen::generate!({
    world: "app",
    path: "wit",
});

struct MyApp;

impl Guest for MyApp {
    fn execute() -> Result<(), String> {
        // 使用新的 WASI 0.2 API
        let env = wasi::cli::environment::get_environment();
        for (key, value) in env {
            println!("{} = {}", key, value);
        }
        Ok(())
    }
}

export!(MyApp);
```

**步骤 3: 更新构建配置**:

```toml
# Cargo.toml
[package]
name = "my-app"
version = "0.1.0"
edition = "2024"

[dependencies]
wit-bindgen = "0.16"

[profile.release]
opt-level = "z"
lto = true
codegen-units = 1

[lib]
crate-type = ["cdylib"]
```

**步骤 4: 编译和测试**:

```bash
# 编译为 WASI 0.2 组件
cargo component build --release

# 使用 wasmtime 运行
wasmtime run target/wasm32-wasip2/release/my_app.wasm
```

#### 3. API 映射表

| WASI 0.1               | WASI 0.2                               | 说明       |
| ---------------------- | -------------------------------------- | ---------- |
| `wasi::fd_read`        | `wasi:io/streams.read`                 | 文件读取   |
| `wasi::fd_write`       | `wasi:io/streams.write`                | 文件写入   |
| `wasi::path_open`      | `wasi:filesystem/types.open-at`        | 打开文件   |
| `wasi::environ_get`    | `wasi:cli/environment.get-environment` | 环境变量   |
| `wasi::args_get`       | `wasi:cli/environment.get-arguments`   | 命令行参数 |
| `wasi::clock_time_get` | `wasi:clocks/wall-clock.now`           | 获取时间   |
| `wasi::random_get`     | `wasi:random/random.get-random-bytes`  | 随机数     |

---

## 最佳实践

### 1. 接口设计原则

#### ✅ 好的实践

```wit
// 使用清晰的命名
interface user-service {
    // 使用 result 类型处理错误
    get-user: func(id: u64) -> result<user, error>;

    // 使用 record 组织相关数据
    record user {
        id: u64,
        name: string,
        email: string,
    }

    // 使用 variant 表示不同状态
    variant error {
        not-found,
        permission-denied,
        internal(string),
    }
}
```

#### ❌ 避免的实践

```wit
// 不好的命名
interface svc {
    // 使用原始类型而不是 result
    get: func(i: u64) -> user;  // 无法处理错误

    // 参数过多
    update: func(
        id: u64,
        name: string,
        email: string,
        age: u32,
        city: string,
        // ...
    );  // 应该使用 record
}
```

### 2. 版本控制策略

```wit
// 使用语义化版本
package my-org:my-service@1.2.3;

// 向后兼容的添加
interface user-service {
    // v1.0.0: 原始方法
    get-user: func(id: u64) -> result<user, error>;

    // v1.1.0: 新增方法（向后兼容）
    list-users: func(offset: u32, limit: u32) -> result<list<user>, error>;

    // v1.2.0: 新增可选字段
    record user {
        id: u64,
        name: string,
        email: string,
        phone: option<string>,  // 新增，可选
    }
}
```

### 3. 性能优化

```wit
interface high-performance {
    // ✅ 批量操作减少调用开销
    batch-process: func(items: list<item>) -> result<list<result>, error>;

    // ✅ 流式处理大数据
    resource data-stream {
        read-chunk: func(size: u32) -> option<list<u8>>;
    }

    // ❌ 避免频繁的小调用
    // process-one: func(item: item) -> result;  // 不推荐
}
```

### 4. 错误处理模式

```wit
interface service {
    // 详细的错误类型
    variant service-error {
        // 客户端错误 (4xx)
        invalid-input(string),
        not-found,
        unauthorized,

        // 服务端错误 (5xx)
        internal-error(string),
        service-unavailable,

        // 特定业务错误
        business-rule-violation {
            rule: string,
            message: string,
        },
    }

    // 使用 result 返回
    perform-operation: func(input: string) -> result<output, service-error>;
}
```

### 5. 资源管理最佳实践

```wit
interface database {
    // 资源生命周期管理
    resource connection {
        // 明确的构造函数
        constructor(url: string, timeout: u32) -> result<connection, db-error>;

        // 操作方法
        query: func(sql: string) -> result<result-set, db-error>;
        execute: func(sql: string) -> result<u64, db-error>;

        // 事务支持
        begin-transaction: func() -> result<transaction, db-error>;

        // 显式释放（可选，会自动调用）
        close: func();
    }

    resource transaction {
        commit: func() -> result<_, db-error>;
        rollback: func() -> result<_, db-error>;
    }
}
```

### 6. 测试策略

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_component_interface() {
        wit_bindgen::generate!({
            world: "test-world",
            path: "wit",
        });

        // 测试接口实现
        let result = MyComponent::process("test input");
        assert!(result.is_ok());
    }

    #[test]
    fn test_component_composition() {
        // 测试组件组合
        // ...
    }
}
```

---

## 工具和生态系统

### 核心工具

| 工具                | 用途                | 链接                                                          |
| ------------------- | ------------------- | ------------------------------------------------------------- |
| **wit-bindgen**     | 从 WIT 生成语言绑定 | [GitHub](https://github.com/bytecodealliance/wit-bindgen)     |
| **wasm-tools**      | Wasm 组件工具集     | [GitHub](https://github.com/bytecodealliance/wasm-tools)      |
| **cargo-component** | Cargo 组件子命令    | [GitHub](https://github.com/bytecodealliance/cargo-component) |
| **wasmtime**        | WASI 0.2 运行时     | [GitHub](https://github.com/bytecodealliance/wasmtime)        |

### 常用命令

```bash
# 安装工具
cargo install cargo-component
cargo install wasm-tools

# 创建新组件项目
cargo component new my-component

# 编译组件
cargo component build --release

# 检查组件
wasm-tools component wit target/wasm32-wasip2/release/my_component.wasm

# 验证组件
wasm-tools validate target/wasm32-wasip2/release/my_component.wasm

# 组合组件
wasm-tools compose component-a.wasm component-b.wasm -o composed.wasm
```

---

## 总结

### 关键要点

1. **组件模型**是 WASI 0.2 的核心，实现真正的语言无关互操作
2. **WIT** 提供声明式接口定义，类型安全且易于维护
3. **资源管理**自动化生命周期，减少内存泄漏风险
4. **组件组合**使模块化开发更加灵活和强大

### 下一步行动

- [ ] 学习并实践 WIT 接口定义
- [ ] 将现有 WASI 0.1 项目迁移到 0.2
- [ ] 探索组件组合的高级用法
- [ ] 为你的库创建 WASI 0.2 组件版本
- [ ] 贡献到 WASI 生态系统

### 参考资源

- [Component Model Specification](https://github.com/WebAssembly/component-model)
- [WASI Preview 2 Documentation](https://github.com/WebAssembly/WASI/tree/main/preview2)
- [WIT Specification](https://github.com/WebAssembly/component-model/blob/main/design/mvp/WIT.md)
- [Bytecode Alliance](https://bytecodealliance.org/)

---

**文档维护**: Documentation Team
**最后更新**: 2025-12-11
**下一次更新**: 根据 WASI 规范更新而定

---

_WASI 0.2 组件模型代表了 WebAssembly 生态系统的重大飞跃，掌握它将使你能够构建更加模块化、可维护和高性能的应用程序。_ 🚀
