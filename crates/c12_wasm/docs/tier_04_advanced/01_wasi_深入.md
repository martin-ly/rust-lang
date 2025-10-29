# C12 WASM - WASI 深入

> **文档类型**: Tier 4 - 高级层
> **文档定位**: WASI 系统接口深入指南
> **项目状态**: ✅ 完整完成
> **相关文档**: [生产级部署](./03_生产级部署.md) | [性能分析与优化](./02_性能分析与优化.md)

**最后更新**: 2025-10-30
**适用版本**: Rust 1.90+ / Edition 2024, WASM 2.0 + WASI 0.2

---

## 📋 目录

- [C12 WASM - WASI 深入](#c12-wasm---wasi-深入)
  - [📊 目录](#-目录)
  - [🎯 概述](#-概述)
  - [🌐 WASI 基础](#-wasi-基础)
  - [🖥️ 本地操作系统运行 WASM](#️-本地操作系统运行-wasm)
    - [为什么在本地运行 WASM？](#为什么在本地运行-wasm)
    - [主要运行时对比](#主要运行时对比)
    - [编译到 WASI 目标](#编译到-wasi-目标)
    - [Cargo.toml 配置](#cargotoml-配置)
    - [示例：简单的 WASI 程序](#示例简单的-wasi-程序)
  - [📁 文件系统](#-文件系统)
  - [🌐 网络接口](#-网络接口)
  - [⏰ 时间接口](#-时间接口)
  - [🚀 实践示例](#-实践示例)
    - [示例 1: 文件处理](#示例-1-文件处理)
    - [示例 2: 使用 WasmEdge 运行 HTTP 服务器](#示例-2-使用-wasmedge-运行-http-服务器)
    - [示例 3: 环境变量和命令行参数](#示例-3-环境变量和命令行参数)
    - [示例 4: 文件系统操作](#示例-4-文件系统操作)
  - [🔧 运行时配置](#-运行时配置)
    - [WasmEdge 配置](#wasmedge-配置)
    - [wasmtime 配置](#wasmtime-配置)
    - [wasmer 配置](#wasmer-配置)
  - [🌐 在 Docker 中运行 WASM](#-在-docker-中运行-wasm)
  - [📊 性能对比](#-性能对比)
  - [📚 相关资源](#-相关资源)

---

## 🎯 概述

本指南深入介绍 WASI (WebAssembly System Interface) 系统接口的使用，以及在本地操作系统上运行 WASM 应用程序的方法。

---

## 🌐 WASI 基础

WASI 是 WebAssembly 的系统接口，提供了：

- 文件系统访问
- 网络接口
- 时间接口
- 环境变量
- 进程管理

## 🖥️ 本地操作系统运行 WASM

### 为什么在本地运行 WASM？

**优势**:

- ✅ **高性能**: 接近原生代码的执行速度
- ✅ **安全性**: 沙箱执行环境，隔离性强
- ✅ **跨平台**: 一次编译，到处运行
- ✅ **轻量级**: 运行时体积小，启动快
- ✅ **生态支持**: 丰富的工具链和运行时

### 主要运行时对比

| 运行时 | 特点 | 适用场景 | 性能 |
|--------|------|----------|------|
| **WasmEdge** | 轻量级、AI 支持 | 云原生、边缘计算 | ⭐⭐⭐⭐⭐ |
| **wasmtime** | 标准化、稳定 | 服务器应用、CLI 工具 | ⭐⭐⭐⭐ |
| **wasmer** | 高性能、多后端 | 通用应用 | ⭐⭐⭐⭐⭐ |
| **wasm3** | 极轻量、解释器 | 嵌入式、IoT | ⭐⭐⭐ |

### 编译到 WASI 目标

要在本地操作系统运行 WASM 程序，需要编译到 `wasm32-wasi` 目标：

```bash
# 添加 WASI 目标
rustup target add wasm32-wasi

# 编译到 WASI
cargo build --target wasm32-wasi --release

# 输出文件
# target/wasm32-wasi/release/your_app.wasm
```

### Cargo.toml 配置

```toml
[package]
name = "my-wasi-app"
version = "0.1.0"
edition = "2024"

[dependencies]
# WASI 应用程序通常不需要额外的依赖
# 标准库已经包含了 WASI 支持

[[bin]]
name = "my-app"
path = "src/main.rs"
```

### 示例：简单的 WASI 程序

```rust
// src/main.rs
use std::env;
use std::fs;

fn main() {
    // 读取命令行参数
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: {} <filename>", args[0]);
        std::process::exit(1);
    }

    // 读取文件
    let filename = &args[1];
    match fs::read_to_string(filename) {
        Ok(content) => {
            println!("File content:\n{}", content);
        }
        Err(e) => {
            eprintln!("Error reading file: {}", e);
            std::process::exit(1);
        }
    }
}
```

**编译和运行**:

```bash
# 编译
cargo build --target wasm32-wasi --release

# 使用 WasmEdge 运行
wasmedge target/wasm32-wasi/release/my_app.wasm input.txt

# 使用 wasmtime 运行
wasmtime run target/wasm32-wasi/release/my_app.wasm -- input.txt

# 使用 wasmer 运行
wasmer run target/wasm32-wasi/release/my_app.wasm -- input.txt
```

---

## 📁 文件系统

### 读取文件

```rust
use std::fs;

#[no_mangle]
pub extern "C" fn read_file() -> String {
    fs::read_to_string("data.txt").unwrap_or_default()
}
```

### 写入文件

```rust
use std::fs;

#[no_mangle]
pub extern "C" fn write_file(content: &str) {
    fs::write("output.txt", content).unwrap();
}
```

---

## 🌐 网络接口

### HTTP 请求

```rust
use std::io::Read;
use std::net::TcpStream;

pub fn http_get(url: &str) -> String {
    // 简化的 HTTP GET 实现
    let mut stream = TcpStream::connect(format!("{}:80", url)).unwrap();
    let mut response = String::new();
    stream.read_to_string(&mut response).unwrap();
    response
}
```

---

## ⏰ 时间接口

```rust
use std::time::{SystemTime, UNIX_EPOCH};

pub fn current_timestamp() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs()
}
```

---

## 🚀 实践示例

### 示例 1: 文件处理

```rust
use std::fs;

pub fn process_file(path: &str) -> String {
    fs::read_to_string(path)
        .unwrap_or_default()
        .to_uppercase()
}
```

### 示例 2: 使用 WasmEdge 运行 HTTP 服务器

```rust
// src/main.rs
use std::io::{Read, Write};
use std::net::TcpListener;

fn main() {
    let listener = TcpListener::bind("127.0.0.1:8080").unwrap();
    println!("Server listening on http://127.0.0.1:8080");

    for stream in listener.incoming() {
        match stream {
            Ok(mut stream) => {
                let mut buffer = [0; 1024];
                stream.read(&mut buffer).unwrap();

                let response = "HTTP/1.1 200 OK\r\n\r\nHello, WASI!";
                stream.write(response.as_bytes()).unwrap();
                stream.flush().unwrap();
            }
            Err(e) => {
                eprintln!("Error: {}", e);
            }
        }
    }
}
```

**使用 WasmEdge 运行**:

```bash
# 编译
cargo build --target wasm32-wasi --release

# 运行（需要网络权限）
wasmedge --allow-net target/wasm32-wasi/release/server.wasm
```

### 示例 3: 环境变量和命令行参数

```rust
use std::env;

fn main() {
    // 读取环境变量
    if let Ok(value) = env::var("MY_VAR") {
        println!("Environment variable MY_VAR: {}", value);
    }

    // 读取命令行参数
    let args: Vec<String> = env::args().collect();
    println!("Arguments: {:?}", args);

    // 获取当前工作目录
    if let Ok(current_dir) = env::current_dir() {
        println!("Current directory: {}", current_dir.display());
    }
}
```

**运行**:

```bash
# 设置环境变量并运行
MY_VAR=hello wasmedge target/wasm32-wasi/release/my_app.wasm arg1 arg2
```

### 示例 4: 文件系统操作

```rust
use std::fs;
use std::path::Path;

fn main() {
    // 创建目录
    fs::create_dir_all("output").unwrap();

    // 写入文件
    fs::write("output/data.txt", "Hello, WASI!").unwrap();

    // 读取文件
    let content = fs::read_to_string("output/data.txt").unwrap();
    println!("File content: {}", content);

    // 列出目录内容
    if let Ok(entries) = fs::read_dir("output") {
        for entry in entries {
            if let Ok(entry) = entry {
                println!("Found: {}", entry.path().display());
            }
        }
    }
}
```

**运行（需要目录访问权限）**:

```bash
# 挂载目录
wasmedge --dir .:/app target/wasm32-wasi/release/my_app.wasm
```

---

## 🔧 运行时配置

### WasmEdge 配置

**目录挂载**:

```bash
# 挂载多个目录
wasmedge --dir .:/app --dir /tmp:/tmp target/wasm32-wasi/release/app.wasm
```

**网络访问**:

```bash
# 允许所有网络访问
wasmedge --allow-net target/wasm32-wasi/release/app.wasm

# 只允许特定域名
wasmedge --allow-net=example.com target/wasm32-wasi/release/app.wasm
```

**环境变量**:

```bash
# 设置环境变量
wasmedge --env "KEY1=VALUE1" --env "KEY2=VALUE2" app.wasm
```

**资源限制**:

```bash
# 限制内存使用（64MB）
wasmedge --max-memory-size=67108864 app.wasm

# 限制 CPU 时间（秒）
wasmedge --time-limit=10 app.wasm
```

### wasmtime 配置

```bash
# 设置内存限制
wasmtime run --max-memory=64M app.wasm

# 启用缓存
wasmtime run --cache-config cache.toml app.wasm

# 设置网络访问
wasmtime run --allow-net app.wasm
```

### wasmer 配置

```bash
# 使用不同的编译器后端
wasmer run --backend=cranelift app.wasm
wasmer run --backend=llvm app.wasm
wasmer run --backend=singlepass app.wasm

# 编译为原生二进制
wasmer compile app.wasm -o app.bin
./app.bin
```

---

## 🌐 在 Docker 中运行 WASM

### Dockerfile 示例

```dockerfile
FROM scratch
COPY target/wasm32-wasi/release/app.wasm /app.wasm
ENTRYPOINT ["wasmedge", "/app.wasm"]
```

### 使用 Docker Compose

```yaml
version: '3.8'
services:
  wasm-app:
    image: wasmedge/wasmedge:latest
    volumes:
      - ./target/wasm32-wasi/release:/app
    command: wasmedge /app/app.wasm
    environment:
      - MY_VAR=value
```

---

## 📊 性能对比

### 启动时间对比

| 运行时 | 启动时间 | 内存占用 |
|--------|----------|----------|
| WasmEdge | ~1ms | ~5MB |
| wasmtime | ~5ms | ~10MB |
| wasmer | ~2ms | ~8MB |
| Native | ~0.1ms | ~1MB |

### 执行性能对比

对于大多数应用，WASM 运行时的性能约为原生代码的：

- **WasmEdge**: 90-95%
- **wasmtime**: 85-90%
- **wasmer**: 90-95%

---

## 📚 相关资源

- [WASI 规范](https://wasi.dev/)
- [WasmEdge 官方文档](https://wasmedge.org/docs/)
- [wasmtime 文档](https://docs.wasmtime.dev/)
- [wasmer 文档](https://docs.wasmer.io/)
- [WASI SDK](https://github.com/WebAssembly/wasi-sdk)

---

**文档维护**: Documentation Team
**创建日期**: 2025-10-30
**适用版本**: Rust 1.90+ / Edition 2024, WASM 2.0 + WASI 0.2
