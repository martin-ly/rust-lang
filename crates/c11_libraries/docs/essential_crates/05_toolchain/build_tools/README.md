# 构建工具 (Build Tools)

**类别**: 第5层 - 工具链  
**重要程度**: ⭐⭐⭐⭐⭐ (必备)  
**更新日期**: 2025-10-20

---

## 📋 目录

- [构建工具 (Build Tools)](#构建工具-build-tools)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🔧 核心工具](#-核心工具)
    - [1. Cargo (必备 ⭐⭐⭐⭐⭐)](#1-cargo-必备-)
      - [核心功能](#核心功能)
      - [常用命令](#常用命令)
      - [Cargo.toml 配置](#cargotoml-配置)
    - [2. cargo-watch (强烈推荐 🌟)](#2-cargo-watch-强烈推荐-)
      - [基础用法](#基础用法)
      - [高级用法](#高级用法)
    - [3. cargo-make (推荐 💡)](#3-cargo-make-推荐-)
      - [Makefile.toml 示例](#makefiletoml-示例)
      - [使用](#使用)
    - [4. cargo-edit (推荐 💡)](#4-cargo-edit-推荐-)
      - [功能](#功能)
    - [5. cargo-cache (可选)](#5-cargo-cache-可选)
  - [💡 最佳实践](#-最佳实践)
    - [1. 工作空间配置](#1-工作空间配置)
    - [2. 性能优化配置](#2-性能优化配置)
    - [3. 自定义构建脚本](#3-自定义构建脚本)
  - [📊 工具对比](#-工具对比)
    - [构建速度优化](#构建速度优化)
  - [🎯 实战示例](#-实战示例)
    - [完整开发工作流](#完整开发工作流)
  - [🔗 相关资源](#-相关资源)

## 📋 概述

Rust 的构建工具生态系统以 Cargo 为核心，提供了从项目创建到构建、测试、发布的完整工作流。

---

## 🔧 核心工具

### 1. Cargo (必备 ⭐⭐⭐⭐⭐)

**官网**: <https://doc.rust-lang.org/cargo/>  
**用途**: Rust 官方包管理器和构建工具

#### 核心功能

- ✅ 项目创建和管理
- ✅ 依赖管理
- ✅ 构建和编译
- ✅ 测试运行
- ✅ 文档生成
- ✅ 包发布

#### 常用命令

```bash
# 项目管理
cargo new my_project           # 创建二进制项目
cargo new --lib my_lib         # 创建库项目
cargo init                     # 在现有目录初始化

# 构建
cargo build                    # Debug 构建
cargo build --release          # Release 构建
cargo check                    # 只检查，不生成二进制

# 运行
cargo run                      # 运行项目
cargo run --release            # Release 模式运行

# 测试
cargo test                     # 运行所有测试
cargo test test_name           # 运行特定测试
cargo test -- --nocapture      # 显示 println! 输出

# 文档
cargo doc --open               # 生成并打开文档

# 清理
cargo clean                    # 清理构建产物
```

#### Cargo.toml 配置

```toml
[package]
name = "my_project"
version = "0.1.0"
edition = "2021"
authors = ["Your Name <you@example.com>"]
license = "MIT"
description = "A short description"
repository = "https://github.com/yourusername/my_project"

[dependencies]
# 普通依赖
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1", features = ["full"] }

# 开发依赖
[dev-dependencies]
criterion = "0.5"
mockall = "0.12"

# 构建依赖
[build-dependencies]
cc = "1.0"

# 工作空间
[workspace]
members = ["crate1", "crate2"]

# 性能配置
[profile.release]
opt-level = 3              # 最大优化
lto = true                 # 链接时优化
codegen-units = 1          # 单个代码生成单元
strip = true               # 移除符号

[profile.dev]
opt-level = 0              # 无优化
debug = true               # 包含调试信息
```

---

### 2. cargo-watch (强烈推荐 🌟)

**安装**: `cargo install cargo-watch`  
**用途**: 文件变化时自动重新构建

#### 基础用法

```bash
# 监听变化并检查
cargo watch -x check

# 监听变化并测试
cargo watch -x test

# 监听变化并运行
cargo watch -x run

# 组合命令
cargo watch -x check -x test -x run

# 清屏重新运行
cargo watch -c -x run

# 忽略特定文件
cargo watch -i "*.tmp" -x check
```

#### 高级用法

```bash
# 只监听特定文件
cargo watch -w src/ -x test

# 延迟执行
cargo watch -d 1 -x test  # 1秒延迟

# 执行 shell 命令
cargo watch -s "cargo check && cargo test"
```

---

### 3. cargo-make (推荐 💡)

**安装**: `cargo install cargo-make`  
**用途**: 任务运行器，类似 make

#### Makefile.toml 示例

```toml
[tasks.default]
alias = "ci"

[tasks.ci]
dependencies = ["format", "clippy", "test", "doc"]

[tasks.format]
command = "cargo"
args = ["fmt", "--", "--check"]

[tasks.clippy]
command = "cargo"
args = ["clippy", "--", "-D", "warnings"]

[tasks.test]
command = "cargo"
args = ["nextest", "run"]

[tasks.doc]
command = "cargo"
args = ["doc", "--no-deps"]

[tasks.coverage]
command = "cargo"
args = ["tarpaulin", "--out", "Html"]

[tasks.clean-all]
command = "cargo"
args = ["clean"]
```

#### 使用

```bash
# 运行默认任务
cargo make

# 运行特定任务
cargo make test
cargo make coverage

# 运行生产构建
cargo make --profile production build
```

---

### 4. cargo-edit (推荐 💡)

**安装**: `cargo install cargo-edit`  
**用途**: 命令行编辑 Cargo.toml

#### 功能

```bash
# 添加依赖
cargo add serde
cargo add tokio --features full
cargo add --dev criterion

# 移除依赖
cargo rm serde

# 升级依赖
cargo upgrade
cargo upgrade --dry-run

# 设置版本
cargo set-version 1.2.3
```

---

### 5. cargo-cache (可选)

**安装**: `cargo install cargo-cache`  
**用途**: 管理 Cargo 缓存

```bash
# 查看缓存大小
cargo cache

# 清理旧缓存
cargo cache --autoclean

# 清理注册表缓存
cargo cache --remove-dir registry-index
```

---

## 💡 最佳实践

### 1. 工作空间配置

```toml
# 根 Cargo.toml
[workspace]
members = [
    "crates/lib1",
    "crates/lib2",
    "examples/*",
]

# 共享依赖版本
[workspace.dependencies]
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1", features = ["full"] }

# 在子 crate 中使用
[dependencies]
serde = { workspace = true }
tokio = { workspace = true }
```

### 2. 性能优化配置

```toml
# Cargo.toml
[profile.release]
opt-level = 3
lto = "fat"
codegen-units = 1
strip = true
panic = "abort"

[profile.dev.package."*"]
opt-level = 2  # 优化依赖
```

### 3. 自定义构建脚本

```rust
// build.rs
use std::env;

fn main() {
    // 读取环境变量
    let target = env::var("TARGET").unwrap();
    
    // 条件编译
    if target.contains("linux") {
        println!("cargo:rustc-cfg=linux");
    }
    
    // 链接库
    println!("cargo:rustc-link-lib=ssl");
    
    // 重新运行条件
    println!("cargo:rerun-if-changed=build.rs");
}
```

---

## 📊 工具对比

### 构建速度优化

| 方法 | 效果 | 适用场景 |
|------|------|---------|
| `cargo check` | ⭐⭐⭐⭐⭐ | 开发时快速反馈 |
| `sccache` | ⭐⭐⭐⭐ | 多项目共享缓存 |
| `mold`/`lld` 链接器 | ⭐⭐⭐⭐ | 大型项目 |
| Incremental 编译 | ⭐⭐⭐ | 默认开启 |

---

## 🎯 实战示例

### 完整开发工作流

```bash
#!/bin/bash

# 1. 创建新项目
cargo new my_awesome_project
cd my_awesome_project

# 2. 添加依赖
cargo add serde -F derive
cargo add tokio -F full
cargo add --dev criterion

# 3. 开发阶段 (新终端)
cargo watch -c -x 'check' -x 'test --lib'

# 4. 代码检查
cargo fmt
cargo clippy -- -D warnings

# 5. 完整测试
cargo nextest run
cargo tarpaulin --out Html

# 6. 性能测试
cargo bench

# 7. 生成文档
cargo doc --no-deps --open

# 8. 发布构建
cargo build --release

# 9. 安全审计
cargo audit
cargo deny check
```

---

## 🔗 相关资源

- [Cargo Book](https://doc.rust-lang.org/cargo/)
- [cargo-watch](https://github.com/watchexec/cargo-watch)
- [cargo-make](https://github.com/sagiegurari/cargo-make)
- [cargo-edit](https://github.com/killercup/cargo-edit)

---

**导航**: [返回工具链层](../README.md) | [下一类别：代码质量](../code_quality/README.md)
