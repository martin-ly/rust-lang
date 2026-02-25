# Cargo 工作空间与依赖管理

> **创建日期**: 2026-02-15
> **最后更新**: 2026-02-15
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📊 目录 {#-目录}

- [Cargo 工作空间与依赖管理](#cargo-工作空间与依赖管理)
  - [📊 目录 {#-目录}](#-目录--目录)
  - [🎯 文档说明 {#-文档说明}](#-文档说明--文档说明)
  - [1. Cargo 工作空间概览](#1-cargo-工作空间概览)
    - [1.1 什么是 Workspace](#11-什么是-workspace)
    - [1.2 Workspace 优势](#12-workspace-优势)
  - [2. 创建和配置 Workspace](#2-创建和配置-workspace)
    - [2.1 基础结构](#21-基础结构)
    - [2.2 Workspace 配置](#22-workspace-配置)
    - [2.3 虚拟工作空间](#23-虚拟工作空间)
  - [3. 依赖管理](#3-依赖管理)
    - [3.1 Workspace 依赖 (Rust 1.64+)](#31-workspace-依赖-rust-164)
    - [3.2 路径依赖](#32-路径依赖)
    - [3.3 依赖版本统一](#33-依赖版本统一)
  - [4. Resolver 3 (Edition 2024)](#4-resolver-3-edition-2024)
    - [4.1 新特性](#41-新特性)
    - [4.2 配置 Resolver 3](#42-配置-resolver-3)
    - [4.3 迁移指南](#43-迁移指南)
  - [5. Feature 管理](#5-feature-管理)
    - [5.1 定义 Features](#51-定义-features)
    - [5.2 Workspace Features](#52-workspace-features)
    - [5.3 Feature 最佳实践](#53-feature-最佳实践)
  - [6. Cargo 命令增强](#6-cargo-命令增强)
    - [6.1 Workspace 命令](#61-workspace-命令)
    - [6.2 增强的构建命令](#62-增强的构建命令)
    - [6.3 发布管理](#63-发布管理)
  - [7. 构建优化](#7-构建优化)
    - [7.1 共享构建缓存](#71-共享构建缓存)
    - [7.2 并行构建](#72-并行构建)
    - [7.3 增量编译](#73-增量编译)
  - [8. 依赖图与分析](#8-依赖图与分析)
    - [8.1 查看依赖树](#81-查看依赖树)
    - [8.2 依赖审计](#82-依赖审计)
    - [8.3 依赖更新](#83-依赖更新)
  - [9. 私有依赖与 Registry](#9-私有依赖与-registry)
    - [9.1 私有 Git 仓库](#91-私有-git-仓库)
    - [9.2 私有 Registry](#92-私有-registry)
  - [10. Cargo 配置](#10-cargo-配置)
    - [10.1 配置文件层级](#101-配置文件层级)
    - [10.2 常用配置](#102-常用配置)
  - [11. 实战案例](#11-实战案例)
    - [11.1 大型多 crate 项目 - 完整配置](#111-大型多-crate-项目---完整配置)
    - [11.2 微服务架构 - 完整示例](#112-微服务架构---完整示例)
  - [12. 最佳实践](#12-最佳实践)
    - [✅ 推荐做法](#-推荐做法)
    - [⚠️ 常见陷阱 {#️-常见陷阱}](#️-常见陷阱-️-常见陷阱)
  - [13. 故障排查](#13-故障排查)
    - [常见问题](#常见问题)
  - [14. 相关资源](#14-相关资源)
    - [📚 官方文档 {#-官方文档}](#-官方文档--官方文档)
    - [🔗 相关文档 {#-相关文档}](#-相关文档--相关文档)
    - [📦 推荐工具](#-推荐工具)

## 🎯 文档说明 {#-文档说明}

本文档全面介绍 Cargo 工作空间 (Workspace)、依赖管理、以及 Cargo 的最新增强功能，帮助开发者高效管理多 crate 项目。

**覆盖内容**: Workspace 配置、依赖解析、Feature 管理、Cargo 命令、构建优化

---

## 1. Cargo 工作空间概览

### 1.1 什么是 Workspace

**定义**: Workspace 是一个包含多个相关 crate 的项目结构，它们共享：

- ✅ **Cargo.lock**: 统一的依赖版本
- ✅ **target 目录**: 共享构建缓存
- ✅ **配置**: 统一的编译选项

**典型结构**:

```text
my-workspace/
├── Cargo.toml          # Workspace 配置
├── Cargo.lock          # 锁定的依赖版本
├── target/             # 共享构建输出
├── crate-a/
│   ├── Cargo.toml
│   └── src/
│       └── lib.rs
├── crate-b/
│   ├── Cargo.toml
│   └── src/
│       └── lib.rs
└── crate-c/
    ├── Cargo.toml
    └── src/
        └── main.rs
```

---

### 1.2 Workspace 优势

1. **依赖版本统一**: 避免版本冲突
2. **构建缓存共享**: 加速编译
3. **统一管理**: 一次命令操作所有 crate
4. **简化发布**: 协调多 crate 发布流程
5. **IDE 友好**: 更好的代码导航和重构

---

## 2. 创建和配置 Workspace

### 2.1 基础结构

**创建 Workspace**:

```bash
# 1. 创建根目录
mkdir my-workspace
cd my-workspace

# 2. 创建 Workspace Cargo.toml
cat > Cargo.toml << 'EOF'
[workspace]
members = [
    "crate-a",
    "crate-b",
    "crate-c",
]
resolver = "2"
EOF

# 3. 创建成员 crate
cargo new --lib crate-a
cargo new --lib crate-b
cargo new crate-c
```

---

### 2.2 Workspace 配置

**完整配置示例**:

```toml
[workspace]
# 指定成员 crate
members = [
    "crate-a",
    "crate-b",
    "crate-c",
]

# 排除某些目录 (可选)
exclude = [
    "examples/old-stuff",
    "target/",
]

# 依赖解析器 (推荐使用 "2")
resolver = "2"

# 工作空间级别的依赖 (Rust 1.64+)
[workspace.dependencies]
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1.0", features = ["full"] }
anyhow = "1.0"

# 工作空间级别的 metadata
[workspace.metadata]
authors = ["Team Name <team@example.com>"]
documentation = "https://docs.example.com"
```

---

### 2.3 虚拟工作空间

**场景**: 根目录没有 crate，只用于组织子 crate

```toml
# 根目录 Cargo.toml
[workspace]
members = ["crate-a", "crate-b"]
resolver = "2"

# 注意: 不包含 [package] 或 [dependencies] 部分
```

---

## 3. 依赖管理

### 3.1 Workspace 依赖 (Rust 1.64+)

**统一依赖版本**:

```toml
# 根 Cargo.toml
[workspace.dependencies]
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1.0", features = ["rt-multi-thread", "macros"] }
anyhow = "1.0"
```

**成员 crate 使用**:

```toml
# crate-a/Cargo.toml
[package]
name = "crate-a"
version = "0.1.0"
edition = "2024"

[dependencies]
serde = { workspace = true }  # 使用 workspace 定义的版本
tokio = { workspace = true, features = ["io-util"] }  # 可以添加额外 features
anyhow = { workspace = true }
```

**优势**:

- ✅ 确保所有 crate 使用相同版本
- ✅ 集中管理依赖
- ✅ 简化 Cargo.toml
- ✅ 避免版本冲突

---

### 3.2 路径依赖

**内部依赖**:

```toml
# crate-c/Cargo.toml
[dependencies]
crate-a = { path = "../crate-a" }
crate-b = { path = "../crate-b", features = ["extra"] }
```

**发布时的处理**:

```toml
# 发布到 crates.io 时，路径依赖需要指定版本
[dependencies]
crate-a = { path = "../crate-a", version = "0.1" }
```

---

### 3.3 依赖版本统一

**问题**: 不同 crate 使用不同版本的同一依赖

```toml
# ❌ 避免
# crate-a/Cargo.toml
[dependencies]
serde = "1.0.150"

# crate-b/Cargo.toml
[dependencies]
serde = "1.0.180"  # 版本不一致！
```

**解决方案**: 使用 Workspace 依赖

```toml
# ✅ 推荐 {#-推荐做法}
# 根 Cargo.toml
[workspace.dependencies]
serde = "1.0.180"

# 所有 crate 使用
[dependencies]
serde = { workspace = true }
```

---

## 4. Resolver 3 (Edition 2024)

### 4.1 新特性

**改进**:

1. **更智能的 Feature 解析**: 避免不必要的 feature 启用
2. **目标平台特定依赖**: 更好的跨平台支持
3. **构建依赖隔离**: `build-dependencies` 不影响主依赖
4. **性能提升**: 依赖解析速度提升 ~10-20%

---

### 4.2 配置 Resolver 3

```toml
[workspace]
members = ["crate-a", "crate-b"]
resolver = "3"  # Edition 2024 引入
```

**或针对单个 crate**:

```toml
[package]
name = "my-crate"
version = "0.1.0"
edition = "2024"  # 自动使用 resolver 3

# 或显式指定
[package.metadata.resolver]
version = "3"
```

---

### 4.3 迁移指南

**步骤**:

1. 更新到 Edition 2024
2. 测试构建: `cargo build --all-targets`
3. 检查 feature 启用: `cargo tree -f "{p} {f}"`
4. 修复任何构建失败

**常见问题**:

```toml
# 问题: 某些 features 不再自动启用
# 解决: 显式启用需要的 features
[dependencies]
tokio = { version = "1.0", features = ["macros", "rt"] }
```

---

## 5. Feature 管理

### 5.1 定义 Features

```toml
[package]
name = "my-crate"

[features]
# 默认 feature
default = ["std"]

# 基础 features
std = []
alloc = []

# 功能 features
async = ["tokio"]
database = ["sqlx", "async"]
full = ["std", "async", "database"]

# 实验性 features
experimental = []

[dependencies]
tokio = { version = "1.0", optional = true }
sqlx = { version = "0.7", optional = true }
```

---

### 5.2 Workspace Features

**统一 Feature 策略**:

```toml
# 根 Cargo.toml
[workspace.dependencies]
tokio = { version = "1.0", features = ["rt-multi-thread"] }

# crate-a/Cargo.toml
[dependencies]
tokio = { workspace = true, features = ["macros"] }  # 添加 macros feature

# crate-b/Cargo.toml
[dependencies]
tokio = { workspace = true, features = ["io-util"] }  # 添加 io-util feature
```

**最终 tokio 的 features**: `["rt-multi-thread", "macros", "io-util"]` (合并)

---

### 5.3 Feature 最佳实践

**✅ 推荐**:

```toml
[features]
# 1. 提供 default feature
default = ["std"]

# 2. 支持 no_std
std = ["dep:std-crate"]

# 3. 分层 features
basic = []
advanced = ["basic", "extra-features"]
full = ["advanced", "all-features"]

# 4. 明确命名
database-postgres = ["sqlx/postgres"]
database-mysql = ["sqlx/mysql"]
```

**⚠️ 避免**:

```toml
[features]
# ❌ 避免: 过于细粒度
feature1 = []
feature2 = []
# ... 100 个 features

# ❌ 避免: 命名不清晰
f1 = []
opt = []
```

---

## 6. Cargo 命令增强

### 6.1 Workspace 命令

**构建所有成员**:

```bash
# 构建所有 workspace 成员
cargo build --workspace
# 或
cargo build --all

# 构建指定成员
cargo build -p crate-a -p crate-b

# 排除某些成员
cargo build --workspace --exclude crate-c
```

**测试**:

```bash
# 测试所有成员
cargo test --workspace

# 测试指定成员
cargo test -p crate-a

# 运行集成测试
cargo test --all-targets
```

**检查 & Clippy**:

```bash
# 检查所有成员
cargo check --workspace

# Clippy
cargo clippy --workspace --all-targets --all-features
```

---

### 6.2 增强的构建命令

**指定目标**:

```bash
# 构建所有 targets (lib, bin, tests, benches, examples)
cargo build --all-targets

# 仅构建 binary
cargo build --bin my-app

# 构建 example
cargo build --example demo
```

**指定 features**:

```bash
# 启用特定 features
cargo build --features "async,database"

# 启用所有 features
cargo build --all-features

# 不使用默认 features
cargo build --no-default-features
```

**目标平台**:

```bash
# 交叉编译
cargo build --target x86_64-unknown-linux-gnu
cargo build --target aarch64-unknown-linux-gnu
cargo build --target wasm32-unknown-unknown
```

---

### 6.3 发布管理

**发布 workspace 成员**:

```bash
# 发布单个 crate
cargo publish -p crate-a

# 检查发布准备
cargo publish -p crate-a --dry-run

# 依次发布所有 crates (手动)
cargo publish -p crate-a
cargo publish -p crate-b
cargo publish -p crate-c
```

**使用 `cargo-release`** (推荐):

```bash
# 安装
cargo install cargo-release

# 发布所有 crates
cargo release --workspace

# 预览
cargo release --workspace --dry-run
```

---

## 7. 构建优化

### 7.1 共享构建缓存

**Workspace 自动共享**:

- 所有成员共享 `target/` 目录
- 相同依赖只编译一次
- 显著减少总构建时间

**清理缓存**:

```bash
# 清理所有构建产物
cargo clean

# 清理指定 package
cargo clean -p crate-a
```

---

### 7.2 并行构建

**配置**:

```toml
# .cargo/config.toml
[build]
jobs = 8  # 并行任务数
```

**命令行**:

```bash
# 指定并行度
cargo build -j 8

# 使用所有 CPU
cargo build -j $(nproc)
```

---

### 7.3 增量编译

```toml
[profile.dev]
incremental = true  # 默认开启

[profile.release]
incremental = false  # 生产环境建议关闭
```

---

## 8. 依赖图与分析

### 8.1 查看依赖树

```bash
# 查看依赖树
cargo tree

# 查看指定 crate 的依赖
cargo tree -p crate-a

# 查看所有 features
cargo tree -f "{p} {f}"

# 反向依赖
cargo tree -i serde
# 显示: 哪些 crates 依赖 serde

# 导出为 DOT 格式
cargo tree --format "{p}" | dot -Tpng > deps.png
```

---

### 8.2 依赖审计

**使用 `cargo-audit`**:

```bash
# 安装
cargo install cargo-audit

# 检查安全漏洞
cargo audit

# 修复已知漏洞
cargo audit fix
```

**使用 `cargo-deny`**:

```bash
# 安装
cargo install cargo-deny

# 初始化配置
cargo deny init

# 检查 licenses, bans, advisories, sources
cargo deny check
```

---

### 8.3 依赖更新

```bash
# 更新 Cargo.lock (不修改 Cargo.toml)
cargo update

# 更新指定依赖
cargo update -p serde

# 使用 cargo-edit
cargo install cargo-edit

# 升级所有依赖
cargo upgrade

# 交互式升级
cargo upgrade --dry-run
```

---

## 9. 私有依赖与 Registry

### 9.1 私有 Git 仓库

```toml
[dependencies]
my-private-crate = { git = "https://github.com/myorg/my-crate.git" }

# 指定分支
my-crate = { git = "https://github.com/myorg/my-crate.git", branch = "develop" }

# 指定 tag
my-crate = { git = "https://github.com/myorg/my-crate.git", tag = "v1.0.0" }

# 指定 commit
my-crate = { git = "https://github.com/myorg/my-crate.git", rev = "abc123" }
```

**SSH 认证**:

```toml
[dependencies]
my-crate = { git = "ssh://git@github.com/myorg/my-crate.git" }
```

---

### 9.2 私有 Registry

**配置私有 registry**:

```toml
# .cargo/config.toml
[registries.my-company]
index = "https://registry.mycompany.com/git/index"

[source.crates-io]
replace-with = "my-company"  # 可选: 替换 crates.io
```

**使用私有 registry**:

```toml
[dependencies]
internal-crate = { version = "1.0", registry = "my-company" }
```

---

## 10. Cargo 配置

### 10.1 配置文件层级

**优先级** (高到低):

1. `.cargo/config.toml` (项目级)
2. `~/.cargo/config.toml` (用户级)
3. `/etc/cargo/config.toml` (系统级)

---

### 10.2 常用配置

**完整配置示例**:

```toml
# .cargo/config.toml

[build]
target = "x86_64-unknown-linux-gnu"
rustflags = ["-C", "link-arg=-fuse-ld=lld"]
jobs = 8
incremental = true

[target.x86_64-unknown-linux-gnu]
linker = "clang"
rustflags = ["-C", "link-arg=-fuse-ld=lld"]

[target.x86_64-pc-windows-msvc]
linker = "link.exe"

[profile.dev]
opt-level = 1

[profile.release]
lto = "thin"
codegen-units = 16

[alias]
b = "build"
t = "test"
r = "run"
c = "check"
br = "build --release"

[net]
git-fetch-with-cli = true
offline = false

[http]
proxy = "http://proxy.example.com:8080"
timeout = 30

[term]
color = "always"
verbose = false
```

---

## 11. 实战案例

### 11.1 大型多 crate 项目 - 完整配置

**项目结构**:

```text
my-app/
├── Cargo.toml               # Workspace 根配置
├── Cargo.lock
├── .cargo/
│   └── config.toml          # Cargo 配置
├── crates/
│   ├── core/                # 核心库（无外部依赖）
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── lib.rs
│   ├── api/                 # API 层（依赖 core）
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── lib.rs
│   ├── db/                  # 数据库层（依赖 core）
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── lib.rs
│   ├── web/                 # Web 服务（依赖 api, db）
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── main.rs
│   └── cli/                 # CLI 工具（依赖 api）
│       ├── Cargo.toml
│       └── src/
│           └── main.rs
├── tests/                   # 集成测试
│   └── integration_test.rs
└── benches/                 # 基准测试
    └── my_bench.rs
```

**根目录 Cargo.toml（完整配置）**:

```toml
[workspace]
members = [
    "crates/*",
]
resolver = "2"  # Rust 1.51+，Edition 2024 使用 resolver = "3"

# 排除不需要作为 workspace 成员的目录
exclude = [
    "tools/scripts",
    "docs",
]

# Workspace 元数据
[workspace.package]
version = "0.1.0"
edition = "2024"
authors = ["Team <team@example.com>"]
license = "MIT OR Apache-2.0"
repository = "https://github.com/example/my-app"
rust-version = "1.93"

# Workspace 依赖 - 所有成员共享这些版本
[workspace.dependencies]
# 异步运行时
tokio = { version = "1.35", features = ["rt-multi-thread", "macros", "sync"] }
tokio-util = { version = "0.7", features = ["codec"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
anyhow = "1.0"
thiserror = "1.0"

# 日志
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }

# HTTP
axum = "0.7"
hyper = { version = "1.0", features = ["full"] }

# 数据库
sqlx = { version = "0.7", features = ["runtime-tokio", "postgres"] }

# 内部依赖（使用 path，版本由 workspace.package 管理）
my-core = { path = "crates/core" }
my-api = { path = "crates/api" }
my-db = { path = "crates/db" }

# 开发依赖
[workspace.dependencies.async-trait]
version = "0.1"

# 构建依赖
[workspace.dependencies.anyhow]
version = "1.0"
default-features = false

# 共享的编译配置
[profile.dev]
opt-level = 1          # 轻度优化，加快编译
incremental = true     # 增量编译
debug = 2              # 完整调试信息

[profile.dev.package."*"]
opt-level = 2          # 依赖包使用更高优化级别

[profile.release]
opt-level = 3          # 最大优化
lto = "thin"           # 轻量链接时优化
codegen-units = 16     # 并行代码生成单元
panic = "unwind"       # 允许捕获 panic
strip = "symbols"      # 移除符号表

[profile.release.package.my-core]
opt-level = 3          # 核心库特别优化

# 测试专用配置
[profile.test]
opt-level = 1
debug = 2

# 基准测试配置
[profile.bench]
opt-level = 3
lto = "thin"
```

**crates/core/Cargo.toml**:

```toml
[package]
name = "my-core"
version.workspace = true
edition.workspace = true
authors.workspace = true
license.workspace = true
repository.workspace = true
rust-version.workspace = true
description = "Core domain types and utilities"

[dependencies]
# 无外部依赖，只使用标准库

[dev-dependencies]
anyhow = { workspace = true }
tokio = { workspace = true }
```

**crates/core/src/lib.rs**:

```rust
//! Core domain types and utilities
//!
//! This crate provides fundamental types used throughout the application.

#![warn(missing_docs)]

use std::fmt;
use std::str::FromStr;

/// Unique identifier for entities
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Id(u64);

impl Id {
    /// Create a new ID from a raw value
    pub const fn new(value: u64) -> Self {
        Self(value)
    }

    /// Get the raw value
    pub const fn value(&self) -> u64 {
        self.0
    }
}

impl fmt::Display for Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl FromStr for Id {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse().map(Self::new)
    }
}

/// Result type alias for core operations
pub type CoreResult<T> = std::result::Result<T, CoreError>;

/// Core error type
#[derive(Debug, Clone, PartialEq)]
pub enum CoreError {
    /// Invalid input
    InvalidInput(String),
    /// Not found
    NotFound(Id),
    /// Internal error
    Internal(String),
}

impl fmt::Display for CoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CoreError::InvalidInput(msg) => write!(f, "Invalid input: {}", msg),
            CoreError::NotFound(id) => write!(f, "Not found: {}", id),
            CoreError::Internal(msg) => write!(f, "Internal error: {}", msg),
        }
    }
}

impl std::error::Error for CoreError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_id_creation() {
        let id = Id::new(42);
        assert_eq!(id.value(), 42);
    }

    #[test]
    fn test_id_parsing() {
        let id: Id = "123".parse().unwrap();
        assert_eq!(id.value(), 123);
    }
}
```

**crates/api/Cargo.toml**:

```toml
[package]
name = "my-api"
version.workspace = true
edition.workspace = true
authors.workspace = true
license.workspace = true
repository.workspace = true
rust-version.workspace = true
description = "API definitions and clients"

[dependencies]
# 内部依赖
my-core = { workspace = true }

# 外部依赖
serde = { workspace = true }
serde_json = { workspace = true }
thiserror = { workspace = true }

[dev-dependencies]
tokio = { workspace = true }
anyhow = { workspace = true }
```

**crates/api/src/lib.rs**:

```rust
//! API layer for the application
//!
//! Provides HTTP client and request/response types.

use my_core::{CoreError, CoreResult, Id};
use serde::{Deserialize, Serialize};

/// API request for creating an entity
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreateRequest {
    /// Entity name
    pub name: String,
    /// Entity data
    pub data: serde_json::Value,
}

/// API response with entity ID
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreateResponse {
    /// Created entity ID
    pub id: Id,
    /// Creation timestamp
    pub created_at: String,
}

/// API client trait
#[async_trait::async_trait]
pub trait ApiClient {
    /// Create a new entity
    async fn create(&self, req: CreateRequest) -> CoreResult<CreateResponse>;

    /// Get entity by ID
    async fn get(&self, id: Id) -> CoreResult<serde_json::Value>;

    /// Delete entity
    async fn delete(&self, id: Id) -> CoreResult<()>;
}

/// API error type
#[derive(Debug, thiserror::Error)]
pub enum ApiError {
    /// HTTP error
    #[error("HTTP error: {0}")]
    Http(String),
    /// Serialization error
    #[error("Serialization error: {0}")]
    Serialization(#[from] serde_json::Error),
    /// Core error
    #[error(transparent)]
    Core(#[from] CoreError),
}

impl From<ApiError> for CoreError {
    fn from(err: ApiError) -> Self {
        match err {
            ApiError::Http(msg) => CoreError::Internal(msg),
            ApiError::Serialization(e) => CoreError::InvalidInput(e.to_string()),
            ApiError::Core(e) => e,
        }
    }
}
```

**crates/db/Cargo.toml**:

```toml
[package]
name = "my-db"
version.workspace = true
edition.workspace = true
authors.workspace = true
license.workspace = true
repository.workspace = true
rust-version.workspace = true
description = "Database layer"

[dependencies]
# 内部依赖
my-core = { workspace = true }

# 外部依赖
sqlx = { workspace = true }
anyhow = { workspace = true }
tokio = { workspace = true }

[dev-dependencies]
# 测试使用内存数据库
sqlx = { workspace = true, features = ["sqlite"] }
```

**crates/web/Cargo.toml**:

```toml
[package]
name = "my-web"
version.workspace = true
edition.workspace = true
authors.workspace = true
license.workspace = true
repository.workspace = true
rust-version.workspace = true
description = "Web service binary"

[[bin]]
name = "my-web-server"
path = "src/main.rs"

[dependencies]
# 内部依赖
my-core = { workspace = true }
my-api = { workspace = true }
my-db = { workspace = true }

# 外部依赖
axum = { workspace = true }
tokio = { workspace = true }
tracing = { workspace = true }
tracing-subscriber = { workspace = true }
anyhow = { workspace = true }
serde = { workspace = true }
serde_json = { workspace = true }
```

**crates/web/src/main.rs**:

```rust
//! Web service entry point

use axum::{
    routing::{get, post},
    Router,
};
use std::net::SocketAddr;
use tracing::{info, Level};
use tracing_subscriber::FmtSubscriber;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // Initialize logging
    let subscriber = FmtSubscriber::builder()
        .with_max_level(Level::INFO)
        .finish();
    tracing::subscriber::set_global_default(subscriber)?;

    info!("Starting web server...");

    // Build router
    let app = Router::new()
        .route("/health", get(health_check))
        .route("/api/v1/items", post(create_item));

    // Run server
    let addr: SocketAddr = "0.0.0.0:3000".parse()?;
    info!("Listening on {}", addr);

    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;

    Ok(())
}

async fn health_check() -> &'static str {
    "OK"
}

async fn create_item(
    axum::Json(req): axum::Json<my_api::CreateRequest>,
) -> Result<axum::Json<my_api::CreateResponse>, axum::http::StatusCode> {
    // Implementation here
    todo!()
}
```

---

### 11.2 微服务架构 - 完整示例

**项目结构**:

```text
microservices/
├── Cargo.toml                    # Workspace 配置
├── Cargo.lock
├── .cargo/
│   └── config.toml
├── services/
│   ├── auth-service/             # 认证服务
│   │   ├── Cargo.toml
│   │   └── src/
│   │       ├── main.rs
│   │       └── handlers.rs
│   ├── user-service/             # 用户服务
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── main.rs
│   ├── order-service/            # 订单服务
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── main.rs
│   └── payment-service/          # 支付服务
│       ├── Cargo.toml
│       └── src/
│           └── main.rs
├── shared/                       # 共享代码
│   ├── common/                   # 通用工具
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── lib.rs
│   ├── proto/                    # gRPC 定义
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── lib.rs
│   └── models/                   # 共享数据模型
│       ├── Cargo.toml
│       └── src/
│           └── lib.rs
├── gateway/                      # API 网关
│   ├── Cargo.toml
│   └── src/
│       └── main.rs
└── deploy/                       # 部署配置
    ├── docker-compose.yml
    └── kubernetes/
```

**根目录 Cargo.toml**:

```toml
[workspace]
members = [
    "services/*",
    "shared/*",
    "gateway",
]
resolver = "3"  # Edition 2024

[workspace.package]
version = "0.1.0"
edition = "2024"
authors = ["Microservices Team <team@example.com>"]
license = "MIT"
rust-version = "1.93"

[workspace.dependencies]
# gRPC
tonic = "0.12"
tonic-health = "0.12"
prost = "0.13"

# HTTP/REST
axum = "0.7"
tower = "0.5"
tower-http = { version = "0.6", features = ["trace", "cors"] }
hyper = { version = "1.0", features = ["full"] }

# Async
tokio = { version = "1.35", features = ["rt-multi-thread", "macros", "signal"] }
tokio-util = "0.7"
async-trait = "0.1"
futures = "0.3"

# Serialization
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
prost-types = "0.13"

# Error handling
anyhow = "1.0"
thiserror = "1.0"

# Observability
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.25"
opentelemetry = "0.26"

# Configuration
config = "0.14"
dotenvy = "0.15"

# Shared crates
shared-common = { path = "shared/common" }
shared-proto = { path = "shared/proto" }
shared-models = { path = "shared/models" }

[profile.release]
opt-level = 3
lto = "thin"
codegen-units = 4  # 每个服务并行构建
strip = "symbols"
```

**services/auth-service/Cargo.toml**:

```toml
[package]
name = "auth-service"
version.workspace = true
edition.workspace = true
authors.workspace = true
license.workspace = true
rust-version.workspace = true
description = "Authentication service"

[[bin]]
name = "auth-service"
path = "src/main.rs"

[dependencies]
# Shared
shared-common = { workspace = true }
shared-proto = { workspace = true }
shared-models = { workspace = true }

# gRPC
tonic = { workspace = true }
tonic-health = { workspace = true }
prost = { workspace = true }

# Async
tokio = { workspace = true }
async-trait = { workspace = true }

# HTTP
axum = { workspace = true }
tower = { workspace = true }
tower-http = { workspace = true }

# Observability
tracing = { workspace = true }
tracing-subscriber = { workspace = true }

# Security
jsonwebtoken = "9"
bcrypt = "0.15"

[dev-dependencies]
tokio-test = "0.4"
```

**shared/models/Cargo.toml**:

```toml
[package]
name = "shared-models"
version.workspace = true
edition.workspace = true
authors.workspace = true
license.workspace = true
rust-version.workspace = true
description = "Shared data models across services"

[dependencies]
# Serialization
serde = { workspace = true }
serde_json = { workspace = true }

# Validation
validator = { version = "0.19", features = ["derive"] }

# Time
chrono = { version = "0.4", features = ["serde"] }

# ID generation
uuid = { version = "1.0", features = ["v4", "serde"] }
```

**shared/models/src/lib.rs**:

```rust
//! Shared data models across microservices

use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use uuid::Uuid;
use validator::Validate;

/// User ID type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct UserId(pub Uuid);

impl UserId {
    pub fn new() -> Self {
        Self(Uuid::new_v4())
    }
}

impl Default for UserId {
    fn default() -> Self {
        Self::new()
    }
}

/// User model
#[derive(Debug, Clone, Serialize, Deserialize, Validate)]
pub struct User {
    pub id: UserId,
    #[validate(email)]
    pub email: String,
    #[validate(length(min = 1, max = 100))]
    pub name: String,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// Order ID type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct OrderId(pub Uuid);

impl OrderId {
    pub fn new() -> Self {
        Self(Uuid::new_v4())
    }
}

/// Order model
#[derive(Debug, Clone, Serialize, Deserialize, Validate)]
pub struct Order {
    pub id: OrderId,
    pub user_id: UserId,
    pub items: Vec<OrderItem>,
    #[validate(range(min = 0.0))]
    pub total_amount: f64,
    pub status: OrderStatus,
    pub created_at: DateTime<Utc>,
}

/// Order item
#[derive(Debug, Clone, Serialize, Deserialize, Validate)]
pub struct OrderItem {
    pub product_id: String,
    #[validate(range(min = 1))]
    pub quantity: i32,
    #[validate(range(min = 0.0))]
    pub unit_price: f64,
}

/// Order status
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum OrderStatus {
    Pending,
    Confirmed,
    Shipped,
    Delivered,
    Cancelled,
}

/// Payment ID type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct PaymentId(pub Uuid);

impl PaymentId {
    pub fn new() -> Self {
        Self(Uuid::new_v4())
    }
}

/// Payment model
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Payment {
    pub id: PaymentId,
    pub order_id: OrderId,
    pub amount: f64,
    pub currency: String,
    pub status: PaymentStatus,
    pub created_at: DateTime<Utc>,
}

/// Payment status
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PaymentStatus {
    Pending,
    Completed,
    Failed,
    Refunded,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_user_creation() {
        let user = User {
            id: UserId::new(),
            email: "test@example.com".to_string(),
            name: "Test User".to_string(),
            created_at: Utc::now(),
            updated_at: Utc::now(),
        };

        assert!(user.validate().is_ok());
    }

    #[test]
    fn test_invalid_email() {
        let user = User {
            id: UserId::new(),
            email: "invalid-email".to_string(),
            name: "Test".to_string(),
            created_at: Utc::now(),
            updated_at: Utc::now(),
        };

        assert!(user.validate().is_err());
    }
}
```

---

## 12. 最佳实践

### ✅ 推荐做法

1. **使用 Workspace 依赖**: 统一版本管理
2. **Resolver 2/3**: 使用最新依赖解析器
3. **Feature 分层**: 提供 `default`, `full`, `minimal` 等预设
4. **文档化**: 在 README 说明 workspace 结构
5. **CI/CD 集成**: 测试所有 workspace 成员

### ⚠️ 常见陷阱 {#️-常见陷阱}

1. **循环依赖**: 避免 crate 之间的循环依赖
2. **过度拆分**: 不要为了拆分而拆分
3. **版本不一致**: 使用 workspace 依赖统一版本
4. **忘记发布顺序**: 按依赖顺序发布 crates

---

## 13. 故障排查

### 常见问题

**1. Workspace 成员无法找到**:

```bash
# 检查成员是否正确
cargo metadata --format-version 1 | jq '.workspace_members'

# 清理并重新构建
cargo clean
cargo build --workspace
```

**2. 依赖版本冲突**:

```bash
# 查看冲突的依赖
cargo tree -d

# 使用 workspace 依赖统一版本
```

**3. Feature 启用问题**:

```bash
# 查看最终启用的 features
cargo tree -f "{p} {f}"

# 使用 resolver 2/3
```

---

## 14. 相关资源

### 📚 官方文档 {#-官方文档}

- [Cargo Book - Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html)
- [Cargo Book - Dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html)
- [Cargo Book - Features](https://doc.rust-lang.org/cargo/reference/features.html)

### 🔗 相关文档 {#-相关文档}

- [01_compiler_features.md](./01_compiler_features.md)
- [03_rustdoc_advanced.md](./03_rustdoc_advanced.md)

### 📦 推荐工具

- **cargo-edit**: 管理依赖
- **cargo-release**: 发布管理
- **cargo-audit**: 安全审计
- **cargo-deny**: 依赖策略检查
- **cargo-workspaces**: Workspace 管理

---

**文档维护**: Documentation Team
**最后更新**: 2026-01-26
**下次审查**: 2026-01-22
**最后对照 releases.rs**: 2026-02-14
