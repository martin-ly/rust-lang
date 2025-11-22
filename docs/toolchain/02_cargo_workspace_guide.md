# Cargo 工作空间与依赖管理

> **文档版本**: Rust 1.90+ | **更新日期**: 2025-10-22
> **文档类型**: 📘 工具链参考 | **适用对象**: 中级到高级开发者

---

## 📊 目录

- [Cargo 工作空间与依赖管理](#cargo-工作空间与依赖管理)
  - [📊 目录](#-目录)
  - [🎯 文档说明](#-文档说明)
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
    - [11.1 大型多 crate 项目](#111-大型多-crate-项目)
    - [11.2 微服务架构](#112-微服务架构)
  - [12. 最佳实践](#12-最佳实践)
    - [✅ 推荐做法](#-推荐做法)
    - [⚠️ 常见陷阱](#️-常见陷阱)
  - [13. 故障排查](#13-故障排查)
    - [常见问题](#常见问题)
  - [14. 相关资源](#14-相关资源)
    - [📚 官方文档](#-官方文档)
    - [🔗 相关文档](#-相关文档)
    - [📦 推荐工具](#-推荐工具)

## 🎯 文档说明

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
# ✅ 推荐
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

### 11.1 大型多 crate 项目

**项目结构**:

```text
my-app/
├── Cargo.toml               # Workspace 配置
├── Cargo.lock
├── crates/
│   ├── core/                # 核心库
│   ├── api/                 # API 层
│   ├── db/                  # 数据库层
│   ├── web/                 # Web 服务
│   └── cli/                 # CLI 工具
├── tests/                   # 集成测试
└── benches/                 # 基准测试
```

**Cargo.toml**:

```toml
[workspace]
members = [
    "crates/*",
]
resolver = "2"

[workspace.dependencies]
# 共享依赖
tokio = { version = "1.0", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
anyhow = "1.0"

# 内部依赖
my-core = { path = "crates/core" }
my-api = { path = "crates/api" }
my-db = { path = "crates/db" }

[profile.release]
lto = "thin"
codegen-units = 16
opt-level = 3
```

---

### 11.2 微服务架构

**项目结构**:

```text
microservices/
├── Cargo.toml
├── services/
│   ├── auth-service/
│   ├── user-service/
│   ├── order-service/
│   └── payment-service/
├── shared/
│   ├── common/              # 共享代码
│   ├── proto/               # gRPC 定义
│   └── models/              # 数据模型
└── deploy/
```

**Cargo.toml**:

```toml
[workspace]
members = [
    "services/*",
    "shared/*",
]
resolver = "2"

[workspace.dependencies]
tonic = "0.10"
tokio = { version = "1.0", features = ["full"] }
shared-common = { path = "shared/common" }
shared-proto = { path = "shared/proto" }
shared-models = { path = "shared/models" }
```

---

## 12. 最佳实践

### ✅ 推荐做法

1. **使用 Workspace 依赖**: 统一版本管理
2. **Resolver 2/3**: 使用最新依赖解析器
3. **Feature 分层**: 提供 `default`, `full`, `minimal` 等预设
4. **文档化**: 在 README 说明 workspace 结构
5. **CI/CD 集成**: 测试所有 workspace 成员

### ⚠️ 常见陷阱

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

### 📚 官方文档

- [Cargo Book - Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html)
- [Cargo Book - Dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html)
- [Cargo Book - Features](https://doc.rust-lang.org/cargo/reference/features.html)

### 🔗 相关文档

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
**最后更新**: 2025-10-22
**下次审查**: 2026-01-22
