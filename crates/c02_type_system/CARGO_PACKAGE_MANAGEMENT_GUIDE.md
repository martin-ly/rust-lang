# Rust 1.90 Cargo 和包管理完整指南

## 📋 目录

- [Rust 1.90 Cargo 和包管理完整指南](#rust-190-cargo-和包管理完整指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [🔧 Cargo.toml 配置详解](#-cargotoml-配置详解)
    - [基础配置](#基础配置)
    - [依赖管理](#依赖管理)
    - [特性管理](#特性管理)
    - [构建配置](#构建配置)
  - [🏗️ 工作空间管理](#️-工作空间管理)
    - [工作空间配置](#工作空间配置)
    - [依赖继承](#依赖继承)
    - [工作空间命令](#工作空间命令)
  - [⚡ 性能优化](#-性能优化)
    - [编译优化](#编译优化)
    - [增量编译](#增量编译)
    - [缓存策略](#缓存策略)
  - [🔒 依赖管理最佳实践](#-依赖管理最佳实践)
    - [版本管理](#版本管理)
    - [特性选择](#特性选择)
    - [安全审计](#安全审计)
  - [📦 包发布指南](#-包发布指南)
    - [发布准备](#发布准备)
    - [发布流程](#发布流程)
    - [文档集成](#文档集成)
  - [🛠️ 常用命令](#️-常用命令)
    - [构建相关](#构建相关)
    - [测试相关](#测试相关)
    - [依赖管理1](#依赖管理1)
  - [🔍 故障排查](#-故障排查)
    - [常见问题](#常见问题)
      - [1. 依赖冲突](#1-依赖冲突)
      - [2. 特性不兼容](#2-特性不兼容)
      - [3. 构建缓存问题](#3-构建缓存问题)
    - [调试技巧](#调试技巧)
  - [📚 参考资料](#-参考资料)
    - [官方文档](#官方文档)
    - [工具](#工具)
    - [最佳实践](#最佳实践)

---

## 🎯 概述

Cargo 是 Rust 的包管理器和构建系统。Rust 1.90 版本带来了多项重要改进：

- **Resolver 3**: 更智能的依赖解析
- **工作空间继承**: 集中管理依赖版本
- **构建优化**: 15-20% 的构建速度提升
- **安全增强**: 改进的依赖审计
- **模块改进**: 更灵活的可见性控制

---

## 🔧 Cargo.toml 配置详解

### 基础配置

```toml
[package]
# 包名称（必需）
name = "c02_type_system"

# 版本号（必需，遵循语义化版本）
version = "0.1.0"

# Rust 版本（Rust 1.90 新增）
edition = "2024"              # Edition 2024 稳定版
resolver = "3"                # 使用 Resolver 3
rust-version = "1.90"         # 最低 Rust 版本要求

# 作者信息
authors = ["Your Name <email@example.com>"]

# 许可证
license = "MIT"

# 描述
description = "A comprehensive type system library for Rust 1.90"

# 文档和仓库
documentation = "https://docs.rs/c02_type_system"
repository = "https://github.com/username/rust-lang"
homepage = "https://example.com"
readme = "README.md"

# 分类和关键词
keywords = ["type-system", "rust", "generics", "traits"]
categories = ["development-tools", "data-structures"]

# 排除和包含文件
exclude = [
    ".github/",
    "tests/",
    "benches/",
    "examples/large_data/",
]

include = [
    "src/**/*",
    "Cargo.toml",
    "README.md",
    "LICENSE",
]
```

### 依赖管理

```toml
[dependencies]
# 工作空间继承（Rust 1.92.0 推荐）
tokio = { workspace = true }
serde = { workspace = true, optional = true }

# 路径依赖
c01_ownership_borrow_scope = { path = "../c01_ownership_borrow_scope" }

# Git 依赖
# some-crate = { git = "https://github.com/user/repo", branch = "main" }

# 版本指定
futures = "0.3"               # ^0.3.0（最新兼容版本）
# exact-version = "=1.0.0"    # 精确版本
# range-version = ">=1.0, <2.0"  # 版本范围

# 可选依赖
criterion = { version = "0.7", optional = true }

# 平台特定依赖
[target.'cfg(not(target_env = "msvc"))'.dependencies]
jemallocator = "0.5.4"

[target.'cfg(unix)'.dependencies]
# libc = "0.2"

[target.'cfg(windows)'.dependencies]
# winapi = "0.3"

# 开发依赖（仅测试和开发使用）
[dev-dependencies]
criterion = { workspace = true }
proptest = "1.0"

# 构建依赖
[build-dependencies]
# cc = "1.0"
```

### 特性管理

```toml
[features]
# 默认特性
default = ["std"]

# 标准库支持
std = []

# 无标准库支持
alloc = []

# 完整特性集
full = ["std", "async", "serde-support", "performance"]

# 异步支持（依赖于 tokio）
async = ["dep:tokio", "futures"]

# 序列化支持
serde-support = ["dep:serde", "dep:serde_json"]

# 性能优化（包含 criterion）
performance = ["dep:criterion"]

# 实验性特性
experimental = []
```

### 构建配置

```toml
# 开发配置
[profile.dev]
opt-level = 1                 # 适度优化（0-3）
debug = true                  # 包含调试信息
incremental = true            # 增量编译
overflow-checks = true        # 溢出检查

# 发布配置
[profile.release]
opt-level = 3                 # 最大优化
debug = false                 # 不包含调试信息
lto = "fat"                   # 全局链接时优化
codegen-units = 1             # 单个代码生成单元
strip = true                  # 去除符号信息
panic = "abort"               # panic 时中止

# 依赖包优化
[profile.release.package."*"]
opt-level = 2                 # 依赖包使用较低优化

# 测试配置
[profile.test]
opt-level = 1

# 基准测试配置
[profile.bench]
opt-level = 3
debug = false
```

---

## 🏗️ 工作空间管理

### 工作空间配置

```toml
# workspace Cargo.toml
[workspace]
members = [
    "crates/c01_ownership_borrow_scope",
    "crates/c02_type_system",
    "crates/c03_control_fn",
    # ... 其他成员
]

# 排除特定目录
exclude = [
    "target",
    "experiments",
]

# 使用 Resolver 3
resolver = "3"

# 工作空间级别配置
[workspace.package]
version = "0.1.0"
edition = "2024"
rust-version = "1.90"
license = "MIT"
authors = ["Your Name"]

# 工作空间级别依赖
[workspace.dependencies]
tokio = { version = "1.48", features = ["full", "rt-multi-thread"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
futures = "0.3"
criterion = "0.7"
```

### 依赖继承

```toml
# 成员 crate 的 Cargo.toml
[package]
name = "c02_type_system"
version.workspace = true      # 继承版本
edition.workspace = true      # 继承 edition
rust-version.workspace = true # 继承 rust-version
license.workspace = true      # 继承许可证

[dependencies]
# 继承工作空间依赖
tokio.workspace = true
serde = { workspace = true, optional = true }
serde_json.workspace = true
futures.workspace = true

[dev-dependencies]
criterion.workspace = true
```

### 工作空间命令

```bash
# 构建整个工作空间
cargo build --workspace

# 构建特定包
cargo build -p c02_type_system

# 测试整个工作空间
cargo test --workspace --no-fail-fast

# 测试特定包
cargo test -p c02_type_system

# 检查整个工作空间
cargo check --workspace --all-features

# 清理整个工作空间
cargo clean --workspace

# 发布特定包
cargo publish -p c02_type_system
```

---

## ⚡ 性能优化

### 编译优化

```toml
# Cargo.toml

# 开发时快速编译
[profile.dev]
opt-level = 1                 # 基础优化
incremental = true            # 增量编译
codegen-units = 256           # 并行代码生成

# 发布时最大性能
[profile.release]
opt-level = 3                 # 最大优化
lto = "fat"                   # 全局链接时优化
codegen-units = 1             # 单个代码生成单元
panic = "abort"               # 移除 panic 展开代码

# 快速发布（调试用）
[profile.release-with-debug]
inherits = "release"
debug = true
strip = false
```

### 增量编译

```bash
# 启用增量编译（默认在 dev 模式）
export CARGO_INCREMENTAL=1

# 并行编译（使用所有 CPU 核心）
cargo build -j $(nproc)

# 指定并行度
cargo build -j 4

# 使用 sccache 加速
export RUSTC_WRAPPER=sccache
cargo build
```

### 缓存策略

```bash
# 清理增量编译缓存
cargo clean -p c02_type_system --release

# 完全清理
cargo clean

# 只清理特定目标
cargo clean --target x86_64-unknown-linux-gnu

# 查看缓存大小
du -sh target/

# 使用 cargo-cache 管理缓存
cargo install cargo-cache
cargo cache --info
cargo cache --autoclean
```

---

## 🔒 依赖管理最佳实践

### 版本管理

```toml
[dependencies]
# 推荐：使用兼容版本
tokio = "1.48"                # ^1.48.0

# 精确版本（关键依赖）
critical-lib = "=2.0.0"

# 版本范围
flexible-lib = ">=1.0, <2.0"

# Git 依赖（开发时）
experimental-lib = { git = "https://github.com/user/repo", rev = "abc123" }

# 补丁替换
[patch.crates-io]
# some-crate = { path = "local-patches/some-crate" }
```

### 特性选择

```toml
[dependencies]
# 最小特性集
tokio = { version = "1.48", features = ["rt", "sync"] }

# 避免默认特性
serde = { version = "1.0", default-features = false, features = ["derive"] }

# 条件特性
[dependencies]
async-support = { version = "1.0", optional = true }

[features]
default = []
full = ["async-support"]
```

### 安全审计

```bash
# 安装 cargo-audit
cargo install cargo-audit

# 审计依赖
cargo audit

# 自动修复
cargo audit fix

# JSON 输出
cargo audit --json

# 忽略特定漏洞
# Cargo.toml
[package.metadata.cargo-audit]
ignore = ["RUSTSEC-2021-0001"]
```

---

## 📦 包发布指南

### 发布准备

```bash
# 1. 检查包内容
cargo package --list

# 2. 本地打包测试
cargo package

# 3. 验证打包的 crate
cargo package --allow-dirty
cd target/package/c02_type_system-0.1.0
cargo build
cargo test

# 4. 检查文档
cargo doc --open --no-deps

# 5. 发布前测试
cargo publish --dry-run
```

### 发布流程

```bash
# 1. 更新版本号
# 编辑 Cargo.toml 中的 version

# 2. 更新 CHANGELOG.md

# 3. 提交更改
git add Cargo.toml CHANGELOG.md
git commit -m "Release v0.1.0"
git tag v0.1.0

# 4. 发布到 crates.io
cargo publish

# 5. 推送到 Git
git push origin main --tags
```

### 文档集成

```toml
# Cargo.toml
[package]
documentation = "https://docs.rs/c02_type_system"

# 文档配置
[package.metadata.docs.rs]
all-features = true
rustdoc-args = ["--cfg", "docsrs"]
```

```rust
// src/lib.rs
#![doc = include_str!("../README.md")]
#![cfg_attr(docsrs, feature(doc_cfg))]

#[cfg_attr(docsrs, doc(cfg(feature = "async")))]
#[cfg(feature = "async")]
pub mod async_support {
    // ...
}
```

---

## 🛠️ 常用命令

### 构建相关

```bash
# 基本构建
cargo build

# 发布构建
cargo build --release

# 所有特性
cargo build --all-features

# 特定特性
cargo build --features "async,serde-support"

# 无默认特性
cargo build --no-default-features

# 检查（不生成二进制）
cargo check

# 清理
cargo clean
```

### 测试相关

```bash
# 运行所有测试
cargo test

# 运行特定测试
cargo test test_name

# 显示输出
cargo test -- --nocapture

# 并行测试
cargo test -- --test-threads=4

# 文档测试
cargo test --doc

# 基准测试
cargo bench
```

### 依赖管理1

```bash
# 更新依赖
cargo update

# 更新特定依赖
cargo update -p tokio

# 精确版本更新
cargo update --precise 1.48.0 tokio

# 依赖树
cargo tree

# 显示重复依赖
cargo tree --duplicates

# 依赖图
cargo tree --depth 2

# 检查过时依赖
cargo install cargo-outdated
cargo outdated
```

---

## 🔍 故障排查

### 常见问题

#### 1. 依赖冲突

```bash
# 问题：不同版本的同一依赖
cargo tree --duplicates

# 解决：使用 patch 统一版本
[patch.crates-io]
problematic-crate = { version = "1.0" }
```

#### 2. 特性不兼容

```bash
# 问题：特性组合导致编译失败
cargo check --no-default-features --features minimal

# 解决：调整特性依赖
[features]
default = ["std"]
minimal = []
```

#### 3. 构建缓存问题

```bash
# 清理并重建
cargo clean
rm -rf target/
cargo build
```

### 调试技巧

```bash
# 详细输出
cargo build -vv

# 显示编译命令
cargo build --verbose

# 检查宏展开
cargo expand

# 检查 MIR
cargo rustc -- -Z unstable-options --emit mir

# 性能分析
cargo build --timings

# 依赖图可视化
cargo install cargo-deps
cargo deps --all-deps | dot -Tpng > deps.png
```

---

## 📚 参考资料

### 官方文档

- [The Cargo Book](https://doc.rust-lang.org/cargo/)
- [Cargo Reference](https://doc.rust-lang.org/cargo/reference/)
- [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)

### 工具

- [cargo-audit](https://github.com/RustSec/rustsec/tree/main/cargo-audit) - 安全审计
- [cargo-outdated](https://github.com/kbknapp/cargo-outdated) - 检查过时依赖
- [cargo-tree](https://doc.rust-lang.org/cargo/commands/cargo-tree.html) - 依赖树
- [cargo-expand](https://github.com/dtolnay/cargo-expand) - 宏展开
- [cargo-cache](https://github.com/matthiaskrgr/cargo-cache) - 缓存管理

### 最佳实践

- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
- [Cargo Best Practices](https://doc.rust-lang.org/cargo/guide/best-practices.html)
- [Rust Performance Book](https://nnethercote.github.io/perf-book/)

---

**文档版本**: 1.0
**最后更新**: 2025-10-19
**适用于**: Rust 1.90+, Cargo 1.90+

*本指南持续更新中，欢迎反馈和建议！* 🦀
