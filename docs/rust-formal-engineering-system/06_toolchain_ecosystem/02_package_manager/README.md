# 包管理器理论

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

> 内容已整合至： [02_cargo_workspace_guide.md](../../../06_toolchain/02_cargo_workspace_guide.md)

[返回主索引](../../00_master_index.md)

---

## Cargo 核心概念

### 依赖管理

```toml
[package]
name = "my-project"
version = "0.1.0"
edition = "2024"

[dependencies]
# 语义化版本
serde = "1.0"           # >= 1.0.0, < 2.0.0
serde = "~1.0.150"      # >= 1.0.150, < 1.1.0
serde = "^1.0"          # >= 1.0.0, < 2.0.0
serde = "=1.0.150"      # 精确版本 1.0.150
serde = ">=1.0, <1.5"   # 范围

# 特性启用
serde = { version = "1.0", features = ["derive"] }
serde = { version = "1.0", default-features = false, features = ["alloc"] }

# 可选依赖
tracing = { version = "0.1", optional = true }

# 平台特定依赖
[target.'cfg(unix)'.dependencies]
nix = "0.27"

[target.'cfg(windows)'.dependencies]
windows-sys = "0.52"

# 开发依赖
[dev-dependencies]
mockall = "0.12"
tokio-test = "0.4"
```

### 工作空间

```toml
[workspace]
members = ["crate-a", "crate-b", "crate-c"]
resolver = "2"

[workspace.dependencies]
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1.35", features = ["full"] }

[workspace.package]
version = "0.1.0"
edition = "2024"
authors = ["Team"]
```

### Cargo 命令

```bash
# 项目管理
cargo new project-name
cargo init
cargo new --lib lib-name

# 构建
cargo build
cargo build --release
cargo build --all-targets
cargo check          # 快速检查
cargo fix            # 自动修复

# 测试
cargo test
cargo test --doc
cargo test --lib
cargo test <filter>

# 依赖管理
cargo add <crate>
cargo add --dev <crate>
cargo update
cargo tree
cargo tree -d        # 显示重复依赖

# 发布
cargo publish --dry-run
cargo publish
cargo yank --version x.y.z
```

## 形式化方法

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 形式化方法概述 | 形式化验证基础理论 | [../../../../research_notes/formal_methods/README.md](../../../../research_notes/formal_methods/README.md) |
| Send/Sync 形式化 | 线程安全形式化定义 | [../../../../research_notes/formal_methods/send_sync_formalization.md](../../../../research_notes/formal_methods/send_sync_formalization.md) |

## 相关研究笔记

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| Cargo 工作空间指南 | 完整工作空间配置 | [../../../06_toolchain/02_cargo_workspace_guide.md](../../../06_toolchain/02_cargo_workspace_guide.md) |
| 研究方法论 | 研究方法指南 | [../../../../research_notes/research_methodology.md](../../../../research_notes/research_methodology.md) |
| 最佳实践 | 工程最佳实践 | [../../../../research_notes/BEST_PRACTICES.md](../../../../research_notes/BEST_PRACTICES.md) |
