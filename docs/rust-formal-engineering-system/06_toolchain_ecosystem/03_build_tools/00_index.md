# 构建与脚本（Build Tools & Scripts）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [构建与脚本（Build Tools \& Scripts）索引](#构建与脚本build-tools--scripts索引)
  - [📊 目录](#-目录)
  - [💻 实际文档示例](#-实际文档示例)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [📚 推荐做法](#-推荐做法)
    - [1. Cargo 子命令（Cargo Subcommands）](#1-cargo-子命令cargo-subcommands)
    - [2. 工作区脚本（Workspace Scripts）](#2-工作区脚本workspace-scripts)
    - [3. 跨平台支持（Cross-Platform Support）](#3-跨平台支持cross-platform-support)
    - [4. 构建优化（Build Optimization）](#4-构建优化build-optimization)
  - [💻 示例](#-示例)
    - [统一构建](#统一构建)
    - [常见任务](#常见任务)
    - [Cargo Alias 配置](#cargo-alias-配置)
  - [🔗 相关条目](#-相关条目)
  - [🧭 导航](#-导航)

## 💻 实际文档示例

将构建工具形式化理论知识应用到实际文档中：

- **[编译器特性与优化](../../../../../docs/toolchain/01_compiler_features.md)** - 构建优化深入指南
  - 增量编译配置
  - LTO 和 PGO 优化
  - 并行编译和缓存优化
  - 编译时间优化策略
- **[Cargo 工作空间指南](../../../../../docs/toolchain/02_cargo_workspace_guide.md)** - 构建系统配置
  - Workspace 构建配置
  - 构建优化和 CI/CD 集成
  - 跨平台构建支持

**学习路径**: 形式化理论 → 实际文档 → 应用实践

---

## 🎯 目的

本模块统一构建脚本、任务脚本与跨平台执行方式，减少环境差异。所有内容均基于 Rust 1.91.0 和当前最佳实践。

### 核心价值

- **构建工具**: 专注于 Rust 构建工具最佳实践
- **最佳实践**: 基于 Rust 社区最新构建实践
- **完整覆盖**: 涵盖 Cargo 子命令、工作区脚本、跨平台支持等核心主题
- **易于理解**: 提供详细的构建工具说明和代码示例

## 📚 推荐做法

### 1. Cargo 子命令（Cargo Subcommands）

**推荐工具**: `cargo`, `cargo-make`, `cargo-run-script`

- **内置命令**: `cargo build`、`cargo test`、`cargo fmt`
- **自定义命令**: Cargo alias、`.cargo/config.toml`
- **第三方工具**: `cargo-make`、`cargo-run-script`
- **命令组合**: 命令链、条件执行

**相关资源**:

- [Cargo Book - Configuration](https://doc.rust-lang.org/cargo/reference/config.html)
- [cargo-make 文档](https://github.com/sagiegurari/cargo-make)
- [cargo-run-script 文档](https://docs.rs/cargo-run-script/)

### 2. 工作区脚本（Workspace Scripts）

**推荐工具**: `cargo`, `cargo-workspaces`

- **统一脚本**: 工作区级别脚本、成员脚本
- **脚本管理**: 脚本版本控制、脚本文档
- **脚本执行**: 脚本执行、错误处理
- **脚本优化**: 脚本缓存、并行执行

**相关资源**:

- [Cargo Book - Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html)
- [cargo-workspaces 文档](https://docs.rs/cargo-workspaces/)

### 3. 跨平台支持（Cross-Platform Support）

**推荐工具**: `cargo`, `cross`

- **平台差异**: Windows PowerShell、Unix Shell
- **等价命令**: 跨平台命令映射、命令文档
- **交叉编译**: `cross`、目标平台支持
- **CI/CD 集成**: GitHub Actions、GitLab CI

**相关资源**:

- [Cargo Book - Targets](https://doc.rust-lang.org/cargo/reference/cargo-targets.html)
- [cross 文档](https://github.com/cross-rs/cross)
- [Rust 1.91 ARM Windows Tier 1 支持](../01_compiler/03_arm_windows_tier1_support_rust_1_91.md)

### 4. 构建优化（Build Optimization）

**推荐工具**: `cargo`, `sccache`, `mold`

- **增量编译**: 增量编译配置、缓存优化
- **并行构建**: 并行编译、工作窃取
- **链接优化**: 链接器选择、LTO 优化
- **编译时间**: 编译时间分析、优化策略

**相关资源**:

- [Cargo Book - Profiles](https://doc.rust-lang.org/cargo/reference/profiles.html)
- [sccache 文档](https://github.com/mozilla/sccache)
- [mold 文档](https://github.com/rui314/mold)
- [编译器特性与优化](../../../../../docs/toolchain/01_compiler_features.md)

## 💻 示例

### 统一构建

```bash
# 构建所有目标
cargo build --all-targets

# 发布构建
cargo build --release

# 工作区构建
cargo build --workspace
```

### 常见任务

```bash
# 代码格式化
cargo fmt --all

# 代码检查
cargo clippy -- -D warnings

# 测试运行
cargo test --workspace

# 文档生成
cargo doc --workspace --open
```

### Cargo Alias 配置

```toml
# .cargo/config.toml
[alias]
check-all = "check --workspace --all-targets"
test-all = "test --workspace --all-targets"
lint = "clippy -- -D warnings"
```

---

## 🔗 相关条目

- **包管理**: [`../02_package_manager/00_index.md`](../02_package_manager/00_index.md)
- **测试框架**: [`../04_testing_frameworks/00_index.md`](../04_testing_frameworks/00_index.md)
- **编译器**: [`../01_compiler/00_index.md`](../01_compiler/00_index.md)

---

## 🧭 导航

- **返回工具链**: [`../00_index.md`](../00_index.md)

---

**最后更新**: 2025-11-10
**维护者**: 项目维护者
**状态**: 已完善 ✅
