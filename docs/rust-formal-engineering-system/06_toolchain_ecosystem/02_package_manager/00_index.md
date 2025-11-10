# 包管理与工作区（Package Manager & Workspace）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [包管理与工作区（Package Manager \& Workspace）索引](#包管理与工作区package-manager--workspace索引)
  - [📊 目录](#-目录)
  - [💻 实际文档示例](#-实际文档示例)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [📚 核心主题](#-核心主题)
    - [1. 工作区管理（Workspace Management）](#1-工作区管理workspace-management)
    - [2. 依赖治理（Dependency Governance）](#2-依赖治理dependency-governance)
    - [3. 特性管理（Feature Management）](#3-特性管理feature-management)
    - [4. 发布流程（Publishing Process）](#4-发布流程publishing-process)
  - [💻 常用命令](#-常用命令)
    - [工作区管理](#工作区管理)
    - [依赖管理](#依赖管理)
    - [特性管理](#特性管理)
    - [发布流程](#发布流程)
  - [🔗 相关条目](#-相关条目)
  - [🧭 导航](#-导航)

## 💻 实际文档示例

将包管理器形式化理论知识应用到实际文档中：

- **[Cargo 工作空间指南](../../../../../docs/toolchain/02_cargo_workspace_guide.md)** - 完整的 Cargo 使用指南
  - Workspace 配置和管理
  - 依赖版本统一和治理
  - Feature 管理和条件编译
  - 构建优化和 CI/CD 集成
  - 私有 Registry 和发布流程

**学习路径**: 形式化理论 → 实际文档 → 应用实践

---

## 🎯 目的

本模块统一 `cargo` 包管理、工作区与依赖治理的最佳实践入口，衔接构建工具、测试框架与质量保障的规范导航。所有内容均基于 Rust 1.91.0 和当前最佳实践。

### 核心价值

- **包管理**: 专注于 Cargo 包管理最佳实践
- **最佳实践**: 基于 Rust 社区最新包管理实践
- **完整覆盖**: 涵盖工作区、依赖、特性、发布等核心主题
- **易于理解**: 提供详细的包管理说明和代码示例

## 📚 核心主题

### 1. 工作区管理（Workspace Management）

**推荐工具**: `cargo`, `cargo-workspaces`

- **Cargo.toml workspace**: 工作区配置、成员选择
- **成员选择**: `default-members`、成员过滤
- **工作区脚本**: 统一构建、测试、发布流程
- **依赖统一**: 工作区依赖版本统一管理

**相关资源**:

- [Cargo Book - Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html)
- [cargo-workspaces 文档](https://docs.rs/cargo-workspaces/)
- [Cargo 工作空间指南](../../../../../docs/toolchain/02_cargo_workspace_guide.md)

### 2. 依赖治理（Dependency Governance）

**推荐工具**: `cargo`, `cargo-audit`, `cargo-deny`, `cargo-tree`

- **版本范围**: 语义化版本、版本约束
- **依赖更新**: `cargo update -p`、选择性更新
- **依赖补丁**: `patch`、`replace`、本地开发
- **镜像配置**: 国内镜像、私有 Registry

**相关资源**:

- [Cargo Book - Dependencies](https://doc.rust-lang.org/cargo/reference/dependencies.html)
- [cargo-audit 文档](https://docs.rs/cargo-audit/)
- [cargo-deny 文档](https://docs.rs/cargo-deny/)

### 3. 特性管理（Feature Management）

**推荐工具**: `cargo`, `cargo-feature`

- **特性定义**: `features`、`default`、可选依赖
- **编译矩阵**: 特性组合、条件编译
- **特性测试**: 特性测试、文档测试
- **特性文档**: 特性文档、使用说明

**相关资源**:

- [Cargo Book - Features](https://doc.rust-lang.org/cargo/reference/features.html)
- [cargo-feature 文档](https://docs.rs/cargo-feature/)

### 4. 发布流程（Publishing Process）

**推荐工具**: `cargo`, `cargo-publish`, `cargo-release`

- **发布准备**: `cargo publish`、pre-release 检查
- **版本管理**: 语义化版本、版本号管理
- **发布检查**: `cargo deny`、安全检查
- **Registry 配置**: crates.io、私有 Registry

**相关资源**:

- [Cargo Book - Publishing](https://doc.rust-lang.org/cargo/reference/publishing.html)
- [cargo-release 文档](https://docs.rs/cargo-release/)

## 💻 常用命令

### 工作区管理

```bash
# 工作区内构建/测试/基准
cargo build --workspace
cargo test --workspace
cargo bench --workspace --no-run

# 特定成员构建
cargo build -p <package>
cargo test -p <package>
```

### 依赖管理

```bash
# 依赖树查看
cargo tree -p <crate>
cargo tree --depth 1

# 依赖更新
cargo update -p <crate>@<version>
cargo update --workspace

# 依赖审计
cargo audit
cargo deny check
```

### 特性管理

```bash
# 特性测试
cargo test --features <feature>
cargo build --no-default-features

# 特性文档
cargo doc --features <feature>
```

### 发布流程

```bash
# 发布检查
cargo publish --dry-run
cargo publish

# 版本管理
cargo release patch
cargo release minor
cargo release major
```

---

## 🔗 相关条目

- **构建工具**: [`../03_build_tools/00_index.md`](../03_build_tools/00_index.md)
- **测试框架**: [`../04_testing_frameworks/00_index.md`](../04_testing_frameworks/00_index.md)
- **代码分析**: [`../05_code_analysis/00_index.md`](../05_code_analysis/00_index.md)

---

## 🧭 导航

- **返回工具链**: [`../00_index.md`](../00_index.md)
- **质量保障**: [`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

---

**最后更新**: 2025-11-10
**维护者**: 项目维护者
**状态**: 已完善 ✅
