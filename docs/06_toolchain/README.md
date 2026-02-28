# Rust 工具链文档

← [返回主索引](../README.md)

---

> **创建日期**: 2025-12-11
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 100% 完成
> **概念说明**: Rust 工具链是编译器（rustc）、包管理器（Cargo）、文档生成器（rustdoc）和相关工具（Clippy、rustfmt、MIRI）的集合。它们协同工作，提供从代码编写、编译、测试到部署的完整开发体验。

---

## 快速开始

```bash
# 创建新项目
cargo new my_project
cd my_project

# 构建项目
cargo build
cargo build --release

# 运行测试
cargo test

# 检查代码
cargo check
cargo clippy

# 格式化代码
cargo fmt

# 生成文档
cargo doc --open
```

```toml
# Cargo.toml 配置示例
[package]
name = "my-project"
version = "0.1.0"
edition = "2024"
rust-version = "1.93"

[dependencies]
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1.35", features = ["full"] }

[profile.release]
opt-level = 3
lto = true
```

---

## 🔬 形式化理论

深入学习工具链生态系统的形式化理论基础：

- 🔧 **[工具链生态形式化理论](../rust-formal-engineering-system/06_toolchain_ecosystem/README.md)** - 工具链生态系统的形式化描述
- ⚙️ **[编译器形式化理论](../rust-formal-engineering-system/06_toolchain_ecosystem/01_compiler/README.md)** - 编译器架构的形式化模型
- 📦 **[包管理器理论](../rust-formal-engineering-system/06_toolchain_ecosystem/02_package_manager/README.md)** - 包管理的形式化定义
- 🏗️ **[构建工具理论](../rust-formal-engineering-system/06_toolchain_ecosystem/03_build_tools/README.md)** - 构建系统的形式化模型

**学习路径**: 实践文档 → 形式化理论 → 深入理解

---

## 🎯 文档说明

本目录包含 Rust 工具链的高级文档，涵盖编译器特性、构建系统、文档生成等核心工具的深入使用指南。

**目标读者**: 中级到高级 Rust 开发者

---

## 📋 文档目录

### 核心工具链文档

#### 0. [Rust 2024 Edition 学习影响](./00_rust_2024_edition_learning_impact.md) 🆕

**涵盖内容**:

- ✅ **Edition 2024 概览**：RPIT、`if let` 临时作用域、`unsafe_op_in_unsafe_fn` 等
- ✅ **对 C01–C11 学习路径的影响**：所有权、类型系统、控制流、宏
- ✅ **迁移与学习建议**

**适用场景**: 理解 2024 Edition 对学习的影响；从 2021 迁移

#### 1. [编译器特性与优化](./01_compiler_features.md)

**涵盖内容**:

- ✅ **增量编译** (Rust 1.54+)
- ✅ **优化级别** (O0-O3, Os, Oz)
- ✅ **Link-Time Optimization** (LTO)
- ✅ **Profile-Guided Optimization** (PGO)
- ✅ **代码生成选项** (target-cpu, target-feature)
- ✅ **调试信息** (DWARF, split-debuginfo)
- ✅ **编译缓存** (sccache)

**适用场景**:

- 性能优化
- 编译时间优化
- 生产环境配置
- 调试和 profiling

#### 2. [Cargo 工作空间与依赖管理](./02_cargo_workspace_guide.md)

**涵盖内容**:

- ✅ **Workspace 配置**
- ✅ **Workspace 依赖** (Rust 1.64+)
- ✅ **Resolver 3** (Edition 2024)
- ✅ **Feature 管理**
- ✅ **依赖图分析**
- ✅ **私有 Registry**

**适用场景**:

- 多 crate 项目管理
- 依赖版本统一
- 大型项目架构
- CI/CD 集成

#### 3. [Rustdoc 高级功能](./03_rustdoc_advanced.md)

**涵盖内容**:

- ✅ **文档注释语法**
- ✅ **文档测试** (Doc Tests)
- ✅ **Intra-doc Links**
- ✅ **JSON 输出** (Rust 1.54+)
- ✅ **主题定制**
- ✅ **CI/CD 集成**

**适用场景**:

- API 文档编写
- 文档自动化
- 文档质量提升
- 文档部署

#### 4. [Rust 1.91 vs 1.90 全面对比分析（对齐官方发布说明）](./04_rust_1.91_vs_1.90_comparison.md)

**涵盖内容（以权威来源为准）**:

- ✅ **LLD 默认链接器（1.90）**：`x86_64-unknown-linux-gnu` 默认改用 LLD（含 opt-out）
- ✅ **Cargo 工作区发布（1.90）**：`cargo publish --workspace`
- ✅ **平台支持变更**：`x86_64-apple-darwin` 降级（1.90）与 `aarch64-pc-windows-msvc` 升级（1.91）
- ✅ **新的 lint（1.91）**：`dangling_pointers_from_locals`（warn-by-default）
- ✅ **验证建议**：工作区 `check/test/doc-test` 的最小验证命令集

#### 5. [Rust 1.93 vs 1.92 全面对比分析](./05_rust_1.93_vs_1.92_comparison.md) 🆕

**涵盖内容**:

- ✅ **musl 1.2.5 更新** (DNS 解析器改进)
- ✅ **全局分配器增强** (线程本地存储支持)
- ✅ **内联汇编改进** (`cfg` 属性支持)
- ✅ **标准库 API 稳定化** (MaybeUninit、集合类型、整数操作等)
- ✅ **工具链更新** (Cargo、Clippy、Rustfmt)
- ✅ **实际应用示例** (代码示例、迁移指南)

**适用场景**:

- 版本升级评估
- 新特性学习
- 性能优化参考
- 迁移规划

---

## 🔍 快速导航

### 按主题分类

#### 性能优化

- [编译器优化](./01_compiler_features.md#3-优化级别)
- [LTO](./01_compiler_features.md#4-link-time-optimization-lto)
- [PGO](./01_compiler_features.md#5-profile-guided-optimization-pgo)
- [代码生成优化](./01_compiler_features.md#6-代码生成选项)

#### 构建系统

- [Workspace 管理](./02_cargo_workspace_guide.md#2-创建和配置-workspace)
- [依赖管理](./02_cargo_workspace_guide.md#3-依赖管理)
- [Feature 管理](./02_cargo_workspace_guide.md#5-feature-管理)
- [构建优化](./02_cargo_workspace_guide.md#7-构建优化)

#### 文档生成

- [文档注释](./03_rustdoc_advanced.md#2-文档注释语法)
- [文档测试](./03_rustdoc_advanced.md#3-文档测试-doc-tests)
- [文档链接](./03_rustdoc_advanced.md#4-文档链接)
- [文档定制](./03_rustdoc_advanced.md#7-主题与定制)

---

## 🆕 Rust 版本新特性

### Rust 1.93 主要改进 🆕

**版本**: Rust 1.93.1 (2026-02-12，补丁版；功能版 1.93.0 于 2026-01-22 发布)

**主要改进**:

- **musl 1.2.5 更新**: 改进 DNS 解析器可靠性，特别是大型 DNS 记录
- **全局分配器增强**: 支持线程本地存储，允许使用 `thread_local!` 和 `std::thread::current`
- **内联汇编改进**: `cfg` 属性可以在 `asm!` 的单个语句上使用
- **大量 API 稳定化**: MaybeUninit、String、Vec、整数操作、VecDeque、Duration、char、fmt 等
- **平台支持**: 以 rustc 平台支持页与 GitHub release tag 为准（release post 未将平台 tier 变更作为重点列出）

**文档**: [05_rust_1.93_vs_1.92_comparison.md](./05_rust_1.93_vs_1.92_comparison.md)

#### 6. [Rust 1.93 兼容性注意事项](./06_rust_1.93_compatibility_notes.md) 🆕

**涵盖内容**:

- ✅ **破坏性变更**: deref_nullptr deny 升级、#[test] 无效位置报错、offset_of! 类型检查、rustdoc 文档属性校验
- ✅ **未来不兼容警告**: ... 可变参数、repr(C) enum discriminant、repr(transparent)
- ✅ **平台变更**: Emscripten unwinding ABI、musl 1.2.5
- ✅ **Cargo 变更**: CARGO_CFG_DEBUG_ASSERTIONS、cargo publish、static-init 兼容性

**适用场景**:

- 升级到 Rust 1.93 前的兼容性检查
- 迁移问题排查

#### 7. [Rust 1.93 兼容性深度解析](./09_rust_1.93_compatibility_deep_dive.md) 🆕

**涵盖内容**:

- ✅ **pin_v2** 内置属性
- ✅ **Emscripten unwinding ABI** 变更
- ✅ **#[test]** 属性严格化
- ✅ **offset_of!** 类型检查
- ✅ **deref_nullptr** deny-by-default
- ✅ **... 可变参数** future-incompat
- ✅ **repr(C) enum** 判别值警告
- ✅ **repr(transparent)** 忽略 repr(C) 警告

**适用场景**:

- 深入理解 1.93 兼容性变更
- 迁移问题根因分析

---

### Rust 1.91 主要改进

**版本**: Rust 1.91.0 (2025-10-30)

**主要改进（对齐官方发布说明）**:

- **平台支持**: `aarch64-pc-windows-msvc` 升级为 Tier 1
- **新的 lint**: `dangling_pointers_from_locals`（warn-by-default）
- **稳定 API**: 以 release notes 的 “Stabilized APIs” 列表为准
- **与 1.90 的关键差异**: 1.90 引入 LLD 默认链接器与 `cargo publish --workspace`

**文档**: [04_rust_1.91_vs_1.90_comparison.md](./04_rust_1.91_vs_1.90_comparison.md)

---

### Rust 1.54+ 新特性

#### 1. 增量编译默认启用

**特性**: Rust 1.54 默认重新启用增量编译

**影响**:

- 开发环境编译速度提升 50-90%
- 构建缓存自动管理
- 无需额外配置

**文档**: [01_compiler_features.md#2-增量编译](./01_compiler_features.md#2-增量编译-rust-154)

---

#### 2. Rustdoc JSON 输出改进

**特性**: 改进的 JSON 格式文档输出

**用途**:

- 自定义文档工具
- API 索引生成
- 文档分析

**文档**: [03_rustdoc_advanced.md#6-json-输出](./03_rustdoc_advanced.md#6-json-输出-rust-154)

---

## 🚀 快速开始

### 生产环境优化配置

```toml
# Cargo.toml
[profile.release]
opt-level = 3
lto = "fat"
codegen-units = 1
panic = "abort"
strip = true
```

**详细指南**: [01_compiler_features.md#12.1](./01_compiler_features.md#121-生产环境优化配置)

---

### 创建 Workspace 项目

```toml
# 根 Cargo.toml
[workspace]
members = ["crate-a", "crate-b"]
resolver = "2"

[workspace.dependencies]
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1.0", features = ["full"] }
```

**详细指南**: [02_cargo_workspace_guide.md#2](./02_cargo_workspace_guide.md#2-创建和配置-workspace)

---

### 编写高质量文档

````rust
/// 函数说明
///
/// # Examples
///
/// ```
/// use my_crate::function;
/// assert_eq!(function(2, 3), 5);
/// ```
///
/// # Errors
///
/// 此函数可能返回错误...
///
/// # Panics
///
/// 此函数在以下情况下 panic...
pub fn function(a: i32, b: i32) -> i32 {
    a + b
}
````

**详细指南**: [03_rustdoc_advanced.md#2](./03_rustdoc_advanced.md#2-文档注释语法)

---

## 📊 工具链对比

本节只列出**官方 release post 明确强调**的差异（避免把“推测/通用经验”写成版本事实）。其余细节请以官方详细 release notes 为准。

| 变化                                               | 首次出现  | 权威来源                                                                                                                                                         |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `cargo publish --workspace`                        | Rust 1.90 | [Rust 1.90.0](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)                                                                                                |
| `aarch64-pc-windows-msvc` → Tier 1                 | Rust 1.91 | [Rust 1.91.0](https://blog.rust-lang.org/2025/10/30/Rust-1.91.0/)；[PR #145682](https://github.com/rust-lang/rust/pull/145682)                                   |
| `dangling_pointers_from_locals`（warn-by-default） | Rust 1.91 | [Rust 1.91.0](https://blog.rust-lang.org/2025/10/30/Rust-1.91.0/)；[warn-by-default lints](https://doc.rust-lang.org/rustc/lints/listing/warn-by-default.html)   |
| musl 1.2.5                                         | Rust 1.93 | [Rust 1.93.0](https://blog.rust-lang.org/2026/01/22/Rust-1.93.0/)                                                                                                |
| `cfg` 属性可用于单个 `asm!` 语句                   | Rust 1.93 | [Rust 1.93.0](https://blog.rust-lang.org/2026/01/22/Rust-1.93.0/)                                                                                                |
| 1.93.1 补丁（ICE/Clippy/WASM 回归修复）           | Rust 1.93.1 | [Rust 1.93.1](https://blog.rust-lang.org/2026/02/12/Rust-1.93.1/)                                                                                                |

---

## 🔗 相关资源

### 内部文档

- [Rust 2024 Edition 学习影响](./00_rust_2024_edition_learning_impact.md) 🆕
- [编译器特性](./01_compiler_features.md)
- [Cargo 工作空间](./02_cargo_workspace_guide.md)
- [Rustdoc 高级](./03_rustdoc_advanced.md)
- [Rust 1.91 vs 1.90 对比分析（对齐官方发布说明）](./04_rust_1.91_vs_1.90_comparison.md)
- [Rust 1.93 vs 1.92 对比分析](./05_rust_1.93_vs_1.92_comparison.md) 🆕
- [Rust 1.93 兼容性注意事项](./06_rust_1.93_compatibility_notes.md) 🆕
- [Rust 1.93 完整变更清单](./07_rust_1.93_full_changelog.md) 🆕
- [Rust 版本演进链 1.89–1.93](./08_rust_version_evolution_1.89_to_1.93.md) 🆕
- [Rust 1.93 兼容性深度解析](./09_rust_1.93_compatibility_deep_dive.md) 🆕
- [Rust 1.89→1.93 累积特性总览](./10_rust_1.89_to_1.93_cumulative_features_overview.md) 🆕
- [Rust 1.93 Cargo 与 Rustdoc 变更详解](./11_rust_1.93_cargo_rustdoc_changes.md) 🆕
- [Rust 1.93.1 vs 1.93.0 补丁版本对比](./12_rust_1.93.1_vs_1.93.0_comparison.md) 🆕
- [Rust 1.93 语言特性全面分析（92 项设计论证）](../research_notes/RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) 🆕

### 官方资源

- [Rustc Book](https://doc.rust-lang.org/rustc/)
- [Cargo Book](https://doc.rust-lang.org/cargo/)
- [Rustdoc Book](https://doc.rust-lang.org/rustdoc/)

### 相关模块

- [C08 Algorithms - 算法优化](../../crates/c08_algorithms/docs/)
- **注意**: 当前项目包含 c01-c12 共 12 个学习模块

---

## 💡 最佳实践

### 开发环境

```toml
[profile.dev]
opt-level = 1          # 轻度优化
incremental = true     # 增量编译
debug = 2              # 完整调试信息
```

### 生产环境

```toml
[profile.release]
opt-level = 3          # 最大优化
lto = "fat"           # Fat LTO
codegen-units = 1      # 单一代码生成单元
strip = true          # 移除符号表
```

### Workspace 管理

```toml
[workspace.dependencies]
# 统一管理依赖版本
serde = { version = "1.0", features = ["derive"] }

[workspace]
resolver = "2"  # 使用 Resolver 2
```

---

## ⚠️ 常见陷阱

### 1. 编译时间过长

**问题**: Fat LTO 导致编译时间过长

**解决**:

- 开发环境使用 `lto = false`
- CI 环境使用 `lto = "thin"`
- 生产环境使用 `lto = "fat"`

**参考**: [01_compiler_features.md#4.3](./01_compiler_features.md#43-性能权衡)

---

### 2. 依赖版本冲突

**问题**: 不同 crate 使用不同版本的依赖

**解决**: 使用 Workspace 依赖统一版本

```toml
[workspace.dependencies]
tokio = { version = "1.0", features = ["full"] }
```

**参考**: [02_cargo_workspace_guide.md#3.3](./02_cargo_workspace_guide.md#33-依赖版本统一)

---

### 3. 文档链接失效

**问题**: Intra-doc links 断开

**解决**: 使用 `cargo rustdoc -- -D rustdoc::broken-intra-doc-links` 检查

**参考**: [03_rustdoc_advanced.md#14](./03_rustdoc_advanced.md#14-故障排查)

---

## 📈 性能基准

### 编译时间对比

| 配置           | 清洁构建 | 增量构建 | 说明     |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| Release (基础) | 30s      | 15s      | 标准优化 |
| Release + LTO  | 60s      | 30s      | 最大优化 |
| Release + PGO  | 80s      | -        | 极致性能 |

**数据来源**: [01_compiler_features.md#13](./01_compiler_features.md#13-性能基准)

---

## 🛠️ 推荐工具

### 编译相关

- **sccache**: 编译缓存
- **cargo-bloat**: 分析二进制大小
- **cargo-llvm-lines**: 分析 LLVM IR
- **cargo-asm**: 查看汇编代码

### 依赖管理

- **cargo-edit**: 管理依赖
- **cargo-audit**: 安全审计
- **cargo-deny**: 依赖策略检查
- **cargo-tree**: 依赖树可视化

### 文档生成工具

- **mdBook**: 书籍格式文档
- **cargo-readme**: 生成 README
- **cargo-deadlinks**: 检查死链接

---

## 🎯 学习路径

### 初学者

1. 了解基础编译流程
2. 学习 Cargo 基础命令
3. 编写基础文档注释

**推荐**: 先阅读每个文档的"概览"和"基础用法"部分

### 中级开发者

1. 配置编译优化
2. 管理 Workspace 项目
3. 使用文档测试

**推荐**: 深入阅读"优化"和"高级特性"章节

### 高级开发者

1. 实施 PGO
2. 自定义构建流程
3. 构建文档工具

**推荐**: 阅读"高级技术"和"实战案例"章节

---

**文档维护**: Documentation Team
**最后更新**: 2026-02-20
**下次审查**: 2026-04-26
**最后对照 releases.rs**: 2026-02-20
