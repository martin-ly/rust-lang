# Rust 工具链文档

> **文档集**: Rust 编译器、Cargo、Rustdoc  
> **更新日期**: 2025-10-22  
> **文档类型**: 📘 工具链参考

---

## 🔬 形式化理论

深入学习工具链生态系统的形式化理论基础：

- 🔧 **[工具链生态形式化理论](../../rust-formal-engineering-system/06_toolchain_ecosystem/)** - 工具链生态系统的形式化描述
- ⚙️ **[编译器形式化理论](../../rust-formal-engineering-system/06_toolchain_ecosystem/01_compiler/)** - 编译器架构的形式化模型
- 📦 **[包管理器理论](../../rust-formal-engineering-system/06_toolchain_ecosystem/02_package_manager/)** - 包管理的形式化定义
- 🏗️ **[构建工具理论](../../rust-formal-engineering-system/06_toolchain_ecosystem/03_build_tools/)** - 构建系统的形式化模型

**学习路径**: 实践文档 → 形式化理论 → 深入理解

---

## 🎯 文档说明

本目录包含 Rust 工具链的高级文档，涵盖编译器特性、构建系统、文档生成等核心工具的深入使用指南。

**目标读者**: 中级到高级 Rust 开发者

---

## 📋 文档目录

### 核心工具链文档

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

## 🆕 Rust 1.54+ 新特性

### 1. 增量编译默认启用

**特性**: Rust 1.54 默认重新启用增量编译

**影响**:

- 开发环境编译速度提升 50-90%
- 构建缓存自动管理
- 无需额外配置

**文档**: [01_compiler_features.md#2-增量编译](./01_compiler_features.md#2-增量编译-rust-154)

---

### 2. Rustdoc JSON 输出改进

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

```rust
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
```

**详细指南**: [03_rustdoc_advanced.md#2](./03_rustdoc_advanced.md#2-文档注释语法)

---

## 📊 工具链对比

### 编译器

| 特性 | Rust 1.54 之前 | Rust 1.54+ | Rust 1.90+ |
|------|---------------|-----------|-----------|
| 增量编译 | 默认禁用 | **默认启用** ✅ | 默认启用 |
| LTO | 支持 | 支持 | 支持 (改进) |
| PGO | 支持 | 支持 | 支持 (改进) |
| DWARF 5 | 实验性 | 实验性 | **稳定** ✅ |

### Cargo

| 特性 | Rust 1.64 之前 | Rust 1.64+ | Edition 2024 |
|------|---------------|-----------|-------------|
| Workspace 依赖 | ❌ | **✅** | ✅ |
| Resolver 2 | 手动配置 | 推荐 | 推荐 |
| Resolver 3 | ❌ | ❌ | **✅** |

### Rustdoc

| 特性 | Rust 1.54 之前 | Rust 1.54+ | Rust 1.90+ |
|------|---------------|-----------|-----------|
| JSON 输出 | ❌ | **✅** | ✅ (改进) |
| Intra-doc Links | ✅ | ✅ | ✅ |
| 搜索别名 | ✅ | ✅ | ✅ |

---

## 🔗 相关资源

### 内部文档

- [编译器特性](./01_compiler_features.md)
- [Cargo 工作空间](./02_cargo_workspace_guide.md)
- [Rustdoc 高级](./03_rustdoc_advanced.md)

### 官方资源

- [Rustc Book](https://doc.rust-lang.org/rustc/)
- [Cargo Book](https://doc.rust-lang.org/cargo/)
- [Rustdoc Book](https://doc.rust-lang.org/rustdoc/)

### 相关模块

- [C13 Reliability - 性能优化](../../crates/c13_reliability/docs/tier_04_advanced/)
- [C08 Algorithms - 算法优化](../../crates/c08_algorithms/docs/)

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

| 配置 | 清洁构建 | 增量构建 | 说明 |
|------|---------|---------|------|
| Dev (默认) | 5s | 1s | 快速迭代 |
| Release (基础) | 30s | 15s | 标准优化 |
| Release + LTO | 60s | 30s | 最大优化 |
| Release + PGO | 80s | - | 极致性能 |

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

### 文档生成1

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
**最后更新**: 2025-10-22  
**下次审查**: 2026-01-22
