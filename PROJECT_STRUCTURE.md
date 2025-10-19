# 📁 项目结构说明 (Project Structure)

> **文档定位**: 详细解释项目的目录结构和组织方式  
> **使用方式**: 了解项目布局，快速定位所需文件  
> **相关文档**: [README](./README.md) | [贡献指南](./CONTRIBUTING.md)

**最后更新**: 2025-10-19  
**项目版本**: v1.0

---

## 📋 目录

- [📁 项目结构说明 (Project Structure)](#-项目结构说明-project-structure)
  - [📋 目录](#-目录)
  - [项目总览](#项目总览)
    - [目录树概览](#目录树概览)
  - [根目录文件](#根目录文件)
    - [核心文档](#核心文档)
      - [README.md](#readmemd)
      - [CONTRIBUTING.md](#contributingmd)
      - [LEARNING\_CHECKLIST.md](#learning_checklistmd)
      - [QUICK\_REFERENCE.md](#quick_referencemd)
      - [ROADMAP.md](#roadmapmd)
      - [CHANGELOG.md](#changelogmd)
      - [TROUBLESHOOTING.md](#troubleshootingmd)
      - [BEST\_PRACTICES.md](#best_practicesmd)
      - [RESOURCES.md](#resourcesmd)
      - [PROJECT\_STRUCTURE.md](#project_structuremd)
    - [配置文件](#配置文件)
      - [Cargo.toml](#cargotoml)
      - [Cargo.lock](#cargolock)
      - [rustfmt.toml](#rustfmttoml)
      - [clippy.toml](#clippytoml)
  - [文档目录](#文档目录)
    - [docs/](#docs)
      - [formal\_rust/](#formal_rust)
      - [language/](#language)
      - [ref/](#ref)
  - [模块目录](#模块目录)
    - [crates/](#crates)
    - [模块结构](#模块结构)
    - [模块详解](#模块详解)
      - [C01 - 所有权与借用 (c01\_ownership\_borrow\_scope/)](#c01---所有权与借用-c01_ownership_borrow_scope)
      - [C02 - 类型系统 (c02\_type\_system/)](#c02---类型系统-c02_type_system)
      - [C03 - 控制流与函数 (c03\_control\_fn/)](#c03---控制流与函数-c03_control_fn)
      - [C04 - 泛型编程 (c04\_generic/)](#c04---泛型编程-c04_generic)
      - [C05 - 线程与并发 (c05\_threads/)](#c05---线程与并发-c05_threads)
      - [C06 - 异步编程 (c06\_async/)](#c06---异步编程-c06_async)
      - [C07 - 进程管理 (c07\_process/)](#c07---进程管理-c07_process)
      - [C08 - 算法与数据结构 (c08\_algorithms/)](#c08---算法与数据结构-c08_algorithms)
      - [C09 - 设计模式 (c09\_design\_pattern/)](#c09---设计模式-c09_design_pattern)
      - [C10 - 网络编程 (c10\_networks/)](#c10---网络编程-c10_networks)
      - [C11 - 中间件集成 (c11\_middlewares/)](#c11---中间件集成-c11_middlewares)
      - [C12 - 模型与架构 (c12\_model/)](#c12---模型与架构-c12_model)
      - [C13 - 可靠性框架 (c13\_reliability/)](#c13---可靠性框架-c13_reliability)
  - [脚本目录](#脚本目录)
    - [scripts/](#scripts)
      - [主要脚本](#主要脚本)
        - [dev-setup.sh / dev-setup.ps1](#dev-setupsh--dev-setupps1)
        - [ci/ 目录](#ci-目录)
        - [observability/ 目录](#observability-目录)
  - [工具配置](#工具配置)
    - [Rust 工具配置](#rust-工具配置)
      - [rustfmt 配置示例](#rustfmt-配置示例)
      - [clippy 配置示例](#clippy-配置示例)
      - [deny.toml](#denytoml)
      - [tarpaulin.toml](#tarpaulintoml)
  - [导航指南](#导航指南)
    - [🎯 我想](#-我想)
      - [学习 Rust](#学习-rust)
      - [查找资料](#查找资料)
      - [解决问题](#解决问题)
      - [提升代码质量](#提升代码质量)
      - [参与贡献](#参与贡献)
  - [📊 项目统计](#-项目统计)
    - [文档规模](#文档规模)
    - [代码规模](#代码规模)
    - [内容覆盖](#内容覆盖)
  - [🔗 相关文档](#-相关文档)

---

## 项目总览

本项目是一个全面的 Rust 学习资源集合，采用 Cargo Workspace 组织多个学习模块。

### 目录树概览

```text
rust-lang/
├── README.md                    # 项目主入口
├── CONTRIBUTING.md              # 贡献指南
├── LEARNING_CHECKLIST.md        # 学习检查清单
├── QUICK_REFERENCE.md           # 快速参考手册
├── ROADMAP.md                   # 项目路线图
├── CHANGELOG.md                 # 更新日志
├── TROUBLESHOOTING.md           # 故障排查指南
├── BEST_PRACTICES.md            # 最佳实践
├── RESOURCES.md                 # 学习资源大全
├── PROJECT_STRUCTURE.md         # 本文档
├── Cargo.toml                   # 工作空间配置
├── Cargo.lock                   # 依赖锁定
├── crates/                      # 学习模块
│   ├── c01_ownership_borrow_scope/   # 所有权与借用
│   ├── c02_type_system/              # 类型系统
│   ├── c03_control_fn/               # 控制流与函数
│   ├── c04_generic/                  # 泛型编程
│   ├── c05_threads/                  # 线程与并发
│   ├── c06_async/                    # 异步编程
│   ├── c07_process/                  # 进程管理
│   ├── c08_algorithms/               # 算法与数据结构
│   ├── c09_design_pattern/           # 设计模式
│   ├── c10_networks/                 # 网络编程
│   ├── c11_middlewares/              # 中间件集成
│   ├── c12_model/                    # 模型与架构
│   └── c13_reliability/              # 可靠性框架
├── docs/                        # 深度文档
│   ├── formal_rust/             # 形式化 Rust
│   ├── language/                # 语言特性详解
│   └── ref/                     # 参考文档
├── scripts/                     # 自动化脚本
│   ├── ci/                      # CI/CD 脚本
│   └── observability/           # 可观测性脚本
├── tests/                       # 集成测试
│   ├── common/                  # 公共测试代码
│   ├── documentation/           # 文档测试
│   ├── integration/             # 集成测试
│   └── performance/             # 性能测试
└── templates/                   # 项目模板
    ├── basic-library/           # 基础库模板
    ├── cli-app/                 # CLI 应用模板
    └── web-app/                 # Web 应用模板
```

---

## 根目录文件

### 核心文档

#### README.md

- **用途**: 项目总览和入口文档
- **包含**:
  - 项目介绍和定位
  - 快速开始指南
  - 3 套完整学习路径
  - 模块导航和统计
- **何时查看**: 第一次了解项目时

#### CONTRIBUTING.md

- **用途**: 贡献指南
- **包含**:
  - 贡献流程（10 步）
  - 代码规范
  - 文档规范
  - 提交规范
  - Issue/PR 模板
- **何时查看**: 想要贡献代码或文档时

#### LEARNING_CHECKLIST.md

- **用途**: 学习进度追踪
- **包含**:
  - 200+ 学习任务
  - 4 个学习阶段
  - 交互式复选框
  - 学习建议和策略
- **何时查看**: 系统学习 Rust 时

#### QUICK_REFERENCE.md

- **用途**: 快速查询手册
- **包含**:
  - 核心语法速查
  - 650+ 代码示例
  - 10 个主题分类
  - 常用模式汇总
- **何时查看**: 需要快速查找语法时

#### ROADMAP.md

- **用途**: 项目路线图
- **包含**:
  - 短/中/长期规划
  - 版本计划（v1.1-v3.0）
  - 功能优先级
  - 社区参与机制
- **何时查看**: 了解项目未来方向时

#### CHANGELOG.md

- **用途**: 版本历史
- **包含**:
  - 版本更新记录
  - 详细变更说明
  - 统计数据
- **何时查看**: 查看版本变更时

#### TROUBLESHOOTING.md

- **用途**: 故障排查指南
- **包含**:
  - 50+ 常见问题
  - 编译/运行时错误
  - 性能问题诊断
  - 工具链问题
- **何时查看**: 遇到错误或问题时

#### BEST_PRACTICES.md

- **用途**: 最佳实践指南
- **包含**:
  - 100+ 实践示例
  - 代码风格规范
  - 性能优化技巧
  - ✅/❌ 对比示例
- **何时查看**: 提升代码质量时

#### RESOURCES.md

- **用途**: 学习资源大全
- **包含**:
  - 官方资源汇总
  - 在线教程推荐
  - 视频课程列表
  - 书籍推荐
  - 工具推荐
- **何时查看**: 寻找学习资源时

#### PROJECT_STRUCTURE.md

- **用途**: 项目结构说明（本文档）
- **包含**:
  - 目录结构详解
  - 文件用途说明
  - 导航指南
- **何时查看**: 了解项目组织时

### 配置文件

#### Cargo.toml

- **用途**: Cargo Workspace 配置
- **包含**:
  - workspace 成员列表
  - 共享依赖配置
  - 全局设置

```toml
[workspace]
members = [
    "crates/c01_ownership_borrow_scope",
    "crates/c02_type_system",
    # ... 其他模块
]

[workspace.dependencies]
# 共享依赖版本
```

#### Cargo.lock

- **用途**: 依赖版本锁定
- **说明**: 自动生成，不应手动编辑
- **版本控制**: 应提交到 Git

#### rustfmt.toml

- **用途**: 代码格式化配置
- **使用**: `cargo fmt` 自动应用

```toml
edition = "2021"
max_width = 100
tab_spaces = 4
```

#### clippy.toml

- **用途**: Clippy linter 配置
- **使用**: `cargo clippy` 应用规则

---

## 文档目录

### docs/

深度文档和参考资料目录。

#### formal_rust/

- **内容**: 形式化 Rust 文档
- **文件数**: 3500+ 个 Markdown 文件
- **主题**:
  - 类型理论
  - 形式化验证
  - 语义分析
  - 安全证明

#### language/

- **内容**: 语言特性详细解释
- **文件数**: 400+ 个文件
- **组织**: 按语言特性分类
- **用途**: 深入理解语言机制

#### ref/

- **内容**: 参考文档
- **文件数**: 860+ 个文件
- **内容**: 标准库文档、RFC 等

---

## 模块目录

### crates/

所有学习模块的根目录，每个模块是一个独立的 Rust crate。

### 模块结构

每个模块（如 `c01_ownership_borrow_scope/`）都遵循统一结构：

```text
c01_ownership_borrow_scope/
├── Cargo.toml               # 模块配置
├── README.md                # 模块说明
├── docs/                    # 文档目录
│   ├── 00_MASTER_INDEX.md   # 主索引（导航入口）
│   ├── FAQ.md               # 常见问题
│   ├── Glossary.md          # 术语表
│   ├── 01_theory/           # 理论文档
│   ├── 02_basics/           # 基础文档
│   ├── 03_advanced/         # 高级文档
│   └── 04_practice/         # 实践文档
├── src/                     # 源代码
│   ├── lib.rs               # 库入口
│   └── ...                  # 其他源文件
├── examples/                # 示例代码
│   ├── 01_basic.rs
│   └── ...
├── tests/                   # 单元/集成测试
│   ├── integration_test.rs
│   └── ...
└── benches/                 # 基准测试（部分模块）
    └── benchmark.rs
```

### 模块详解

#### C01 - 所有权与借用 (c01_ownership_borrow_scope/)

- **主题**: 所有权、借用、生命周期
- **难度**: ⭐ 入门必修
- **文档**: 20+ 术语，6 个 FAQ
- **入口**: [docs/00_MASTER_INDEX.md](./crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md)

#### C02 - 类型系统 (c02_type_system/)

- **主题**: 类型、泛型、Trait
- **难度**: ⭐⭐ 初级
- **文档**: 15+ 术语，7 个 FAQ
- **入口**: [docs/00_MASTER_INDEX.md](./crates/c02_type_system/docs/00_MASTER_INDEX.md)

#### C03 - 控制流与函数 (c03_control_fn/)

- **主题**: 条件、循环、闭包、错误处理
- **难度**: ⭐⭐ 初级
- **文档**: 12+ 术语，8 个 FAQ
- **入口**: [docs/00_MASTER_INDEX.md](./crates/c03_control_fn/docs/00_MASTER_INDEX.md)

#### C04 - 泛型编程 (c04_generic/)

- **主题**: 高级泛型、GATs、RPITIT
- **难度**: ⭐⭐⭐ 中级
- **文档**: 10+ 术语，6 个 FAQ
- **入口**: [docs/00_MASTER_INDEX.md](./crates/c04_generic/docs/00_MASTER_INDEX.md)

#### C05 - 线程与并发 (c05_threads/)

- **主题**: 多线程、Channel、Mutex、Arc
- **难度**: ⭐⭐⭐ 中级
- **文档**: 15+ 术语，8 个 FAQ
- **入口**: [docs/00_MASTER_INDEX.md](./crates/c05_threads/docs/00_MASTER_INDEX.md)

#### C06 - 异步编程 (c06_async/)

- **主题**: async/await、Future、tokio
- **难度**: ⭐⭐⭐⭐ 高级
- **文档**: 18+ 术语，9 个 FAQ
- **入口**: [docs/00_MASTER_INDEX.md](./crates/c06_async/docs/00_MASTER_INDEX.md)

#### C07 - 进程管理 (c07_process/)

- **主题**: 进程、IPC、信号处理
- **难度**: ⭐⭐⭐ 中级
- **文档**: 12+ 术语，5 个 FAQ
- **入口**: [docs/00_MASTER_INDEX.md](./crates/c07_process/docs/00_MASTER_INDEX.md)

#### C08 - 算法与数据结构 (c08_algorithms/)

- **主题**: 常见算法和数据结构实现
- **难度**: ⭐⭐⭐ 中级
- **文档**: 10+ 术语，6 个 FAQ
- **入口**: [docs/00_MASTER_INDEX.md](./crates/c08_algorithms/docs/00_MASTER_INDEX.md)

#### C09 - 设计模式 (c09_design_pattern/)

- **主题**: GoF 模式、Rust 特定模式、并发模式
- **难度**: ⭐⭐⭐⭐ 高级
- **文档**: 15+ 术语，7 个 FAQ
- **入口**: [docs/00_MASTER_INDEX.md](./crates/c09_design_pattern/docs/00_MASTER_INDEX.md)

#### C10 - 网络编程 (c10_networks/)

- **主题**: TCP/UDP、HTTP、WebSocket
- **难度**: ⭐⭐⭐ 中级-高级
- **文档**: 12+ 术语，8 个 FAQ
- **入口**: [docs/00_MASTER_INDEX.md](./crates/c10_networks/docs/00_MASTER_INDEX.md)

#### C11 - 中间件集成 (c11_middlewares/)

- **主题**: 数据库、消息队列、缓存
- **难度**: ⭐⭐⭐ 中级
- **文档**: 10+ 术语，5 个 FAQ
- **入口**: [docs/00_MASTER_INDEX.md](./crates/c11_middlewares/docs/00_MASTER_INDEX.md)

#### C12 - 模型与架构 (c12_model/)

- **主题**: 建模理论、架构模式、形式化方法
- **难度**: ⭐⭐⭐⭐ 高级
- **文档**: 8+ 术语，5 个 FAQ
- **入口**: [docs/00_MASTER_INDEX.md](./crates/c12_model/docs/00_MASTER_INDEX.md)

#### C13 - 可靠性框架 (c13_reliability/)

- **主题**: 容错、分布式系统、可观测性
- **难度**: ⭐⭐⭐⭐⭐ 高级
- **文档**: 18+ 术语，9 个 FAQ
- **入口**: [docs/00_MASTER_INDEX.md](./crates/c13_reliability/docs/00_MASTER_INDEX.md)

---

## 脚本目录

### scripts/

自动化脚本和工具。

#### 主要脚本

##### dev-setup.sh / dev-setup.ps1

- **用途**: 开发环境设置
- **功能**:
  - 安装 Rust 工具链
  - 配置开发工具
  - 安装依赖

##### ci/ 目录

- **用途**: CI/CD 脚本
- **文件**:
  - `check_dependencies.ps1` - 依赖检查
  - `run_benchmarks.ps1` - 运行基准测试
  - `security_fix_automation.ps1` - 安全修复

##### observability/ 目录

- **用途**: 可观测性相关脚本
- **用途**: 监控、日志、追踪

---

## 工具配置

### Rust 工具配置

#### rustfmt 配置示例

```toml
edition = "2021"
max_width = 100
tab_spaces = 4
```

#### clippy 配置示例

```toml
# Clippy 配置
```

#### deny.toml

- **用途**: cargo-deny 配置
- **功能**: 依赖审计、安全检查

#### tarpaulin.toml

- **用途**: 代码覆盖率配置
- **工具**: cargo-tarpaulin

---

## 导航指南

### 🎯 我想

#### 学习 Rust

1. **完全新手**: 从 [README.md](./README.md) 开始
2. **选择路径**: 查看 [学习路径](./README.md#学习路径推荐)
3. **开始模块**: 从 [C01](./crates/c01_ownership_borrow_scope/) 开始

#### 查找资料

1. **快速查询**: [QUICK_REFERENCE.md](./QUICK_REFERENCE.md)
2. **详细学习**: 各模块的 `docs/00_MASTER_INDEX.md`
3. **常见问题**: 各模块的 `docs/FAQ.md`
4. **术语查询**: 各模块的 `docs/Glossary.md`

#### 解决问题

1. **编译错误**: [TROUBLESHOOTING.md](./TROUBLESHOOTING.md#编译错误)
2. **运行时错误**: [TROUBLESHOOTING.md](./TROUBLESHOOTING.md#运行时错误)
3. **性能问题**: [TROUBLESHOOTING.md](./TROUBLESHOOTING.md#性能问题)

#### 提升代码质量

1. **最佳实践**: [BEST_PRACTICES.md](./BEST_PRACTICES.md)
2. **代码审查**: 查看示例代码
3. **学习模式**: [C09 设计模式](./crates/c09_design_pattern/)

#### 参与贡献

1. **阅读指南**: [CONTRIBUTING.md](./CONTRIBUTING.md)
2. **查看规划**: [ROADMAP.md](./ROADMAP.md)
3. **选择任务**: GitHub Issues

---

## 📊 项目统计

### 文档规模

- **项目级文档**: 10 个（~14,500 行）
- **模块级文档**: 39 个（~8,600 行）
- **深度文档**: 4000+ 个文件
- **总文档量**: ~23,000 行 + 深度文档

### 代码规模

- **模块数量**: 13 个
- **源代码**: 50,000+ 行
- **示例代码**: 300+ 个
- **测试用例**: 200+ 个
- **基准测试**: 50+ 个

### 内容覆盖

- **核心概念**: 100%
- **高级特性**: 100%
- **并发编程**: 100%
- **异步编程**: 100%
- **网络编程**: 100%
- **系统编程**: 100%

---

## 🔗 相关文档

- **项目入口**: [README.md](./README.md)
- **学习资源**: [RESOURCES.md](./RESOURCES.md)
- **贡献指南**: [CONTRIBUTING.md](./CONTRIBUTING.md)
- **项目路线**: [ROADMAP.md](./ROADMAP.md)

---

**快速定位，高效学习！** 🚀

了解项目结构有助于更好地利用学习资源。

**最后更新**: 2025-10-19
**维护团队**: Rust 学习社区
**版本**: v1.0
