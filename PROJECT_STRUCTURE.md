# 📁 项目结构说明 (Project Structure)

> **文档定位**: 详细解释项目的目录结构和组织方式
> **最后更新**: 2026-02-11
> **项目版本**: v1.0

---

## 📋 目录

- [📁 项目结构说明 (Project Structure)](#-项目结构说明-project-structure)
  - [📋 目录](#-目录)
  - [项目总览](#项目总览)
    - [设计原则](#设计原则)
  - [目录树概览](#目录树概览)
  - [核心目录说明](#核心目录说明)
    - [根目录文件](#根目录文件)
      - [📄 核心文档](#-核心文档)
      - [📦 配置文件](#-配置文件)
    - [crates/ - 学习模块](#crates---学习模块)
      - [📚 模块列表](#-模块列表)
      - [🏗️ 模块标准结构](#️-模块标准结构)
    - [guides/ - 学习指南](#guides---学习指南)
      - [📖 指南分类](#-指南分类)
    - [项目报告 (archive/)](#项目报告-archive)
      - [📊 报告位置](#-报告位置)
    - [docs/ - 跨模块文档与指南](#docs---跨模块文档与指南)
      - [📚 文档分类](#-文档分类)
    - [scripts/ - 脚本工具](#scripts---脚本工具)
    - [examples/ - 根级综合示例](#examples---根级综合示例)
    - [tests/ - 集成测试](#tests---集成测试)
    - [exercises/ - 练习入口](#exercises---练习入口)
  - [导航指南](#导航指南)
    - [🎯 我想](#-我想)
      - [学习Rust](#学习rust)
      - [查找资料](#查找资料)
      - [解决问题](#解决问题)
      - [提升代码质量](#提升代码质量)
      - [了解项目进度](#了解项目进度)
      - [参与贡献](#参与贡献)
  - [项目统计](#项目统计)
    - [📊 规模统计](#-规模统计)
    - [✨ 内容覆盖](#-内容覆盖)
  - [🔗 相关文档](#-相关文档)

---

## 项目总览

本项目是一个全面的 Rust 学习资源集合，采用 **Cargo Workspace** 组织多个学习模块。
项目结构经过精心设计，确保清晰的组织和易于导航。

### 设计原则

- ✅ **清晰分类**: 文档、代码、配置分别组织
- ✅ **扁平化根目录**: 根目录只保留核心文档
- ✅ **模块化设计**: 每个学习模块独立完整
- ✅ **文档优先**: 丰富的文档和指南支持

---

## 目录树概览

```text
rust-lang/
├── 📄 核心文档（根目录）
│   ├── README.md                    # 项目主入口 ⭐
│   ├── README.en.md                 # 英文版README
│   ├── CONTRIBUTING.md              # 贡献指南
│   ├── CHANGELOG.md                 # 更新日志
│   ├── LICENSE                      # 开源许可证
│   ├── BEST_PRACTICES.md            # 最佳实践
│   ├── LEARNING_CHECKLIST.md        # 学习检查清单
│   ├── QUICK_REFERENCE.md           # 快速参考手册
│   ├── RESOURCES.md                 # 学习资源大全
│   ├── ROADMAP.md                   # 项目路线图
│   ├── TROUBLESHOOTING.md           # 故障排查指南
│   └── PROJECT_STRUCTURE.md         # 本文档
│
├── 📦 构建配置
│   ├── Cargo.toml                   # Workspace配置 ⭐
│   ├── Cargo.lock                   # 依赖锁定文件
│   ├── rustfmt.toml                 # 代码格式化配置
│   ├── clippy.toml                  # Clippy Lint配置
│   ├── deny.toml                    # cargo-deny配置
│   └── tarpaulin.toml               # 代码覆盖率配置
│
├── 📚 crates/                       # 学习模块 ⭐⭐⭐
│   ├── c01_ownership_borrow_scope/  # C01: 所有权与借用
│   ├── c02_type_system/             # C02: 类型系统
│   ├── c03_control_fn/              # C03: 控制流与函数
│   ├── c04_generic/                 # C04: 泛型编程
│   ├── c05_threads/                 # C05: 线程与并发
│   ├── c06_async/                   # C06: 异步编程
│   ├── c07_process/                 # C07: 进程管理
│   ├── c08_algorithms/              # C08: 算法与数据结构
│   ├── c09_design_pattern/          # C09: 设计模式
│   ├── c10_networks/                # C10: 网络编程
│   ├── c11_macro_system/            # C11: 宏系统（声明宏、过程宏）
│   └── c12_wasm/                    # C12: WebAssembly
│
├── 📖 guides/                       # 学习指南入口 ⭐⭐
│   ├── README.md                    # 指南目录索引
│   └── AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md  # AI 辅助编程指南
│
├── 📊 报告 (见 archive/)             # 项目报告已归档 ⭐
│   ├── archive/reports/             # 阶段报告、模块报告
│   ├── docs/archive/reports/        # 归档报告
│   └── docs/archive/root_completion_reports/  # 根完成报告
│
├── 📖 docs/                         # 跨模块文档与指南
│   ├── quick_reference/             # 速查卡 (21 个)
│   ├── toolchain/                   # 工具链与版本说明
│   ├── rust-formal-engineering-system/  # 形式化工程索引
│   ├── research_notes/              # 研究笔记
│   ├── archive/                     # 归档报告
│   └── [使用指南、思维导图等 .md]
│
├── 🔧 scripts/                      # 脚本工具
│   ├── *.ps1                        # PowerShell脚本
│   ├── *.sh                         # Bash脚本
│   ├── check_links.ps1              # 文档链接检查
│   └── README.md
│
├── 💡 examples/                     # 根级综合示例（非 workspace 成员）
│   ├── advanced_usage_examples.rs
│   ├── comprehensive_integration_example.rs
│   ├── module_complete_examples.rs
│   └── real_world_applications.rs
│
├── 🧪 tests/                        # 集成测试
│   └── [测试文件...]
│
└── 🎯 exercises/                    # 练习入口（仅 README，指向外部工具）
    └── README.md
```

---

## 核心目录说明

### 根目录文件

#### 📄 核心文档

| 文件                    | 用途           | 何时查看        |
| ----------------------- | -------------- | --------------- |
| `README.md`             | 项目总览和入口 | 首次了解项目 ⭐ |
| `CONTRIBUTING.md`       | 贡献指南       | 想要贡献代码时  |
| `CHANGELOG.md`          | 更新日志       | 查看版本变更    |
| `BEST_PRACTICES.md`     | 最佳实践       | 提升代码质量    |
| `LEARNING_CHECKLIST.md` | 学习清单       | 追踪学习进度    |
| `QUICK_REFERENCE.md`    | 快速参考       | 查找语法速查 ⭐ |
| `RESOURCES.md`          | 学习资源       | 寻找学习材料    |
| `ROADMAP.md`            | 项目路线图     | 了解项目规划    |
| `TROUBLESHOOTING.md`    | 故障排查       | 遇到问题时 ⭐   |
| `PROJECT_STRUCTURE.md`  | 项目结构       | 了解目录组织    |

#### 📦 配置文件

| 文件             | 用途          | 说明                 |
| ---------------- | ------------- | -------------------- |
| `Cargo.toml`     | Workspace配置 | Cargo工作空间定义    |
| `Cargo.lock`     | 依赖锁定      | 自动生成，勿手动编辑 |
| `rustfmt.toml`   | 格式化配置    | `cargo fmt` 使用     |
| `clippy.toml`    | Lint配置      | `cargo clippy` 使用  |
| `deny.toml`      | 安全审计配置  | `cargo deny` 使用    |
| `tarpaulin.toml` | 覆盖率配置    | 代码覆盖率测试       |

---

### crates/ - 学习模块

**核心学习内容**，12 个独立模块，从基础到高级全面覆盖 Rust。

#### 📚 模块列表

| 模块    | 名称           | 难度       | 主题                   |
| ------- | -------------- | ---------- | ---------------------- |
| **C01** | 所有权与借用   | ⭐         | 所有权、借用、生命周期 |
| **C02** | 类型系统       | ⭐⭐       | 类型、泛型、Trait      |
| **C03** | 控制流与函数   | ⭐⭐       | 条件、循环、闭包       |
| **C04** | 泛型编程       | ⭐⭐⭐     | 高级泛型、GATs         |
| **C05** | 线程与并发     | ⭐⭐⭐     | 多线程、锁、原子       |
| **C06** | 异步编程       | ⭐⭐⭐⭐   | async/await、Future    |
| **C07** | 进程管理       | ⭐⭐⭐     | 进程、IPC              |
| **C08** | 算法与数据结构 | ⭐⭐⭐     | 经典算法               |
| **C09** | 设计模式       | ⭐⭐⭐⭐   | GoF模式、Rust模式      |
| **C10** | 网络编程       | ⭐⭐⭐     | TCP/UDP、HTTP          |
| **C11** | 宏系统         | ⭐⭐⭐⭐   | 声明宏、过程宏、DSL    |
| **C12** | WebAssembly    | ⭐⭐⭐⭐   | WASM、wasm-bindgen     |

#### 🏗️ 模块标准结构

每个模块遵循统一的结构：

```text
c##_module_name/
├── Cargo.toml           # 模块配置
├── README.md            # 模块说明
├── docs/                # 文档目录
│   ├── 00_MASTER_INDEX.md  # 主索引 ⭐
│   ├── FAQ.md              # 常见问题
│   ├── Glossary.md         # 术语表
│   └── [主题文档...]
├── src/                 # 源代码
│   ├── lib.rs
│   └── [模块代码...]
├── examples/            # 示例代码
├── tests/               # 测试用例
└── benches/            # 基准测试（部分模块）
```

**入口文档**: 每个模块的 `docs/00_MASTER_INDEX.md` 是学习的起点！

---

### guides/ - 学习指南

**系统化的学习指南和参考文档**，帮助深入理解和高效学习。

#### 📖 指南分类

**指南入口**: [guides/README.md](./guides/README.md) 提供指南导航和官方资源映射

**实际指南位置**:

- **docs/** - 异步编程、设计模式、宏系统、线程并发、WASM、性能调优、故障排查等使用指南
- **crates/*/docs/** - 各模块的 Tier 指南、快速开始、实践指南
- **docs/quick_reference/** - 19 个速查卡

**已完善**: AI 辅助指南 ([guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md](./guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md))、Unsafe 专题 ([docs/UNSAFE_RUST_GUIDE.md](./docs/UNSAFE_RUST_GUIDE.md))

**计划完善**（后续版本）: 编译器内部、认知科学、交互式学习平台等

👉 查看 [guides/README.md](./guides/README.md) 了解完整导航

---

### 项目报告 (archive/)

**项目各阶段的完成报告、更新总结和分析文档**，已归档至以下位置：

#### 📊 报告位置

| 类型 | 路径 |
| ------------ | ---- |
| 阶段/模块报告 | [archive/reports/](./archive/reports/) |
| 归档报告 | [docs/archive/reports/](./docs/archive/reports/) |
| 根完成报告 | [docs/archive/root_completion_reports/](./docs/archive/root_completion_reports/) |
| 计划实施完成 | [docs/PLAN_IMPLEMENTATION_COMPLETION_2026_02.md](./docs/PLAN_IMPLEMENTATION_COMPLETION_2026_02.md) |

---

### docs/ - 跨模块文档与指南

**跨模块通用文档、速查卡、工具链说明和研究笔记**。各模块深度内容以 `crates/*/docs/` 为准。

#### 📚 文档分类

- **quick_reference/** - 21 个速查卡
- **toolchain/** - 编译器、Cargo、Rust 版本演进说明
- **rust-formal-engineering-system/** - 形式化工程系统索引（内容整合至 research_notes）
- **research_notes/** - 研究笔记、实验、形式化方法
- **archive/** - 归档报告
- **根目录 .md** - 使用指南（WASM、线程并发、宏系统等）、思维导图、知识结构

---

### scripts/ - 脚本工具

**自动化脚本和工具**，支持Windows (PowerShell) 和 Unix (Bash)。

```text
scripts/
├── *.ps1               # PowerShell脚本
├── *.sh                # Bash脚本
├── check_links.ps1     # 文档链接检查（含旧路径扫描）
└── README.md           # 脚本说明
```

---

### examples/ - 根级综合示例

**跨模块综合示例**，展示多模块协同用法。这些 `.rs` 文件非 Cargo workspace 成员，可复制到 [Rust Playground](https://play.rust-lang.org/) 运行，或作为参考代码学习。

- `advanced_usage_examples.rs` - 高级用法
- `comprehensive_integration_example.rs` - 综合集成
- `module_complete_examples.rs` - 模块完整示例
- `real_world_applications.rs` - 实际应用场景

**注**：各模块的 `crates/*/examples/` 为可运行示例，使用 `cargo run -p <crate> --example <name>` 运行。

---

### tests/ - 集成测试

**工作空间级别的集成测试**。

---

### exercises/ - 练习入口

**交互式练习导航**。本项目无内置练习题，[exercises/README.md](./exercises/README.md) 提供外部工具入口：

- **Rustlings** - 官方命令行交互式学习
- **Rust Playground** - 在线运行代码
- **各模块 examples** - 可运行 `cargo run -p <crate> --example <name>` 实践

---

## 导航指南

### 🎯 我想

#### 学习Rust

1. **完全新手** → [README.md](./README.md) → [C01模块](./crates/c01_ownership_borrow_scope/)
2. **选择路径** → [学习路径](./README.md#学习路径推荐)
3. **快速上手** → [学习指南](./guides/README.md)

#### 查找资料

1. **快速查询** → [QUICK_REFERENCE.md](./QUICK_REFERENCE.md) 或 [速查卡目录](./docs/quick_reference/README.md)
2. **深入学习** → 各模块的 `docs/00_MASTER_INDEX.md`
3. **常见问题** → 各模块的 `docs/FAQ.md`
4. **术语查询** → 各模块的 `docs/Glossary.md`
5. **所有文档** → [文档中心](./docs/README.md)

#### 解决问题

1. **编译错误** → [TROUBLESHOOTING.md](./TROUBLESHOOTING.md#编译错误)
2. **运行时错误** → [TROUBLESHOOTING.md](./TROUBLESHOOTING.md#运行时错误)
3. **性能问题** → [TROUBLESHOOTING.md](./TROUBLESHOOTING.md#性能问题)

#### 提升代码质量

1. **最佳实践** → [BEST_PRACTICES.md](./BEST_PRACTICES.md)
2. **代码审查** → 查看模块示例代码
3. **学习模式** → [C09 设计模式](./crates/c09_design_pattern/)

#### 了解项目进度

1. **整体进度** → [archive/reports/](./archive/reports/)
2. **模块进度** → [archive/reports/](./archive/reports/)
3. **更新历史** → [CHANGELOG.md](./CHANGELOG.md)
4. **未来规划** → [ROADMAP.md](./ROADMAP.md)

#### 参与贡献

1. **阅读指南** → [CONTRIBUTING.md](./CONTRIBUTING.md)
2. **查看规划** → [ROADMAP.md](./ROADMAP.md)
3. **提交Issue** → GitHub Issues

---

## 项目统计

### 📊 规模统计

```text
📁 目录结构：
├─ 学习模块：12 个 (C01-C12)
├─ 指南文档：15+ 篇
├─ 项目报告：30+ 篇
├─ 深度文档：5000+ 个文件
└─ 总文档量：~50,000 行

💻 代码规模：
├─ Rust 源代码：50,000+ 行
├─ 示例代码：300+ 个
├─ 测试用例：200+ 个
└─ 基准测试：50+ 个

📚 学习资源：
├─ 主索引文档：12 个
├─ FAQ：79 个问题
├─ 术语定义：165+ 个
└─ 实践项目：10+ 个
```

### ✨ 内容覆盖

- ✅ **基础语法**: 100%
- ✅ **并发编程**: 100%
- ✅ **异步编程**: 100%
- ✅ **网络编程**: 100%
- ✅ **系统编程**: 100%
- ✅ **生产实践**: 100%

---

## 🔗 相关文档

- **项目入口**: [README.md](./README.md) ⭐
- **学习指南**: [guides/](./guides/) ⭐⭐
- **项目报告**: [archive/reports/](./archive/reports/)
- **贡献指南**: [CONTRIBUTING.md](./CONTRIBUTING.md)
- **项目路线**: [ROADMAP.md](./ROADMAP.md)
- **学习资源**: [RESOURCES.md](./RESOURCES.md)

---

**快速定位，高效学习！** 🚀

了解项目结构有助于更好地利用学习资源。

**最后更新**: 2026-02-11
**维护团队**: Rust 学习社区
**版本**: v2.0
