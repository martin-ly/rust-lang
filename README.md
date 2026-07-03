# Rust 分层概念知识体系 v3.0

> **Rust版本**: 1.96.1 stable (2026-07-04)
> **Edition**: 2024
> **状态**: v3.0 正式发布 | 302 concept 文件（共 336） | 2,908 Markdown | 1,524 Rust 源文件 | Bloom 双标签覆盖率 99.6% | Phase 1-5 完成 | 活跃锚点 0 | 代码块编译通过率 100.0% | 概念国际化元数据覆盖率 EN/Summary/来源 100% | 2026-06-21

[![Rust](https://img.shields.io/badge/rust-1.96.1+-blue.svg)](https://www.rust-lang.org)
[![Edition](https://img.shields.io/badge/edition-2024-purple.svg)](https://doc.rust-lang.org/edition-guide/rust-2024/)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](LICENSE)
[![KB Quality](https://img.shields.io/badge/kb_quality-23_risk_files-yellow.svg)](reports/kb_quality_dashboard.md)
[![i18n](https://img.shields.io/badge/i18n-EN%2FSummary%20100%25-success.svg)](concept/00_meta/learning_mvp_path.md)

---

## 什么是这个项目？

一个**分层、可验证、可搜索**的 Rust 概念知识库，覆盖从入门到形式化验证的完整学习路径。

区别于传统的"代码示例集合"，本体系采用**八层认知架构**（L0-L7），每个概念都有：**定义 → 代码 → 反例 → 形式化 → 跨语言对比 → 工程实践 → 未来演进**。

```text
L0 元层 ──→ 学习指南、速查卡片、自测题库、质量仪表盘
L1 基础 ──→ 所有权、借用、生命周期、类型系统
L2 进阶 ──→ Trait、泛型、内存管理、错误处理
L3 高级 ──→ 并发、异步、unsafe、宏
L4 形式化 ─→ 线性逻辑、类型论、所有权形式化、RustBelt
L5 对比 ──→ 多语言范式对比、安全边界分析
L6 生态 ──→ 工具链、设计模式、核心 crate、应用领域
L7 未来 ──→ AI 集成、形式化方法、语言演进
```

---

## 🌍 国际学习者入口

本知识库以**中文深度内容**为主体，同时为国际化可读性提供：

- 每个 `concept/` 概念文件均含 `**EN**` 英文标题与 `**Summary**` 英文摘要
- [`terminology_glossary.md`](concept/00_meta/terminology_glossary.md) 提供 180+ 中英术语对照
- [`LEARNING_MVP_PATH.md`](concept/00_meta/learning_mvp_path.md) 对接国际官方/经典教程：
  - [The Rust Programming Language (3rd Ed)](https://doc.rust-lang.org/book/)
  - [Brown University Interactive Book](https://rust-book.cs.brown.edu/)
  - [Google Comprehensive Rust](https://google.github.io/comprehensive-rust/)
  - [Rust By Example](https://doc.rust-lang.org/rust-by-example/)

> 欢迎通过 Issue 或 PR 反馈术语翻译、链接可达性与跨文化学习体验问题。

---

## 内容治理与 Canonical 规则

> 完整规则见 [`AGENTS.md`](AGENTS.md)。

本项目采用 **单一权威来源（Single Source of Truth）** 原则：

- **`concept/` 是权威概念层**。每个 Rust 概念只应在 `concept/` 中有一份完整、深度、可维护的解释。
- **`knowledge/`** 只保留精简卡片、速查、学习入口；重复内容改为重定向到 `concept/`。
- **`docs/`** 只保留指南、参考、研究报告；概念解释必须链接到 `concept/` 权威页。
- **`content/`** 保留专题深度内容；若与 `concept/` 重叠，应合并到 `concept/` 或改为重定向。
- **`crates/*/docs/`** 只保留与 crate 直接相关的独特内容，禁止复制通用概念解释。
- **`archive/`** 是只读历史归档，不得与活跃目录重复。
- **`book/`** 是 `mdbook build` 输出目录，除 `book/README.md` 外不提交到版本控制。

新增或修改内容前，请先运行 `python scripts/detect_content_overlap.py` 检查重复。

---

## 快速开始

### 学习路径

| 目标 | 起点 | 预计时长 |
|:---|:---|:---|
| 🎯 **系统掌握** | [`learning_guide.md`](concept/00_meta/learning_guide.md) → L1 → L2 → L3 | 40-60h |
| 💼 **面试准备** | [`quick_reference.md`](concept/00_meta/quick_reference.md) + [`self_assessment.md`](concept/00_meta/self_assessment.md) | 8-12h |
| 🎓 **学术深入** | L4 形式化层 + [`semantic_space.md`](concept/00_meta/semantic_space.md) | 20-30h |
| 🔧 **问题驱动** | [`self_assessment.md`](concept/00_meta/self_assessment.md) 错题 → 对应章节 | 按需 |
| 🌍 **国际学习者** | [`LEARNING_MVP_PATH.md`](concept/00_meta/learning_mvp_path.md) → 官方文档对照 | 按需 |

### 质量审计

```bash
# 运行自动化质量审计
python scripts/kb_auditor.py

# 查看仪表盘
cat reports/kb_quality_dashboard.md

# 构建概念搜索索引
python scripts/build_search_index.py

# 编译验证
cargo build --workspace
cargo test --workspace
```

### 工具链说明

- 默认工具链为 **stable 1.96.1**（`rust-toolchain.toml` 使用 `stable` 通道）。
- `crates/c02_type_system`、`c04_generic`、`c06_async`、`c08_algorithms`、`c13_embedded`、`exercises` 中的 nightly-only 预览模块通过各 crate 的 `build.rs` 自动检测 nightly 并启用；stable 默认构建不会编译这些不稳定特性。
- 如需本地验证 nightly 预览模块：

  ```bash
  cargo +nightly check --workspace --all-features
  cargo +nightly clippy --workspace --tests --all-features -- -D warnings
  cargo +nightly test --workspace --all-features
  ```

---

## 核心文件导航

### L0 元层：学习工具

| 文件 | 用途 | 规模 |
|:---|:---|:---|
| [`learning_guide.md`](concept/00_meta/learning_guide.md) | 4条学习路径 + 每级关键概念 + 前置依赖 | ~657行 |
| [`quick_reference.md`](concept/00_meta/quick_reference.md) | A-Z概念速查 + ~27个错误码 + 模式决策树 | ~817行 |
| [`self_assessment.md`](concept/00_meta/self_assessment.md) | **80道自测题**（L1-L6，含折叠答案） | ~2,210行 |
| [`semantic_space.md`](concept/00_meta/semantic_space.md) | 表征空间理论 + 等价表达 + 机制组合代数 | ~1,319行 |
| [`terminology_glossary.md`](concept/00_meta/terminology_glossary.md) | 100个核心术语中英对照 + 定义 | ~584行 |

### L1-L3：核心概念

| 层级 | 文件 | 核心内容 |
|:---|:---|:---|
| L1 | [`01_ownership.md`](concept/01_foundation/01_ownership.md) | Move/Copy/Drop、RAII、所有权转移规则 |
| L1 | [`02_borrowing.md`](concept/01_foundation/02_borrowing.md) | 借用规则、分离逻辑、分数权限 |
| L1 | [`03_lifetimes.md`](concept/01_foundation/03_lifetimes.md) | 生命周期、NLL、Polonius、Elision形式化 |
| L1 | [`04_type_system.md`](concept/01_foundation/04_type_system.md) | enum/impl Trait/dyn Trait、类型论差异 |
| L2 | [`01_traits.md`](concept/02_intermediate/01_traits.md) | Auto trait、GATs、RPITIT、对象安全 |
| L2 | [`02_generics.md`](concept/02_intermediate/02_generics.md) | Const Generics、单态化、HRTB |
| L2 | [`03_memory_management.md`](concept/02_intermediate/03_memory_management.md) | Box/Rc/Arc、内部可变性、MaybeUninit |
| L2 | [`04_error_handling.md`](concept/02_intermediate/04_error_handling.md) | Result/Option、?运算符、错误传播 |
| L2 | [`05_assert_matches.md`](concept/02_intermediate/05_assert_matches.md) | 模式匹配断言（1.96 stable） |
| L3 | [`01_concurrency.md`](concept/03_advanced/01_concurrency.md) | Send/Sync、Atomic内存序、死锁分析 |
| L3 | [`02_async.md`](concept/03_advanced/02_async.md) | Future/Pin/Waker、async/await状态机 |
| L3 | [`03_unsafe.md`](concept/03_advanced/03_unsafe.md) | FFI、repr属性、Miri、原始指针 |
| L3 | [`04_macros.md`](concept/03_advanced/04_macros.md) | macro_rules!/过程宏、卫生性 |

### L4：形式化

| 文件 | 核心内容 |
|:---|:---|
| [`01_linear_logic.md`](concept/04_formal/01_linear_logic.md) | ⊗/⊸/! 对应 Rust 所有权/Copy/借用 |
| [`02_type_theory.md`](concept/04_formal/02_type_theory.md) | System F、HM算法、参数性定理 |
| [`03_ownership_formal.md`](concept/04_formal/03_ownership_formal.md) | Oxide、Tree Borrows、Polonius |
| [`04_rustbelt.md`](concept/04_formal/04_rustbelt.md) | Iris分离逻辑、CSL、验证工具链 |
| [`22_modern_verification_tools.md`](concept/04_formal/22_modern_verification_tools.md) | AutoVerus、Kani、ESBMC、Safety Tags |

### L5-L7：对比、生态、未来

| 层级 | 文件 | 核心内容 |
|:---|:---|:---|
| L5 | [`01_rust_vs_cpp.md`](concept/05_comparative/01_rust_vs_cpp.md) | RAII语义差异、性能对比 |
| L5 | [`02_rust_vs_go.md`](concept/05_comparative/02_rust_vs_go.md) | 并发模型、错误处理、GC对比 |
| L5 | [`03_paradigm_matrix.md`](concept/05_comparative/03_paradigm_matrix.md) | 多语言范式谱系 |
| L5 | [`04_safety_boundaries.md`](concept/05_comparative/04_safety_boundaries.md) | unsafe边界、供应链安全 |
| L6 | [`01_toolchain.md`](concept/06_ecosystem/01_toolchain.md) | Cargo、Workspace、Features |
| L6 | [`02_patterns.md`](concept/06_ecosystem/02_patterns.md) | 类型状态、Builder、Newtype |
| L6 | [`03_core_crates.md`](concept/06_ecosystem/03_core_crates.md) | serde/tokio/rayon等核心crate |
| L6 | [`04_application_domains.md`](concept/06_ecosystem/04_application_domains.md) | WASM/嵌入式/CLI/游戏 |
| L7 | [`01_ai_integration.md`](concept/07_future/01_ai_integration.md) | AI辅助编程、RL on编译错误 |
| L7 | [`02_formal_methods.md`](concept/07_future/02_formal_methods.md) | Kani/Miri/CI集成 |
| L7 | [`03_evolution.md`](concept/07_future/03_evolution.md) | Edition系统、Effects System |
| L7 | [`rust_1_97_preview.md`](concept/07_future/rust_1_97_preview.md) | 1.97 前沿特性跟踪 |

---

## 质量基线

| 指标 | 数值 | 状态 |
|:---|:---|:---|
| concept 文件 | 288 | ✅ |
| 总 Markdown 文档 | 2,890 | ✅ |
| Rust 源文件 | 1,524 | ✅ |
| Workspace Crates | 17 | ✅ |
| 定理链 (⟹) | 1,172 | ✅ |
| 反命题 | 597 | ✅ |
| Mermaid图 | 537 | ✅ |
| 代码块编译验证 | 90.7% 通过 | 🔄 持续优化 |
| 死链 | 0（核心路径）/ 8 文件待修复 | ⚠️ |
| 风险文件（非L0）| 23 | ⚠️ |
| 认知路径覆盖率 | 91% | ⚠️ |
| 自测题 | 80题 | ✅ |
| 概念搜索索引 | 851概念 | ✅ |

---

## 项目结构

```text
rust-lang/
├── concept/                    # 📚 知识体系核心（288 个活跃 md 文件，共 322 个）
│   ├── 00_meta/                # L0: 学习工具 + 质量基础设施
│   ├── 01_foundation/          # L1: 所有权/借用/生命周期/类型系统
│   ├── 02_intermediate/        # L2: Trait/泛型/内存管理/错误处理
│   ├── 03_advanced/            # L3: 并发/异步/unsafe/宏
│   ├── 04_formal/              # L4: 线性逻辑/类型论/形式化
│   ├── 05_comparative/         # L5: 多语言对比
│   ├── 06_ecosystem/           # L6: 工具链/模式/crate/应用
│   └── 07_future/              # L7: AI/形式化/演进
├── crates/                     # 🦀 可编译代码示例（17 workspace members）
│   ├── c01_ownership_borrow_scope/
│   ├── c02_type_system/
│   ├── c03_control_fn/
│   ├── c04_generic/
│   ├── c05_threads/
│   ├── c06_async/
│   ├── c07_process/
│   ├── c08_algorithms/
│   ├── c09_design_pattern/
│   ├── c10_networks/
│   ├── c11_macro_system_proc/
│   ├── c12_wasm/
│   ├── c13_embedded/
│   ├── common/
│   └── integration_tests/
├── exercises/                  # 📝 编程练习（80 个 .rs 文件，10 主题）
├── book/                       # 📖 mdbook 构建产物（不提交源码，除 README）
├── knowledge/                  # 🎯 结构化知识卡片
├── docs/                       # 📋 参考文档、研究报告、模板
├── scripts/                    # 🔧 自动化脚本（质量审计、链接检查、索引构建）
├── reports/                    # 📊 质量仪表盘、审计报告
├── .github/workflows/          # 🔄 CI 自动审计
├── CHANGELOG.md                # 变更日志
└── README.md                   # 本文件
```

---

## 自动化 CI

每次 PR 自动运行：

- ✅ 死链检测
- ✅ 风险文件识别
- ✅ 定理链/代码块统计
- ✅ 质量仪表盘更新
- ✅ 代码块编译验证
- ✅ Miri 内存安全验证
- ✅ 版本跟踪检查

---

## 许可证

[MIT许可证](LICENSE)

---

**维护者**: rust-lang 知识体系项目组
**最后更新**: 2026-07-01
**版本**: v3.0.1
**状态**: ✅ 内容去重 Phase 1 进行中

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-06-21 全面更新 README 数据，对齐实际项目规模（288 活跃 concept / 共 322、17 workspace members、2,890 文档）

**文档版本**: 3.0
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-06-21
**状态**: ✅ 门面数据全面对齐 2026-06-21
