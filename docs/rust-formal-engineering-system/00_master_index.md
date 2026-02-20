# Rust 形式化工程系统 - 主索引

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+
> **阅读说明**: 本目录为**单一索引层**，各子目录 README 仅为占位重定向（内容已整合至研究笔记及 crates）。**实质内容请直接访问下方表格中的链接**，勿依赖子目录 README 获取正文。

---

## 🏛️ 理论体系与论证体系结构（顶层入口）

| 文档 | 说明 |
| :--- | :--- || [THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE](../research_notes/THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md) | 理论四层、论证五层、安全与非安全边界 |
| [SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS](../research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) | 安全与非安全全面论证、契约、UB |

---

## 理论基础 (01_theoretical_foundations)

| 子模块 | 映射目标 | 说明 |
| :--- | :--- | :--- || **01 类型系统** | [research_notes/type_theory/](../research_notes/type_theory/) | 类型系统基础、Trait、型变 |
| **02 所有权系统** | [research_notes/formal_methods/ownership_model.md](../research_notes/formal_methods/ownership_model.md) | 所有权形式化模型 |
| **03 所有权与借用** | [research_notes/formal_methods/](../research_notes/formal_methods/) | 借用检查器、所有权、生命周期 |
| **02 内存安全** | [research_notes/formal_methods/borrow_checker_proof.md](../research_notes/formal_methods/borrow_checker_proof.md) | 借用检查器与内存安全 |
| **05 Trait 系统** | [research_notes/type_theory/trait_system_formalization.md](../research_notes/type_theory/trait_system_formalization.md) | Trait 形式化 |
| **06 生命周期管理** | [research_notes/formal_methods/lifetime_formalization.md](../research_notes/formal_methods/lifetime_formalization.md) | 生命周期形式化 |
| **08 宏系统** | [crates/c11_macro_system/docs/](../../crates/c11_macro_system/docs/) | 宏系统文档 |
| **09 形式化验证** | [research_notes/TOOLS_GUIDE.md](../research_notes/TOOLS_GUIDE.md) | Prusti、Kani、Creusot |
| **10 数学基础** | [research_notes/type_theory/](../research_notes/type_theory/) | 类型理论与数学基础 |

### 类型系统子路径

| 路径 | 映射目标 |
| :--- | :--- || 01_type_system/ | [type_theory/](../research_notes/type_theory/) |
| 01_type_system/06_variance.md | [type_theory/variance_theory.md](../research_notes/type_theory/variance_theory.md) |

---

## 编程范式 (02_programming_paradigms)

| 子模块 | 映射目标 | 说明 |
| :--- | :--- | :--- || **01 同步编程** | [crates/c05_threads/](../../crates/c05_threads/) | 线程与同步并发 |
| **02 异步编程** | [crates/c06_async/](../../crates/c06_async/) | 异步、Future、async/await |
| **09 Actor 模型** | [crates/c05_threads/docs/](../../crates/c05_threads/docs/)、[crates/c06_async/docs/](../../crates/c06_async/docs/) | 消息传递与 Actor |
| **11 基准指南** | [research_notes/experiments/performance_benchmarks.md](../research_notes/experiments/performance_benchmarks.md) | 性能基准 |

---

## 设计模式 (03_design_patterns)

| 子模块 | 映射目标 |
| :--- | :--- || 设计模式 | [crates/c09_design_pattern/](../../crates/c09_design_pattern/) |
| 04 并发模式 | [crates/c09_design_pattern/docs/](../../crates/c09_design_pattern/docs/) |

---

## 工具链生态 (06_toolchain_ecosystem)

| 子模块 | 映射目标 |
| :--- | :--- || 工具链 | [06_toolchain/](../06_toolchain/) |
| 01 编译器 | [06_toolchain/01_compiler_features.md](../06_toolchain/01_compiler_features.md) |
| 02 包管理器 | [06_toolchain/02_cargo_workspace_guide.md](../06_toolchain/02_cargo_workspace_guide.md) |
| 03 构建工具 | [06_toolchain/](../06_toolchain/) |

---

## 软件工程 (05_software_engineering)

| 子模块 | 映射目标 |
| :--- | :--- || 07 测试 | [quick_reference/testing_cheatsheet.md](../02_reference/quick_reference/testing_cheatsheet.md) |
| 应用分析 | [APPLICATIONS_ANALYSIS_VIEW.md](../04_thinking/APPLICATIONS_ANALYSIS_VIEW.md) — 应用场景→技术选型→论证依据 |

---

## 研究议程 (09_research_agenda)

| 子模块 | 映射目标 |
| :--- | :--- || 04 研究方法 | [research_notes/research_methodology.md](../research_notes/research_methodology.md) |

---

## 质量保障 (10_quality_assurance)

| 映射目标 |
| :--- || [docs/TESTING_COVERAGE_GUIDE.md](../TESTING_COVERAGE_GUIDE.md) |
| [docs/PERFORMANCE_TESTING_REPORT.md](../05_guides/PERFORMANCE_TESTING_REPORT.md) |

---

## 证明与公理→定理链

| 资源 | 说明 |
| :--- | :--- || [PROOF_INDEX](../research_notes/PROOF_INDEX.md) | 形式化证明索引（87+ 个证明，与思维表征证明树交叉引用） |
| [THINKING_REPRESENTATION_METHODS](../04_thinking/THINKING_REPRESENTATION_METHODS.md) | 证明树图（MaybeUninit、借用检查器、生命周期、Send/Sync 等） |

---

## 返回

- [形式化工程系统 README](./README.md)
- [文档中心](../README.md)
