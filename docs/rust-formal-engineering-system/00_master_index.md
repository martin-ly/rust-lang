# Rust 形式化工程系统 - 主索引

> **内容分级**: [归档级]
> **说明**: 本文档为历史研究材料，最新内容请参阅 [knowledge/04_expert/safety_critical/02_rust_safety_critical_ecosystem_master_index.md](../../knowledge/04_expert/safety_critical/02_rust_safety_critical_ecosystem_master_index.md)
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Rust 形式化工程系统 - 主索引](#rust-形式化工程系统---主索引)
  - [📑 目录](#-目录)
  - [🏛️ 理论体系与论证体系结构（顶层入口）](#️-理论体系与论证体系结构顶层入口)
  - [理论基础 (01\_theoretical\_foundations)](#理论基础-01_theoretical_foundations)
    - [类型系统子路径](#类型系统子路径)
  - [编程范式 (02\_programming\_paradigms)](#编程范式-02_programming_paradigms)
  - [设计模式 (03\_design\_patterns)](#设计模式-03_design_patterns)
  - [工具链生态 (06\_toolchain\_ecosystem)](#工具链生态-06_toolchain_ecosystem)
  - [软件工程 (05\_software\_engineering)](#软件工程-05_software_engineering)
  - [研究议程 (09\_research\_agenda)](#研究议程-09_research_agenda)
  - [质量保障 (10\_quality\_assurance)](#质量保障-10_quality_assurance)
  - [证明与公理→定理链](#证明与公理定理链)
  - [返回](#返回)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)
  - [权威来源索引](#权威来源索引-1)

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **阅读说明**: 本目录为**单一索引层**，各子目录 README 仅为占位重定向（内容已整合至研究笔记及 crates）。**实质内容请直接访问下方表格中的链接**，勿依赖子目录 README 获取正文。

---

## 🏛️ 理论体系与论证体系结构（顶层入口）
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 文档 | 说明 |
| :--- | :--- | :--- | :--- | :--- |
| [SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS](../research_notes/10_safe_unsafe_comprehensive_analysis.md) | 安全与非安全全面论证、契约、UB |

---

## 理论基础 (01_theoretical_foundations)
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 子模块 | 映射目标 | 说明 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **02 所有权系统** | [research_notes/formal_methods/10_ownership_model.md](../research_notes/formal_methods/10_ownership_model.md) | 所有权形式化模型 |
| **03 所有权与借用** | [research_notes/formal_methods/](../../archive/research_notes_2026_06_25/formal_methods/README.md) | 借用检查器、所有权、生命周期 |
| **02 内存安全** | [research_notes/formal_methods/10_borrow_checker_proof.md](../research_notes/formal_methods/10_borrow_checker_proof.md) | 借用检查器与内存安全 |
| **05 Trait 系统** | [research_notes/type_theory/10_trait_system_formalization.md](../../archive/research_notes_2026_06_25/type_theory/10_trait_system_formalization.md) | Trait 形式化 |
| **06 生命周期管理** | research_notes/formal_methods/10_lifetime_formalization.md | 生命周期形式化 |
| **08 宏系统** | [crates/c11_macro_system/docs/](../../crates/c11_macro_system/docs/README.md) | 宏系统文档 |
| **09 形式化验证** | [research_notes/10_tools_guide.md](../../archive/research_notes_2026_06_25/10_tools_guide.md) | Prusti、Kani、Creusot |
| **10 数学基础** | [research_notes/type_theory/](../research_notes/type_theory/README.md) | 类型理论与数学基础 |

### 类型系统子路径

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 路径 | 映射目标 |
| :--- | :--- | :--- | :--- | :--- |
| 01_type_system/06_variance.md | [type_theory/10_variance_theory.md](../research_notes/type_theory/10_variance_theory.md) |

---

## 编程范式 (02_programming_paradigms)
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 子模块 | 映射目标 | 说明 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **02 异步编程** | [crates/c06_async/](../../crates/c06_async/README.md) | 异步、Future、async/await |
| **09 Actor 模型** | [crates/c05_threads/docs/](../../crates/c05_threads/docs/README.md)、[crates/c06_async/docs/](../../crates/c06_async/docs/README.md) | 消息传递与 Actor |
| **11 基准指南** | [research_notes/experiments/10_performance_benchmarks.md](../../archive/research_notes_2026_06_25/experiments/10_performance_benchmarks.md) | 性能基准 |

---

## 设计模式 (03_design_patterns)
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 子模块 | 映射目标 |
| :--- | :--- | :--- | :--- | :--- |
| 04 并发模式 | [crates/c09_design_pattern/docs/](../../crates/c09_design_pattern/docs/README.md) |

---

## 工具链生态 (06_toolchain_ecosystem)
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 子模块 | 映射目标 |
| :--- | :--- | :--- | :--- | :--- |
| 01 编译器 | [06_toolchain/01_compiler_features.md](../06_toolchain/01_compiler_features.md) |
| 02 包管理器 | 06_toolchain/02_cargo_workspace_guide.md |
| 03 构建工具 | [06_toolchain/](../06_toolchain/README.md) |

---

## 软件工程 (05_software_engineering)
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 子模块 | 映射目标 |
| :--- | :--- | :--- | :--- | :--- |
| 应用分析 | [04_applications_analysis_view.md](../04_thinking/04_applications_analysis_view.md) — 应用场景→技术选型→论证依据 |

---

## 研究议程 (09_research_agenda)
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

| 子模块 | 映射目标 |
| :--- | :--- | :--- | :--- | :--- |

---

## 质量保障 (10_quality_assurance)
>
> **[来源: [crates.io](https://crates.io/)]**

| 映射目标 |
| :--- | :--- | :--- |
| [docs/05_performance_testing_report.md](../05_guides/05_performance_testing_report.md) |

---

## 证明与公理→定理链
>
> **[来源: [docs.rs](https://docs.rs/)]**

| 资源 | 说明 |
| :--- | :--- | :--- | :--- | :--- |
| [THINKING_REPRESENTATION_METHODS](../04_thinking/04_thinking_representation_methods.md) | 证明树图（MaybeUninit、借用检查器、生命周期、Send/Sync 等） |

---

## 返回
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [形式化工程系统 README](./README.md)
- [文档中心](../README.md)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- [rust-formal-engineering-system 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **来源: [Wikipedia - Formal Methods](https://en.wikipedia.org/wiki/Formal_Methods)**
> **来源: [Coq Reference](https://coq.inria.fr/doc/)**
> **来源: [TLA+](https://lamport.azurewebsites.net/tla/tla.html)**
> **来源: [ACM - Formal Verification](https://dl.acm.org/)**
> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
> **来源: [IEEE](https://standards.ieee.org/)**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Iris Project](https://iris-project.org/)]**
>
> **[来源: [POPL/PLDI 论文](https://dblp.org/db/conf/pldi/index.html)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>
---
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
---
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
