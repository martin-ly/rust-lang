# Formal Modules / 形式化模块系统 {#formal-modules-形式化模块系统}

> **EN**: Formal Modules
> **Summary**: 形式化模块系统 Formal Modules. (stub/archive redirect)
>
> **概念族**: 形式化模块
> **内容分级**: [核心级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 新建完成 / 权威国际化来源对齐完成

---

## 目录 {#目录}

- [Formal Modules / 形式化模块系统 {#formal-modules-形式化模块系统}](#formal-modules--形式化模块系统-formal-modules-形式化模块系统)
  - [目录 {#目录}](#目录-目录)
  - [研究目标 {#研究目标}](#研究目标-研究目标)
  - [当前内容 {#当前内容}](#当前内容-当前内容)
  - [计划补充内容 {#计划补充内容}](#计划补充内容-计划补充内容)
  - [权威来源 {#权威来源}](#权威来源-权威来源)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术/社区来源参考 {#学术社区来源参考}](#学术社区来源参考-学术社区来源参考)

---

## 研究目标 {#研究目标}

本目录聚焦于 **Rust 模块系统（modules / crates / visibility / linkage）** 的规范化定义与形式化语义，旨在：

1. 精确描述 Rust 模块系统的结构规则与可见性规则。
2. 建立模块系统与编译器内部表示（HIR / MIR）之间的对应关系。
3. 对照形式化验证生态（RustBelt、Aeneas、coq-of-rust 等）明确模块/封装边界在证明中的处理方式。
4. 为 crate 架构、API 设计、安全抽象边界提供理论支撑。

---

## 当前内容 {#当前内容}

| 文件 | 说明 | 状态 |
| :--- | :--- | :--- |
| [10_formalization_ecology_mindmap.md](10_formalization_ecology_mindmap.md) | Rust 形式化验证生态思维导图 | 已从 archive 迁回，待升级到 Rust 1.96+ |
| [10_module_system_specification.md](10_module_system_specification.md) | 模块系统规范：crate/module/path/use/visibility | ✅ 已完成 |
| [20_linkage_and_symbols.md](20_linkage_and_symbols.md) | Linkage、extern crate、crate-type、符号可见性 | ✅ 已完成 |
| [30_module_hir_mir_mapping.md](30_module_hir_mir_mapping.md) | 模块结构到 HIR / MIR 的映射 | ✅ 已完成 |
| [40_module_safety_abstraction.md](40_module_safety_abstraction.md) | 模块系统与安全抽象边界 | ✅ 已完成 |
| [50_formal_tools_module_mapping.md](50_formal_tools_module_mapping.md) | Aeneas / coq-of-rust / RustBelt 中的模块处理 | ✅ 已完成 |

---

## 计划补充内容 {#计划补充内容}

- [x] **模块系统规范梳理**：crate、module、path、use、visibility（`pub`、`pub(crate)`、`pub(super)`、`pub(in path)`）的完整规则。
- [x] **Linkage 与名称解析**：`extern crate`、crate-type、`#[no_mangle]`、符号可见性、链接时边界。
- [x] **HIR/MIR 对应**：模块结构如何降维到 HIR ItemTree、MIR 中的封装边界如何保持。
- [x] **模块系统与安全抽象**：可见性如何作为安全边界（safe/unsafe 接口封装、内部可变性抽象）。
- [x] **形式化工具映射**：Aeneas / coq-of-rust / RustBelt 中如何处理模块、crate、私有性。

---

> **权威来源**: [Rust Reference – Items and Modules](https://doc.rust-lang.org/reference/items.html) | [Rust Reference – Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html) | [The Rust Programming Language – Packages, Crates, and Modules](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html) | [rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/) | [Ferrocene Language Specification](https://spec.ferrocene.dev/) | [RustBelt](https://plv.mpi-sws.org/rustbelt/)

## 权威来源 {#权威来源}

---

## 相关概念 {#相关概念}

- [知识图谱索引](../10_knowledge_graph_index.md) — 模块系统在整个知识体系中的层级定位与关系边
- [跨文档映射网络](../10_cross_reference_index.md) — 层级-主题-文档三维矩阵
- [层次化梳理与映射总结](../10_hierarchical_mapping_and_summary.md) — 概念族↔文档↔定理映射
- [Rust Book 对齐](../10_rust_book_alignment.md) — TRPL Ch 7 模块系统映射
- [形式化方法索引](../formal_methods/)
- [研究笔记主索引](../README.md)
- [Crate 架构分析](../software_design_theory/07_crate_architectures/)

---

## 学术/社区来源参考 {#学术社区来源参考}

> **来源**: [RustBelt](https://plv.mpi-sws.org/rustbelt/)
> **来源**: [Aeneas](https://aeneas-verification.github.io/)
> **来源**: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)
