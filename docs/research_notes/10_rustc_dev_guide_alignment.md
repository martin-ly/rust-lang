# rustc-dev-guide 对齐矩阵 {#rustc-dev-guide-对齐矩阵}

> **概念族**: 权威来源对齐 / rustc-dev-guide
> **内容分级**: [核心级]
> **层级**: L0-L4
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [rustc-dev-guide 对齐矩阵](#rustc-dev-guide-对齐矩阵)
  - [目录](#目录)
  - [一、对齐说明](#一对齐说明)
  - [二、编译流程概览](#二编译流程概览)
  - [三、名称解析](#三名称解析)
  - [四、类型推断](#四类型推断)
  - [五、借用检查](#五借用检查)
  - [六、HIR / MIR](#六hir-mir)
  - [七、Async 与状态机](#七async-与状态机)
  - [八、未覆盖缺口](#八未覆盖缺口)
  - [相关概念](#相关概念)
  - [学术权威参考](#学术权威参考)
  - [社区权威参考](#社区权威参考)

---

## 一、对齐说明 {#一对齐说明}

[rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/) 是 Rust 编译器实现者的权威参考。本文档将 `docs/research_notes/` 中的实现机制分析与 rustc-dev-guide 的编译器内部章节建立映射。

---

## 二、编译流程概览 {#二编译流程概览}

| rustc-dev-guide 章节 | 项目文档 | 状态 | 备注 |
|----------------------|----------|------|------|
| [Overview](https://rustc-dev-guide.rust-lang.org/overview.html) | [10_formal_full_model_overview.md](10_formal_full_model_overview.md) | ✅ | 编译流程与形式化模型总览 |
| [Compiler Source](https://rustc-dev-guide.rust-lang.org/compiler-src.html) | [software_design_theory/07_crate_architectures/](../software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) | 🔄 | rustc 自身架构可后续扩展 |

---

## 三、名称解析 {#三名称解析}

| rustc-dev-guide 章节 | 项目文档 | 状态 | 备注 |
|----------------------|----------|------|------|
| [Name Resolution](https://rustc-dev-guide.rust-lang.org/name-resolution.html) | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) | ✅ | 模块系统与名称解析 |
| [Modules and Source Files](https://rustc-dev-guide.rust-lang.org/modules.html) | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) | ✅ | crate/module/path 规则 |

---

## 四、类型推断 {#四类型推断}

| rustc-dev-guide 章节 | 项目文档 | 状态 | 备注 |
|----------------------|----------|------|------|
| [Type Inference](https://rustc-dev-guide.rust-lang.org/type-inference.html) | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | ✅ | 类型系统基础 |
| [Trait Solving](https://rustc-dev-guide.rust-lang.org/traits/resolution.html) | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | ✅ | trait 系统形式化 |

---

## 五、借用检查 {#五借用检查}

| rustc-dev-guide 章节 | 项目文档 | 状态 | 备注 |
|----------------------|----------|------|------|
| [Borrow Checker](https://rustc-dev-guide.rust-lang.org/borrow_check.html) | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | ✅ | 借用检查器证明 |
| [Region Inference](https://rustc-dev-guide.rust-lang.org/borrow_check/region_inference.html) | [type_theory/10_lifetime_formalization.md](type_theory/10_lifetime_formalization.md) | ✅ | 生命周期推断 |
| [MIR Borrow Check](https://rustc-dev-guide.rust-lang.org/borrow_check.html) | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | ✅ | NLL / Polonius |

---

## 六、HIR / MIR {#六hir-mir}

| rustc-dev-guide 章节 | 项目文档 | 状态 | 备注 |
|----------------------|----------|------|------|
| [High-level IR (HIR)](https://rustc-dev-guide.rust-lang.org/hir.html) | [formal_modules/30_module_hir_mir_mapping.md](formal_modules/30_module_hir_mir_mapping.md) | ✅ | 模块结构到 HIR 映射 |
| [MIR](https://rustc-dev-guide.rust-lang.org/mir/index.html) | [formal_modules/30_module_hir_mir_mapping.md](formal_modules/30_module_hir_mir_mapping.md) | ✅ | 模块结构到 MIR 映射 |
| [Codegen](https://rustc-dev-guide.rust-lang.org/backend/index.html) | [formal_modules/20_linkage_and_symbols.md](formal_modules/20_linkage_and_symbols.md) | 🔄 | 链接与符号 |

---

## 七、Async 与状态机 {#七async-与状态机}

| rustc-dev-guide 章节 | 项目文档 | 状态 | 备注 |
|----------------------|----------|------|------|
| [Async/Await Lowering](https://rustc-dev-guide.rust-lang.org/query/async_await.html) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | ✅ | async 状态机展开 |
| [Generator / Async Fn in Traits](https://rustc-dev-guide.rust-lang.org/traits/async-fn-in-trait.html) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | 🔄 | async trait 实现机制 |

---

## 八、未覆盖缺口 {#八未覆盖缺口}

1. 宏展开与 hygiene 的 rustc 实现章节可进一步对齐。
2. 增量编译、查询系统（query system）可补充工程层文档。
3. 编译器诊断与错误码生成可关联到各反例文件的编译器错误。

> **权威来源**: [rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [Rust Reference 对齐](10_rust_reference_alignment.md)
- [模块系统规范](formal_modules/10_module_system_specification.md)
- [模块 HIR/MIR 映射](formal_modules/30_module_hir_mir_mapping.md)
- [知识图谱索引](10_knowledge_graph_index.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)

## 社区权威参考 {#社区权威参考}

- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [This Week in Rust](https://this-week-in-rust.org/)