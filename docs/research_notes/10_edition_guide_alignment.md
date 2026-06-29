# Rust Edition Guide 对齐矩阵

> **概念族**: 权威来源对齐 / Edition Guide
> **内容分级**: [核心级]
> **层级**: L7
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录

- [Rust Edition Guide 对齐矩阵](#rust-edition-guide-对齐矩阵)
  - [目录](#目录)
  - [一、对齐说明](#一对齐说明)
  - [二、Edition 2018](#二edition-2018)
  - [三、Edition 2021](#三edition-2021)
  - [四、Edition 2024](#四edition-2024)
  - [五、迁移工具与流程](#五迁移工具与流程)
  - [六、版本特性与知识图谱映射](#六版本特性与知识图谱映射)
  - [七、未覆盖缺口](#七未覆盖缺口)

---

## 一、对齐说明

本文档将 `docs/research_notes/` 中版本演进、迁移反例与 [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/) 建立映射，重点覆盖 2018、2021、2024 三个 Edition 的关键变更。

---

## 二、Edition 2018

| Edition Guide 章节 | 项目文档 | 状态 | 备注 |
|--------------------|----------|------|------|
| [Module System Changes](https://doc.rust-lang.org/edition-guide/rust-2018/module-system/index.html) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §4 | ✅ | `use` 路径绝对化 |
| [Path Changes](https://doc.rust-lang.org/edition-guide/rust-2018/path-changes.html) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §4-§5 | ✅ | `crate::`、`extern crate` |
| [Ownership Changes](https://doc.rust-lang.org/edition-guide/rust-2018/ownership-and-lifetimes/index.html) | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | ✅ | NLL |

---

## 三、Edition 2021

| Edition Guide 章节 | 项目文档 | 状态 | 备注 |
|--------------------|----------|------|------|
| [Default trait method available](https://doc.rust-lang.org/edition-guide/rust-2021/index.html) | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | ✅ | trait 系统演进 |
| [Panic Macro Consistency](https://doc.rust-lang.org/edition-guide/rust-2021/panic-macro-consistency.html) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §7 | 🔄 | 弃用警告处理 |
| [Reserving Syntax](https://doc.rust-lang.org/edition-guide/rust-2021/reserving-syntax.html) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §3 | ✅ | `gen` 关键字 |

---

## 四、Edition 2024

| Edition Guide 章节 | 项目文档 | 状态 | 备注 |
|--------------------|----------|------|------|
| [Tail Expr Drop Order](https://doc.rust-lang.org/edition-guide/rust-2024/tail-expr-drop-order.html) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §1 | ✅ | drop 顺序变化 |
| [unsafe_op_in_unsafe_fn](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-op-in-unsafe-fn.html) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §2 | ✅ | unsafe 块要求 |
| [Match Ergonomics](https://doc.rust-lang.org/edition-guide/rust-2024/match-ergonomics.html) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §4 | ✅ | match 临时值作用域 |
| [Gen Blocks](https://doc.rust-lang.org/edition-guide/rust-2024/gen-blocks.html) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §3 | ✅ | `gen` 关键字保留 |

---

## 五、迁移工具与流程

| Edition Guide 章节 | 项目文档 | 状态 | 备注 |
|--------------------|----------|------|------|
| [Editions](https://doc.rust-lang.org/edition-guide/editions/index.html) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §6 | ✅ | Edition 混用 |
| [Migration](https://doc.rust-lang.org/edition-guide/editions/transitioning-an-existing-project-to-a-new-edition.html) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) | ✅ | `cargo fix --edition` |

---

## 六、版本特性与知识图谱映射

| L7 节点 | Edition Guide 锚点 | 项目反例/说明 |
|---------|-------------------|---------------|
| Edition 2018 `use` 绝对路径 | [Path Changes](https://doc.rust-lang.org/edition-guide/rust-2018/path-changes.html) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §4 |
| Edition 2024 drop order | [Tail Expr Drop Order](https://doc.rust-lang.org/edition-guide/rust-2024/tail-expr-drop-order.html) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §1 |
| Edition 2024 unsafe lint | [unsafe_op_in_unsafe_fn](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-op-in-unsafe-fn.html) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §2 |

---

## 七、未覆盖缺口

1. 2024 Edition 的 `if let` / `while let` 临时作用域变化可进一步细化。
2. `cargo fix` 自动迁移的边界案例可补充示例。
3. 未来 Rust 1.97+ Edition 预览特性需持续跟踪。

> **权威来源**: [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)

## 相关概念

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [版本演进边界与迁移反例](10_version_evolution_counterexamples.md)
- [Rust Reference 对齐](10_rust_reference_alignment.md)
- [知识图谱索引](10_knowledge_graph_index.md)
