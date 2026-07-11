# Rust RFC 对齐索引 {#rust-rfc-对齐索引}

> **EN**: Rfc Alignment Index
> **Summary**: Rust RFC 对齐索引 Rfc Alignment Index.
> **概念族**: 权威来源对齐 / RFC
> **内容分级**: [核心级]
> **层级**: L0-L7
> **Bloom 层级**: L5-L6
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [Rust RFC 对齐索引 {#rust-rfc-对齐索引}](#rust-rfc-对齐索引-rust-rfc-对齐索引)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、核心语言 RFC {#二核心语言-rfc}](#二核心语言-rfc-二核心语言-rfc)
  - [三、类型系统与 Trait RFC {#三类型系统与-trait-rfc}](#三类型系统与-trait-rfc-三类型系统与-trait-rfc)
  - [四、异步与并发 RFC {#四异步与并发-rfc}](#四异步与并发-rfc-四异步与并发-rfc)
  - [五、Edition 与版本 RFC {#五edition-与版本-rfc}](#五edition-与版本-rfc-五edition-与版本-rfc)
  - [六、工具链 RFC {#六工具链-rfc}](#六工具链-rfc-六工具链-rfc)
  - [七、未覆盖缺口 {#七未覆盖缺口}](#七未覆盖缺口-七未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、对齐说明 {#一对齐说明}

本文档将 `docs/research_notes/` 中的核心概念、设计决策与 [Rust RFCs](https://rust-lang.github.io/rfcs/) 建立映射。RFC 是 Rust 语言与工具链设计的权威记录。

---

## 二、核心语言 RFC {#二核心语言-rfc}

| RFC | 主题 | 项目文档 | 状态 |
|-----|------|----------|------|
| [RFC 1859](https://rust-lang.github.io/rfcs/2094-nll.html) — Non-Lexical Lifetimes | 借用（Borrowing）检查器改进 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | ✅ |
| [RFC 2094](https://rust-lang.github.io/rfcs/2094-nll.html) — NLL | 非词法生命周期（Lifetimes） | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | ✅ |
| [RFC 0380](https://rust-lang.github.io/rfcs/1184-stabilize-no_std.html) — `no_std` | 无 std 环境 | [crates/c13_embedded/](../../crates/c13_embedded/README.md) | ✅ |
| [RFC 1210](https://rust-lang.github.io/rfcs/1210-impl-specialization.html) — Specialization | Trait 特化 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | 🔄 |

---

## 三、类型系统与 Trait RFC {#三类型系统与-trait-rfc}

| RFC | 主题 | 项目文档 | 状态 |
|-----|------|----------|------|
| [RFC 0195](https://rust-lang.github.io/rfcs/0195-associated-items.html) — Associated Items | 关联类型/常量 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | ✅ |
| [RFC 0401](https://rust-lang.github.io/rfcs/0401-coercions.html) — Coercions | 类型强制 | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | 🔄 |
| [RFC 0738](https://rust-lang.github.io/rfcs/0738-variance.html) — Variance | 型变 | [type_theory/10_variance_theory.md](type_theory/10_variance_theory.md) | ✅ |
| [RFC 1598](https://rust-lang.github.io/rfcs/1598-generic_associated_types.html) — GATs | 泛型（Generics）关联类型 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | ✅ |
| [RFC 2289](https://rust-lang.github.io/rfcs/2289-associated-type-bounds.html) — Associated Type Bounds | 关联类型约束 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | ✅ |

---

## 四、异步与并发 RFC {#四异步与并发-rfc}

| RFC | 主题 | 项目文档 | 状态 |
|-----|------|----------|------|
| [RFC 2394](https://rust-lang.github.io/rfcs/2394-async_await.html) — async/await | 异步语法 | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | ✅ |
| [RFC 2418](https://rust-lang.github.io/rfcs/2394-async_await.html) / Async Drop（暂无合并 RFC，跟踪 issue [rust-lang/rust#126482](https://github.com/rust-lang/rust/issues/126482)） — Async Drop | 异步析构 | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §6 | ✅ |
| [RFC 2645 — transparent unions/enums](https://rust-lang.github.io/rfcs/2645-transparent-unions.html) | 透明布局类型 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | 🔄 |

---

## 五、Edition 与版本 RFC {#五edition-与版本-rfc}

| RFC | 主题 | 项目文档 | 状态 |
|-----|------|----------|------|
| [RFC 2052](https://rust-lang.github.io/rfcs/2052-epochs.html) — Epochs/Editions | Edition 机制 | [10_edition_guide_alignment.md](10_edition_guide_alignment.md) | ✅ |
| [RFC 3101 — Reserved Prefixes](https://rust-lang.github.io/rfcs/3101-reserved_prefixes.html) — Reserved Prefix | 保留前缀 | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §3 | ✅ |

---

## 六、工具链 RFC {#六工具链-rfc}

| RFC | 主题 | 项目文档 | 状态 |
|-----|------|----------|------|
| [RFC 2906](https://rust-lang.github.io/rfcs/2906-cargo-workspace-deduplicate.html) — Workspace Deduplicate | workspace 依赖去重 | [formal_modules/70_module_patterns_and_refactoring.md](formal_modules/70_module_patterns_and_refactoring.md) §5 | ✅ |
| [RFC 2957](https://rust-lang.github.io/rfcs/2957-cargo-features2.html) — Cargo Features 2.0 | feature resolver v2 | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §5 | ✅ |

---

## 七、未覆盖缺口 {#七未覆盖缺口}

1. 宏系统相关 RFC（如 `macro_rules!` hygiene、proc-macro）可进一步索引。
2. const 泛型（Generics）、const eval 相关 RFC 待随内容扩展补充。
3. Rust 1.97+ 新特性的 RFC 需持续跟踪。

> **权威来源**: [Rust RFCs](https://rust-lang.github.io/rfcs/)

## 相关概念 {#相关概念}

- [RFC 到反例自动化映射索引](10_rfc_to_counterexample_mapping.md)
- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [Rust Reference 对齐](10_rust_reference_alignment.md)
- [Edition Guide 对齐](10_edition_guide_alignment.md)
- [知识图谱索引](10_knowledge_graph_index.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneasverif.github.io/)

## 社区权威参考 {#社区权威参考}

- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [This Week in Rust](https://this-week-in-rust.org/)
