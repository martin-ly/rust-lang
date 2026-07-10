# RFC 实现状态追踪表 {#rfc-实现状态追踪表}

> **EN**: Rfc Tracking Status
> **Summary**: RFC 实现状态追踪表 Rfc Tracking Status.
> **概念族**: 权威来源对齐 / RFC / 版本跟踪
> **内容分级**: [核心级]
> **层级**: L0-L7
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [RFC 实现状态追踪表 {#rfc-实现状态追踪表}](#rfc-实现状态追踪表-rfc-实现状态追踪表)
  - [目录 {#目录}](#目录-目录)
  - [一、追踪说明 {#一追踪说明}](#一追踪说明-一追踪说明)
  - [二、已稳定 RFC {#二已稳定-rfc}](#二已稳定-rfc-二已稳定-rfc)
  - [三、实现中 RFC {#三实现中-rfc}](#三实现中-rfc-三实现中-rfc)
  - [四、已废弃/替代 RFC {#四已废弃替代-rfc}](#四已废弃替代-rfc-四已废弃替代-rfc)
  - [五、对项目文档的影响 {#五对项目文档的影响}](#五对项目文档的影响-五对项目文档的影响)
  - [六、未覆盖缺口 {#六未覆盖缺口}](#六未覆盖缺口-六未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、追踪说明 {#一追踪说明}

本文档追踪与 `docs/research_notes/` 知识体系相关的 Rust RFC 的 **实现状态**（stable / in-progress / deprecated），帮助维护者判断哪些 RFC 需要在版本演进或对齐文档中更新。

状态标记：

- ✅ Stable — 已稳定并可在当前 Rust 1.97.0+ 中使用
- 🔄 In Progress — 已实现部分，或有预览特性
- ❌ Deprecated — 被后续 RFC 替代或废弃

---

## 二、已稳定 RFC {#二已稳定-rfc}

| RFC | 主题 | 稳定版本 | 项目文档 | 状态 |
|-----|------|----------|----------|------|
| RFC 1859 | Non-Lexical Lifetimes | 1.31 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | ✅ |
| RFC 2094 | NLL 完整实现 | 1.63 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | ✅ |
| RFC 0738 | Variance | 1.0+ | [type_theory/10_variance_theory.md](type_theory/10_variance_theory.md) | ✅ |
| RFC 0195 | Associated Items | 1.0+ | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | ✅ |
| RFC 1598 | Generic Associated Types | 1.65 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | ✅ |
| RFC 2394 | async/await | 1.39 | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | ✅ |
| RFC 2052 | Epochs/Editions | 1.31 | [10_edition_guide_alignment.md](10_edition_guide_alignment.md) | ✅ |
| RFC 2957 | Cargo Features 2.0 | 1.51 | [10_cargo_book_alignment.md](10_cargo_book_alignment.md) | ✅ |
| RFC 2906 | Workspace Deduplicate | 1.64 | [10_cargo_book_alignment.md](10_cargo_book_alignment.md) | ✅ |
| RFC 3101 | Reserved Prefix | 1.86+ | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) | ✅ |

---

## 三、实现中 RFC {#三实现中-rfc}

| RFC | 主题 | 当前状态 | 项目文档 | 备注 |
|-----|------|----------|----------|------|
| RFC 1210 | Specialization | 部分实现 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | `min_specialization`  nightly |
| RFC 3185 | Async Drop | 设计中 | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §6 | 尚未稳定 |
| RFC 3516 | Gen Blocks | 不稳定 | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §3 | `gen` 关键字保留 |
| RFC 3627 | Maybe Dangling | 讨论中 | [type_theory/10_lifetime_formalization.md](type_theory/10_lifetime_formalization.md) | 未来可能影响生命周期（Lifetimes） |

---

## 四、已废弃/替代 RFC {#四已废弃替代-rfc}

| RFC | 主题 | 状态 | 替代 | 项目文档 |
|-----|------|------|------|----------|
| RFC 2418 | Remove async fn | 废弃 | RFC 2394 已稳定 | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) |

---

## 五、对项目文档的影响 {#五对项目文档的影响}

| 影响类型 | RFC 示例 | 项目响应 |
|----------|----------|----------|
| 新概念引入 | RFC 2394 async/await | 创建异步状态机文档 |
| 现有概念变化 | RFC 3101 保留前缀 | 更新版本演进反例 |
| 工具链变化 | RFC 2957 Features 2.0 | 更新 Cargo 对齐矩阵 |
| 未来特性 | RFC 3185 Async Drop | 在反例中标记为待稳定 |

---

## 六、未覆盖缺口 {#六未覆盖缺口}

1. 需要建立与 RFC 仓库的自动同步，检测新合并 RFC。
2. 每个 RFC 的「项目响应」字段可进一步细化到具体文件行号。
3. Rust 1.97+ 预览特性需持续补充。

> **权威来源**: [Rust RFCs](https://rust-lang.github.io/rfcs/) | [Rust RFC Repository](https://github.com/rust-lang/rfcs) | [Rust Tracking Issues](https://github.com/rust-lang/rust/labels/C-tracking-issue)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [RFC 对齐索引](10_rfc_alignment_index.md)
- [RFC 到反例自动化映射索引](10_rfc_to_counterexample_mapping.md)
- [RFC 深度论证链](10_rfc_argumentation_chain.md)
- [版本演进边界与迁移反例](10_version_evolution_counterexamples.md)
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
