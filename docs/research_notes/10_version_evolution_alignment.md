# 版本演进权威来源对齐矩阵 {#版本演进权威来源对齐矩阵}

> **EN**: Version Evolution Alignment
> **Summary**: 版本演进权威来源对齐矩阵 Version Evolution Alignment.
> **概念族**: 权威来源对齐 / 版本演进
> **内容分级**: [核心级]
> **层级**: L0-L5
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [版本演进权威来源对齐矩阵 {#版本演进权威来源对齐矩阵}](#版本演进权威来源对齐矩阵-版本演进权威来源对齐矩阵)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、官方版本发布说明 {#二官方版本发布说明}](#二官方版本发布说明-二官方版本发布说明)
  - [三、Edition 演进 {#三edition-演进}](#三edition-演进-三edition-演进)
  - [四、关键特性版本映射 {#四关键特性版本映射}](#四关键特性版本映射-四关键特性版本映射)
  - [五、不稳定/待稳定特性 {#五不稳定待稳定特性}](#五不稳定待稳定特性-五不稳定待稳定特性)
  - [六、与项目文档的映射 {#六与项目文档的映射}](#六与项目文档的映射-六与项目文档的映射)
  - [七、未覆盖缺口 {#七未覆盖缺口}](#七未覆盖缺口-七未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)

---

## 一、对齐说明 {#一对齐说明}

本文档将 `docs/research_notes/` 中的版本演进内容与 Rust 官方版本发布说明、Edition Guide、RFC、GitHub 里程碑建立映射，确保每个版本化特性都能追溯到官方发布记录。

---

## 二、官方版本发布说明 {#二官方版本发布说明}

| 版本范围 | 官方链接 | 项目文档 |
|----------|----------|----------|
| Rust 1.96 | <https://blog.rust-lang.org/2025/12/04/Rust-1.96.1.html> | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) |
| Rust 1.85 (Rust 2024) | <https://blog.rust-lang.org/2025/02/20/Rust-1.85.0.html> | [10_edition_guide_alignment.md](10_edition_guide_alignment.md) |
| Rust 1.81 | <https://blog.rust-lang.org/2024/09/05/Rust-1.81.0.html> | [60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §11 (move closure) |
| Rust 1.80 | <https://blog.rust-lang.org/2024/07/25/Rust-1.80.0.html> | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §2 |
| Rust 1.79 | <https://blog.rust-lang.org/2024/06/13/Rust-1.79.0.html> | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §2 |
| Rust 1.75 | <https://blog.rust-lang.org/2023/12/28/Rust-1.75.0.html> | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) (async fn in trait) |

---

## 三、Edition 演进 {#三edition-演进}

| Edition | 官方指南 | 项目文档 | 核心变化 |
|---------|----------|----------|----------|
| Rust 2024 | [Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2024/index.html) | [10_edition_guide_alignment.md](10_edition_guide_alignment.md) | gen keyword、tail expr temp scope、unsafe extern |
| Rust 2021 | [Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2021/index.html) | [10_edition_guide_alignment.md](10_edition_guide_alignment.md) | 预留字、闭包捕获、panic macro |
| Rust 2018 | [Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2018/index.html) | [10_edition_guide_alignment.md](10_edition_guide_alignment.md) | module system、NLL、async/await |

---

## 四、关键特性版本映射 {#四关键特性版本映射}

| 特性 | 引入版本 | 官方来源 | 项目文档 |
|------|----------|----------|----------|
| async/await | 1.39 | [Rust 1.39](https://blog.rust-lang.org/2019/11/07/Rust-1.39.0.html) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) |
| const generics | 1.51 | [Rust 1.51](https://blog.rust-lang.org/2021/03/25/Rust-1.51.0.html) | [type_theory/10_construction_capability.md](type_theory/10_construction_capability.md) |
| GATs | 1.65 | [Rust 1.65](https://blog.rust-lang.org/2022/11/03/Rust-1.65.0.html) | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) |
| let-else | 1.65 | [Rust 1.65](https://blog.rust-lang.org/2022/11/03/Rust-1.65.0.html) | [10_rust_book_alignment.md](10_rust_book_alignment.md) |
| RPITIT | 1.75 | [Rust 1.75](https://blog.rust-lang.org/2023/12/28/Rust-1.75.0.html) | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) |
| async fn in trait | 1.75 | [Rust 1.75](https://blog.rust-lang.org/2023/12/28/Rust-1.75.0.html) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) |
| `gen` blocks | 1.95 (nightly) | [RFC 3516](https://rust-lang.github.io/rfcs/3516-gen-blocks.html) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §3 |
| unsafe extern blocks | 1.82 | [Rust 1.82](https://blog.rust-lang.org/2024/10/17/Rust-1.82.0.html) | [10_edition_guide_alignment.md](10_edition_guide_alignment.md) §5 |

---

## 五、不稳定/待稳定特性 {#五不稳定待稳定特性}

| 特性 | 追踪 issue | 状态 | 项目文档 |
|------|------------|------|----------|
| gen blocks | [rust-lang/rust#117078](https://github.com/rust-lang/rust/issues/117078) | 实验中 | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §3 |
| associated type defaults | [rust-lang/rust#29661](https://github.com/rust-lang/rust/issues/29661) | 不稳定 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) |
| specialization | [rust-lang/rust#31844](https://github.com/rust-lang/rust/issues/31844) | 部分稳定 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) |
| never type `!` | [rust-lang/rust#35121](https://github.com/rust-lang/rust/issues/35121) | 稳定中 | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) |

---

## 六、与项目文档的映射 {#六与项目文档的映射}

| 项目文档 | 覆盖内容 | 权威来源 |
|----------|----------|----------|
| [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) | 版本迁移反例、keyword、MSRV | 官方博客、Edition Guide |
| [10_edition_guide_alignment.md](10_edition_guide_alignment.md) | Rust 2024/2021/2018 全部变化 | Edition Guide |
| [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | async 稳定历史 | 官方博客 |
| [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | GAT、specialization | 官方博客、Tracking issues |

---

## 七、未覆盖缺口 {#七未覆盖缺口}

1. 自动生成“每个研究笔记的最后验证版本”脚本。
2. Rust 1.97+ 新特性的预对齐。
3. 各 crate 生态的版本兼容性映射。

> **权威来源**: [Rust Release Blog](https://blog.rust-lang.org/) | [Edition Guide](https://doc.rust-lang.org/edition-guide/) | [Rust GitHub](https://github.com/rust-lang/rust) | [Rustup Changelog](https://github.com/rust-lang/rustup/blob/master/CHANGELOG.md)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [版本演进反例](10_version_evolution_counterexamples.md)
- [Edition Guide 对齐](10_edition_guide_alignment.md)
- [RFC 实现状态追踪](10_rfc_tracking_status.md)
- [知识图谱索引](10_knowledge_graph_index.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)
