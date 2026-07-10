# 国际化多语言权威来源对齐索引 {#国际化多语言权威来源对齐索引}

> **EN**: I18n Source Alignment
> **Summary**: 国际化多语言权威来源对齐索引 I18n Source Alignment.
> **概念族**: 权威来源对齐 / 国际化 / i18n
> **内容分级**: [核心级]
> **层级**: L0-L1
> **Bloom 层级**: L5-L6
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [国际化多语言权威来源对齐索引 {#国际化多语言权威来源对齐索引}](#国际化多语言权威来源对齐索引-国际化多语言权威来源对齐索引)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、中文权威来源 {#二中文权威来源}](#二中文权威来源-二中文权威来源)
  - [三、日文权威来源 {#三日文权威来源}](#三日文权威来源-三日文权威来源)
  - [四、其他语言来源 {#四其他语言来源}](#四其他语言来源-四其他语言来源)
  - [五、多语言术语对照 {#五多语言术语对照}](#五多语言术语对照-五多语言术语对照)
  - [六、术语库数据源 {#六术语库数据源}](#六术语库数据源-六术语库数据源)
  - [七、社区翻译贡献 {#七社区翻译贡献}](#七社区翻译贡献-七社区翻译贡献)
  - [八、未覆盖缺口 {#八未覆盖缺口}](#八未覆盖缺口-八未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、对齐说明 {#一对齐说明}

本文档将 `docs/research_notes/` 中的核心概念与国际化多语言权威来源建立映射，包括官方翻译、社区翻译和区域性学习资源。对齐目的：

- 为中文/日文等多语言学习者提供可追溯的权威参考。
- 统一关键术语的多语言表述，避免翻译歧义。
- 识别不同语言社区对同一概念的解释差异。

---

## 二、中文权威来源 {#二中文权威来源}

| 来源 | 类型 | 项目文档 | 覆盖主题 | 状态 |
|------|------|----------|----------|------|
| [Rust 程序设计语言 中文版](https://kaisery.github.io/trpl-zh-cn/) | 官方翻译 | [10_rust_book_alignment.md](10_rust_book_alignment.md) | TRPL 21 章中文翻译 | ✅ 已对齐 |
| [Rust Reference 中文翻译](https://rustwiki.org/zh-CN/reference/) | 社区翻译 | [10_rust_reference_alignment.md](10_rust_reference_alignment.md) | 语言规范 | 🔄 部分 |
| [Rust By Example 中文](https://rustwiki.org/zh-CN/rust-by-example/) | 社区翻译 | [10_rust_by_example_alignment.md](10_rust_by_example_alignment.md) | 交互式示例 | 🔄 部分 |
| [Rust 中文社区 [已失效]]<!-- 原链接: https://rustcc.cn/ --> | 社区论坛 | [10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) | 讨论、博客、招聘 | ✅ 持续 |
| [Rust 语言圣经](https://course.rs/) | 中文教程 | [10_learning_path_comprehensive.md](10_learning_path_comprehensive.md) | 中文学习路径 | ✅ 已索引 |

---

## 三、日文权威来源 {#三日文权威来源}

| 来源 | 类型 | 项目文档 | 覆盖主题 | 状态 |
|------|------|----------|----------|------|
| [The Rust Programming Language 日本語版](https://doc.rust-jp.rs/book-ja/) | 官方翻译 | [10_rust_book_alignment.md](10_rust_book_alignment.md) | TRPL 日文翻译 | ✅ 已对齐 |
| [Rust by Example 日本語版](https://doc.rust-jp.rs/rust-by-example-ja/) | 社区翻译 | [10_rust_by_example_alignment.md](10_rust_by_example_alignment.md) | 交互式示例 | 🔄 部分 |
| [Rust Japan Community](https://rust-jp.rs/) | 社区 | [10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) | 活动、资源 | ✅ 持续 |

---

## 四、其他语言来源 {#四其他语言来源}

| 语言 | 来源 | 类型 | 项目文档 | 状态 |
|------|------|------|----------|------|
| 法语 | [Rust FR](https://rust-fr.github.io/) | 社区 | [10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) | 🔄 待扩展 |
| 德语 | [Rust DE](https://rust-lang.de/) | 社区 | [10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) | 🔄 待扩展 |
| 西班牙语 | [Rust ES](https://rust-es.org/) | 社区 | [10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) | 🔄 待扩展 |
| 俄语 | [Rust RU](https://rust-lang.ru/) | 社区 | [10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) | 🔄 待扩展 |

---

## 五、多语言术语对照 {#五多语言术语对照}

| 英文术语 | 中文 | 日文 | 项目文档 |
|----------|------|------|----------|
| Ownership | 所有权 | 所有権 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) |
| Borrowing | 借用 | 借用 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) |
| Lifetime | 生命周期（Lifetimes） | ライフタイム | [type_theory/10_lifetime_formalization.md](type_theory/10_lifetime_formalization.md) |
| Trait | 特征 / Trait | トレイト | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) |
| unsafe | 不安全 / unsafe | unsafe | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) |
| async/await | 异步/等待 | 非同期/待機 | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) |
| Pin | 固定 / Pin | 固定/Pin | [formal_methods/10_pin_self_referential.md](formal_methods/10_pin_self_referential.md) |
| crate | 包 / crate | クレート | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) |

## 六、术语库数据源 {#六术语库数据源}

完整术语库存放于 [`data/i18n_terminology.yaml`](../../data/i18n_terminology.yaml)，采用 YAML 结构化格式，包含每个术语的英文原文、中文翻译、日文翻译、分类及使用说明。

引用（Reference）方式：

- 在 Markdown 文档中提及本术语库时，使用相对路径 `data/i18n_terminology.yaml` 或链接 `[术语库](data/i18n_terminology.yaml)`。
- 维护脚本可通过 `PROJECT_ROOT / "data" / "i18n_terminology.yaml"` 读取并解析该文件。
- 新增术语时应同步更新该文件，并优先保证与上表一致。

---

## 七、社区翻译贡献 {#七社区翻译贡献}

- 官方翻译仓库：[rust-lang/book](https://github.com/rust-lang/book)、[rust-lang/reference](https://github.com/rust-lang/reference)
- 中文社区翻译：[rust-lang-cn](https://github.com/rust-lang-cn)
- 日文社区翻译：[rust-jp](https://github.com/rust-jp)

---

## 八、未覆盖缺口 {#八未覆盖缺口}

1. 中文 Rust Reference 翻译与项目 Reference 对齐矩阵可进一步细化。
2. ~~日文/中文术语对照表可扩展至更多专业术语（如 variance、coercion、orphan rules）。~~ 已补充：高级术语已统一纳入 [`data/i18n_terminology.yaml`](../../data/i18n_terminology.yaml)。
3. 可建立自动化脚本检查各语言翻译版本与英文原版的版本差异。

> **权威来源**: [TRPL 中文](https://kaisery.github.io/trpl-zh-cn/) | [TRPL 日文](https://doc.rust-jp.rs/book-ja/) | [Rust 中文社区 [已失效]]<!-- 原链接: https://rustcc.cn/ --> | [Rust Japan](https://rust-jp.rs/)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [Rust Book 对齐](10_rust_book_alignment.md)
- [综合学习路径](10_learning_path_comprehensive.md)
- [知识图谱索引](10_knowledge_graph_index.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)

## 社区权威参考 {#社区权威参考}

- [Rust Book 中文](https://kaisery.github.io/trpl-zh-cn/)
- [This Week in Rust](https://this-week-in-rust.org/)
