# 国际化翻译版本差异检测与对齐指南

> **概念族**: 权威来源对齐 / 国际化 / i18n
> **内容分级**: [核心级]
> **层级**: L0-L1
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录

- [国际化翻译版本差异检测与对齐指南](#国际化翻译版本差异检测与对齐指南)
  - [目录](#目录)
  - [一、指南说明](#一指南说明)
  - [二、官方翻译版本现状](#二官方翻译版本现状)
  - [三、版本差异检测维度](#三版本差异检测维度)
  - [四、自动化检测方法](#四自动化检测方法)
    - [4.1 基于 GitHub API 的版本对比](#41-基于-github-api-的版本对比)
    - [4.2 基于文件哈希的章节一致性检查](#42-基于文件哈希的章节一致性检查)
    - [4.3 维护脚本](#43-维护脚本)
  - [五、关键术语翻译一致性](#五关键术语翻译一致性)
  - [六、差异处理流程](#六差异处理流程)
  - [七、未覆盖缺口](#七未覆盖缺口)
  - [相关概念](#相关概念)
  - [学术权威参考](#学术权威参考)
  - [社区权威参考](#社区权威参考)

---

## 一、指南说明

本文档建立 `docs/research_notes/` 中核心概念与国际化多语言权威来源之间的**版本差异检测机制**，确保中文、日文等翻译版本与英文原版保持同步，并识别因翻译滞后导致的知识偏差。

---

## 二、官方翻译版本现状

| 语言 | 来源 | 原版追踪 | 当前状态 | 项目映射 |
|------|------|----------|----------|----------|
| 中文 | [TRPL 中文版](https://kaisery.github.io/trpl-zh-cn/) | [rust-lang/book](https://github.com/rust-lang/book) | 🔄 通常滞后 1-3 个小版本 | [10_rust_book_alignment.md](10_rust_book_alignment.md) |
| 中文 | [Rust Reference 中文](https://rustwiki.org/zh-CN/reference/) | [rust-lang/reference](https://github.com/rust-lang/reference) | ⏳ 滞后较多 | [10_rust_reference_alignment.md](10_rust_reference_alignment.md) |
| 日文 | [TRPL 日本語版](https://doc.rust-jp.rs/book-ja/) | [rust-lang/book](https://github.com/rust-lang/book) | 🔄 滞后 1-2 个小版本 | [10_rust_book_alignment.md](10_rust_book_alignment.md) |
| 日文 | [Rust by Example 日本語版](https://doc.rust-jp.rs/rust-by-example-ja/) | [rust-lang/rust-by-example](https://github.com/rust-lang/rust-by-example) | ⏳ 部分章节未翻译 | [10_rust_by_example_alignment.md](10_rust_by_example_alignment.md) |

---

## 三、版本差异检测维度

| 维度 | 检测内容 | 项目响应 |
|------|----------|----------|
| 版本号 | 翻译仓库的 commit 与原版的 commit 差距 | 在 [10_authoritative_source_version_tracking.md](10_authoritative_source_version_tracking.md) 记录 |
| 章节增删 | 原版新增/删除/重排章节 | 同步调整对齐矩阵 |
| 代码示例 | 示例是否随原版更新 | 检查项目示例 crate |
| 术语变更 | 英文术语翻译一致性 | 更新多语言术语对照表 |
| 版本特性标注 | 翻译是否标注最低 Rust 版本 | 项目文档显式标注 `Rust 1.96.0+` |

---

## 四、自动化检测方法

### 4.1 基于 GitHub API 的版本对比

```bash
# 获取原版与翻译仓库的最新 release/tag
curl -s https://api.github.com/repos/rust-lang/book/releases/latest | jq .tag_name
curl -s https://api.github.com/repos/rust-lang-cn/book/releases/latest | jq .tag_name
```

### 4.2 基于文件哈希的章节一致性检查

```bash
# 对比原版与翻译的目录结构
diff <(ls en/src) <(ls zh-CN/src)
```

### 4.3 维护脚本

已提供 `scripts/maintenance/check_i18n_translation_gap.py`：

- 输入：各语言翻译仓库的 GitHub owner/repo、原版引用。
- 输出：版本差距报告（release tag、latest commit）。

运行方式：

```bash
python scripts/maintenance/check_i18n_translation_gap.py
```

术语一致性检查以 [`data/i18n_terminology.yaml`](../../data/i18n_terminology.yaml) 作为权威数据源，脚本可读取该文件并对照各语言翻译中的关键术语使用情况。该文件涵盖所有权、类型系统、并发安全、异步、包管理等核心概念，是检测术语偏差与未覆盖缺口的标准来源。

> 当前版本仅做版本号/最新 commit 差距检测，缺失章节与术语差异待后续扩展。

---

## 五、关键术语翻译一致性

| 英文术语 | 官方中文 | 官方日文 | 说明 |
|----------|----------|----------|------|
| Ownership | 所有权 | 所有権 | 已统一 |
| Borrowing | 借用 | 借用 | 已统一 |
| Lifetime | 生命周期 | ライフタイム | 避免直译为“寿命” |
| Trait | 特征 / Trait | トレイト | 中文保留英文更常见 |
| unsafe | unsafe / 不安全 | unsafe | 代码中保留英文 |
| Edition | 版本 / Edition | Edition | 注意与“版本号”区分 |
| crate | 包 / crate | クレート | 中文语境常用“crate” |

完整术语库见 [`data/i18n_terminology.yaml`](../../data/i18n_terminology.yaml)。该文件是本项目中所有 i18n 相关文档进行术语一致性检查的统一数据源，包含英文、中文、日文翻译及分类说明。文档在引用或讨论术语时应优先与该库保持一致。

> 亦见 [10_i18n_source_alignment.md](10_i18n_source_alignment.md) 中的多语言术语对照简表。

---

## 六、差异处理流程

```text
检测差异
   │
   ▼
评估影响（P0/P1/P2）
   │
   ▼
更新对应语言对齐文档
   │
   ▼
更新知识图谱索引与版本跟踪表
   │
   ▼
运行 check_research_notes.py 验证
```

---

## 七、未覆盖缺口

1. 尚未实现 `check_i18n_translation_gap.py` 自动化脚本。
2. 法语、德语、西班牙语等其他语言社区资源未建立版本跟踪。
3. 术语对照表未覆盖 variance、coercion、orphan rules 等高级术语。

> **权威来源**: [TRPL 中文](https://kaisery.github.io/trpl-zh-cn/) | [TRPL 日文](https://doc.rust-jp.rs/book-ja/) | [rust-lang/book](https://github.com/rust-lang/book) | [rust-lang-cn/book](https://github.com/rust-lang-cn/book) | [rust-jp/book](https://github.com/rust-jp/book)

## 相关概念

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [国际化多语言来源对齐](10_i18n_source_alignment.md)
- [权威来源版本跟踪](10_authoritative_source_version_tracking.md)
- [Rust Book 对齐](10_rust_book_alignment.md)
- [知识图谱索引](10_knowledge_graph_index.md)

---

## 学术权威参考

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)

## 社区权威参考

- [Rust Book 中文](https://kaisery.github.io/trpl-zh-cn/)
- [This Week in Rust](https://this-week-in-rust.org/)
