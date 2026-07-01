# 权威来源版本跟踪表 {#权威来源版本跟踪表}

> **概念族**: 权威来源对齐 / 版本跟踪
> **内容分级**: [核心级]
> **层级**: L0-L7
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [权威来源版本跟踪表 {#权威来源版本跟踪表}](#权威来源版本跟踪表-权威来源版本跟踪表)
  - [目录 {#目录}](#目录-目录)
  - [一、跟踪说明 {#一跟踪说明}](#一跟踪说明-一跟踪说明)
  - [二、P0 官方权威来源版本 {#二p0-官方权威来源版本}](#二p0-官方权威来源版本-二p0-官方权威来源版本)
  - [三、P1 学术权威来源版本 {#三p1-学术权威来源版本}](#三p1-学术权威来源版本-三p1-学术权威来源版本)
  - [四、P2 社区权威来源版本 {#四p2-社区权威来源版本}](#四p2-社区权威来源版本-四p2-社区权威来源版本)
  - [五、更新响应流程 {#五更新响应流程}](#五更新响应流程-五更新响应流程)
  - [六、自动化建议 {#六自动化建议}](#六自动化建议-六自动化建议)
  - [相关概念 {#相关概念}](#相关概念-相关概念)

---

## 一、跟踪说明 {#一跟踪说明}

本文档记录 `docs/research_notes/` 所引用的国际化权威来源的 **最后检查日期**、**版本/Edition** 和 **状态**，确保对齐网络与权威来源保持同步。

状态标记：

- ✅ 最新 — 已检查至当前 Rust 1.96.0+ / Edition 2024
- 🔄 需更新 — 权威来源有新版本，项目文档待同步
- ⏳ 待检查 — 尚未完成版本核对

---

## 二、P0 官方权威来源版本 {#二p0-官方权威来源版本}

| 权威来源 | URL | 版本/Edition | 最后检查 | 状态 |
|----------|-----|--------------|----------|------|
| The Rust Book | [Rust Book](https://doc.rust-lang.org/book/) | 2024 Edition, 1.96.0+ | 2026-06-29 | ✅ |
| Rust Reference | [Rust Reference](https://doc.rust-lang.org/reference/) | 1.96.0+ | 2026-06-29 | ✅ |
| Rustonomicon | [Rustonomicon](https://doc.rust-lang.org/nomicon/) | 1.96.0+ | 2026-06-29 | ✅ |
| Cargo Book | [Cargo Book](https://doc.rust-lang.org/cargo/) | 1.96.0+ | 2026-06-29 | ✅ |
| Rust Edition Guide | [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/) | 2024 Edition | 2026-06-29 | ✅ |
| Async Book | [Async Book](https://rust-lang.github.io/async-book/) | 1.96.0+ | 2026-06-29 | ✅ |
| Rust RFCs | [Rust RFCs](https://rust-lang.github.io/rfcs/) | 持续更新 | 2026-06-29 | ✅ |
| Standard Library | [Standard Library](https://doc.rust-lang.org/std/) | 1.96.0+ | 2026-06-29 | ✅ |
| Rust By Example | [Rust By Example](https://doc.rust-lang.org/rust-by-example/) | 1.96.0+ | 2026-06-29 | ✅ |
| Unsafe Code Guidelines | [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) | 持续更新 | 2026-06-29 | ✅ |
| Rust Error Codes | [Rust Error Codes](https://doc.rust-lang.org/error_codes/error-index.html) | 1.96.0+ | 2026-06-29 | ✅ |
| Ferrocene FLS | [Ferrocene FLS](https://spec.ferrocene.dev/) | 1.76+ (stable) | 2026-06-29 | ✅ |
| rustc-dev-guide | [rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/) | 1.96.0+ | 2026-06-29 | ✅ |

---

## 三、P1 学术权威来源版本 {#三p1-学术权威来源版本}

| 权威来源 | 机构 | 版本/年份 | 最后检查 | 状态 |
|----------|------|-----------|----------|------|
| RustBelt | MPI-SWS | POPL 2018 | 2026-06-29 | ✅ |
| Tree Borrows | ETH Zürich | PLDI 2025 | 2026-06-29 | ✅ |
| Stacked Borrows | MPI-SWS | 2018 | 2026-06-29 | ✅ |
| RustSEM | 多机构 | 2024 | 2026-06-29 | ✅ |
| Aeneas | EPFL | 持续更新 | 2026-06-29 | ✅ |
| coq-of-rust | Formal Land | 持续更新 | 2026-06-29 | ✅ |

---

## 四、P2 社区权威来源版本 {#四p2-社区权威来源版本}

| 权威来源 | 类型 | 最后检查 | 状态 |
|----------|------|----------|------|
| Rust API Guidelines | [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) | 2026-06-29 | ✅ |
| Rust Design Patterns | [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) | 2026-06-29 | ✅ |
| Rust Performance Book | [Rust Performance Book](https://nnethercote.github.io/perf-book/) | 2026-06-29 | ✅ |
| This Week in Rust | [This Week in Rust](https://this-week-in-rust.org/) | 2026-06-29 | ✅ 持续 |
| Inside Rust Blog | [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/) | 2026-06-29 | ✅ 持续 |

---

## 五、更新响应流程 {#五更新响应流程}

1. **监测**：每季度检查 Rust 官方博客、releases.rs、RFC 仓库。
2. **评估**：判断新版本/新 RFC 是否影响项目文档中的概念、反例或代码示例。
3. **更新**：在对应对齐文档中标记新版本，必要时更新反例或版本演进文件。
4. **验证**：运行 `check_research_notes.py` 确保链接和元数据一致。

---

## 六、自动化建议 {#六自动化建议}

可扩展 `check_research_notes.py` 实现：

- 解析每个对齐文档中的 URL。
- 通过 HTTP HEAD 请求检查 URL 可访问性（避免频繁调用）。
- 对比 `rustc --version` 输出与文档中声明的 Rust 版本。

> **权威来源**: [Rust Release Notes](https://releases.rs/) | [Rust Blog](https://blog.rust-lang.org/) | [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/) | [This Week in Rust](https://this-week-in-rust.org/)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [RFC 对齐索引](10_rfc_alignment_index.md)
- [版本演进边界与迁移反例](10_version_evolution_counterexamples.md)
- [知识图谱索引](10_knowledge_graph_index.md)

> **来源: [RustSEM: A Formal Semantics for Rust](https://link.springer.com/article/10.1007/s10703-024-00460-3)**

> **来源: [Aeneas Verification](https://aeneas-verification.github.io/)**
