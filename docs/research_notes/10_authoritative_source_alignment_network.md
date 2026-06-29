# 权威来源对齐网络总索引

> **概念族**: 权威来源对齐 / 索引
> **内容分级**: [核心级]
> **层级**: L0-L1
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录

- [权威来源对齐网络总索引](#权威来源对齐网络总索引)
  - [目录](#目录)
  - [一、网络说明](#一网络说明)
  - [二、P0 官方权威来源对齐](#二p0-官方权威来源对齐)
  - [三、P1 学术权威来源对齐](#三p1-学术权威来源对齐)
  - [四、P2 社区权威来源对齐](#四p2-社区权威来源对齐)
  - [五、对齐维度与状态标记](#五对齐维度与状态标记)
  - [六、维护与更新](#六维护与更新)

---

## 一、网络说明

本文档是 `docs/research_notes/` 的 **权威来源对齐网络总入口**。它将项目内所有研究笔记与国际化权威来源建立映射，确保：

- 每个核心概念都有可追溯的权威定义。
- 每个反例边界都有官方规范或学术文献支撑。
- 版本特性与官方发布说明、RFC、Edition Guide 保持一致。

对齐网络覆盖 **P0 官方权威**、**P1 学术权威**、**P2 社区权威** 三个层级。

---

## 二、P0 官方权威来源对齐

| 权威来源 | 类型 | 对齐文档 | 覆盖主题 | 状态 |
|----------|------|----------|----------|------|
| [The Rust Programming Language](https://doc.rust-lang.org/book/) | 教程 | [10_rust_book_alignment.md](10_rust_book_alignment.md) | 所有权、类型系统、并发、错误处理、宏、OOP 等 21 章 | ✅ 已完成 |
| [Rust Reference](https://doc.rust-lang.org/reference/) | 语言规范 | [10_rust_reference_alignment.md](10_rust_reference_alignment.md) | 词法、类型、表达式、items、modules、unsafe、attributes | ✅ 已完成 |
| [Rustonomicon](https://doc.rust-lang.org/nomicon/) | 高级/unsafe 指南 | [10_rustonomicon_alignment.md](10_rustonomicon_alignment.md) | 所有权、生命周期、子类型、Send/Sync、FFI、未初始化内存 | ✅ 已完成 |
| [Cargo Book](https://doc.rust-lang.org/cargo/) | 构建工具 | [10_cargo_book_alignment.md](10_cargo_book_alignment.md) | 依赖、workspace、features、crate-type、发布、配置 | ✅ 已完成 |
| [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/) | 版本迁移 | [10_edition_guide_alignment.md](10_edition_guide_alignment.md) | 2015/2018/2021/2024 Edition 差异与迁移 | ✅ 已完成 |
| [Async Book](https://rust-lang.github.io/async-book/) | 异步编程 | [10_async_book_alignment.md](10_async_book_alignment.md) | Future、async/await、Pin、执行器、IO | ✅ 已完成 |
| [Rust RFCs](https://rust-lang.github.io/rfcs/) | 设计提案 | [10_rfc_alignment_index.md](10_rfc_alignment_index.md) | 所有权、借用、生命周期、async、Edition、语法糖 | ✅ 已完成 |
| [Standard Library](https://doc.rust-lang.org/std/) | API 文档 | 各主题文档内嵌链接 | 核心类型、trait、collections、sync、io | ✅ 持续 |
| [Ferrocene Language Specification](https://spec.ferrocene.dev/) | 形式化规范 | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) | 语义规范、安全关键认证 | ✅ 已索引 |
| [rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/) | 编译器开发 | [formal_modules/](formal_modules/README.md) / [type_theory/](type_theory/README.md) | HIR/MIR、名称解析、类型推断 | ✅ 已索引 |

---

## 三、P1 学术权威来源对齐

| 权威来源 | 机构 | 类型 | 对齐文档 | 覆盖主题 |
|----------|------|------|----------|----------|
| [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/) | MPI-SWS | 形式化证明 | [10_rustbelt_alignment.md](10_rustbelt_alignment.md) | 所有权、借用、Unsafe 语义 |
| [Aeneas](https://aeneas-verification.github.io/) | EPFL | 验证工具 | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) | 可验证的 Rust 子集 |
| [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3) | 多机构 | 操作语义 | [10_rustsem_semantics.md](10_rustsem_semantics.md) | Rust 操作语义 |
| [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html) | ETH Zürich | 借用模型 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | 别名模型改进 |
| [Stacked Borrows](https://plv.mpi-sws.org/rustbos/) | MPI-SWS | 借用模型 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | 原始别名规则 |

---

## 四、P2 社区权威来源对齐

| 权威来源 | 类型 | 覆盖主题 | 状态 |
|----------|------|----------|------|
| [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) | 最佳实践 | API 设计、命名、SemVer、Future-proofing | ✅ 已索引 |
| [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) | 设计模式 | 惯用法、反模式、idioms | ✅ 已索引 |
| [Rust Performance Book](https://nnethercote.github.io/perf-book/) | 性能优化 | 基准测试、Profiling、优化技巧 | ✅ 已索引 |
| [This Week in Rust](https://this-week-in-rust.org/) | 社区周报 | 新版本特性、博客、RFC 进展 | ✅ 持续追踪 |
| [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/) | 官方博客 | 编译器、语言团队进展 | ✅ 持续追踪 |

---

## 五、对齐维度与状态标记

每个对齐文档至少覆盖以下维度：

1. **概念定义对齐** — 项目定义与权威来源是否一致。
2. **代码示例对齐** — 示例是否可运行且符合官方 API。
3. **版本特性对齐** — 是否标注最低 Rust 版本 / Edition。
4. **差异说明** — 若项目表述与来源有差异，需显式论证。
5. **反向追溯** — 从权威来源章节可反向找到项目文档。

状态标记：

- ✅ 已对齐 — 内容与权威来源一致，且已检查。
- 🔄 部分对齐 — 部分内容已对齐，仍有缺口。
- ⏳ 待对齐 — 已规划但未完成。
- ⚠️ 存在差异 — 项目表述与权威来源不同，需论证。

---

## 六、维护与更新

- 每季度运行一次全量对齐审查。
- Rust 新版本发布后 2 周内更新对应对齐文档。
- 新增研究笔记时，必须在知识图谱索引中补充权威来源链接。

> **权威来源**: [Rust Official Docs](https://doc.rust-lang.org/) | [Rust Reference](https://doc.rust-lang.org/reference/) | [The Rust Programming Language](https://doc.rust-lang.org/book/) | [Rustonomicon](https://doc.rust-lang.org/nomicon/) | [Cargo Book](https://doc.rust-lang.org/cargo/) | [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)

## 相关概念

- [权威内容对齐指南](10_authoritative_alignment_guide.md)
- [知识图谱索引](10_knowledge_graph_index.md)
- [Rust Book 对齐](10_rust_book_alignment.md)
- [RustBelt 对齐](10_rustbelt_alignment.md)
- [国际形式化验证索引](10_international_formal_verification_index.md)
