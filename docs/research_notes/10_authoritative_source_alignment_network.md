# 权威来源对齐网络总索引 {#权威来源对齐网络总索引}

> **EN**: Authoritative Source Alignment Network
> **Summary**: 权威来源对齐网络总索引 Authoritative Source Alignment Network.
> **概念族**: 权威来源对齐 / 索引
> **内容分级**: [核心级]
> **层级**: L0-L1
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 七、扩展对齐专题 {#七扩展对齐专题}

| 专题 | 对齐文档 | 说明 |
|------|----------|------|
| 设计模式 | [10_design_patterns_authoritative_alignment.md](10_design_patterns_authoritative_alignment.md) | GoF、Rust 惯用法、企业级模式、反模式 |
| 异步生态 | [10_async_ecosystem_alignment.md](10_async_ecosystem_alignment.md) | tokio、async-std、smol、axum、tonic 等生态 |
| 版本演进 | [10_version_evolution_alignment.md](10_version_evolution_alignment.md) | 官方发布、Edition、关键特性、不稳定特性追踪 |
| 性能与测试 | [10_performance_and_testing_alignment.md](10_performance_and_testing_alignment.md) | Rust Performance Book、Cargo 测试、Miri、Clippy、Criterion、Sanitizer |
| 行号级锚点 | [10_authoritative_source_line_anchors.md](10_authoritative_source_line_anchors.md) | 核心概念到权威来源 GitHub 行号级链接 |
| RFC 到反例映射 | [10_rfc_to_counterexample_mapping.md](10_rfc_to_counterexample_mapping.md) | 关键 RFC 与项目反例文档的双向映射 |
| 宏 / FFI / 嵌入式生态 | [10_macros_ffi_embedded_alignment.md](10_macros_ffi_embedded_alignment.md) | 宏系统、FFI、WebAssembly、嵌入式生态权威来源对齐 |
| 错误处理（Error Handling） / 网络 / Web | [10_error_handling_network_web_alignment.md](10_error_handling_network_web_alignment.md) | Rust Book Ch 9、std::result、thiserror/anyhow/eyre、tokio::net、hyper、tonic、axum、actix-web、rocket、tower、HTTP/1/2/3、WebSocket、OpenAPI 权威来源对齐 |
| 数据库、存储与云原生 | [10_database_storage_cloud_alignment.md](10_database_storage_cloud_alignment.md) | diesel、sqlx、sea-orm、rusqlite、redis、mongo、kafka、rabbitmq、nats、kube-rs、otel、prometheus、容器/K8s |
| CI/CD 与供应链安全 | [10_cicd_supply_chain_alignment.md](10_cicd_supply_chain_alignment.md) | GitHub Actions、GitLab CI、测试质量、供应链安全、发布签名 |
| 缺口与反向追溯 | [10_authoritative_source_gap_and_backref_index.md](10_authoritative_source_gap_and_backref_index.md) | 权威来源缺口分析、已建立/未建立反向追溯的权威来源、P0/P1/P2 补全优先级 |
| Crate 架构 | [10_crate_architecture_authoritative_alignment.md](10_crate_architecture_authoritative_alignment.md) | workspace、public/private API、feature、错误类型、日志、配置、CLI、库/二进制、MSRV |
| 学习路径与面试题 | [10_learning_and_interview_alignment.md](10_learning_and_interview_alignment.md) | 官方/社区学习资源、面试题与权威来源映射、Bloom 层级对应 |
| 自动补全计划 | [10_authoritative_source_completion_plan.md](10_authoritative_source_completion_plan.md) | 权威来源 P0/P1/P2 自动补全建议与覆盖率提升计划 |
| 100% 完成路线图 | [10_authoritative_source_100_percent_roadmap.md](10_authoritative_source_100_percent_roadmap.md) | P0/P1/P2 覆盖率 100% 目标、冲刺阶段、自动化工具与质量门禁 |

---

## 目录 {#目录}

- [权威来源对齐网络总索引 {#权威来源对齐网络总索引}](#权威来源对齐网络总索引-权威来源对齐网络总索引)
  - [七、扩展对齐专题 {#七扩展对齐专题}](#七扩展对齐专题-七扩展对齐专题)
  - [目录 {#目录}](#目录-目录)
  - [一、网络说明 {#一网络说明}](#一网络说明-一网络说明)
  - [二、P0 官方权威来源对齐 {#二p0-官方权威来源对齐}](#二p0-官方权威来源对齐-二p0-官方权威来源对齐)
  - [三、P1 学术权威来源对齐 {#三p1-学术权威来源对齐}](#三p1-学术权威来源对齐-三p1-学术权威来源对齐)
  - [四、P2 社区权威来源对齐 {#四p2-社区权威来源对齐}](#四p2-社区权威来源对齐-四p2-社区权威来源对齐)
  - [五、对齐维度与状态标记 {#五对齐维度与状态标记}](#五对齐维度与状态标记-五对齐维度与状态标记)
  - [六、维护与更新 {#六维护与更新}](#六维护与更新-六维护与更新)
  - [相关概念 {#相关概念}](#相关概念-相关概念)

---

## 一、网络说明 {#一网络说明}

本文档是 `docs/research_notes/` 的 **权威来源对齐网络总入口**。它将项目内所有研究笔记与国际化权威来源建立映射，确保：

- 每个核心概念都有可追溯的权威定义。
- 每个反例边界都有官方规范或学术文献支撑。
- 版本特性与官方发布说明、RFC、Edition Guide 保持一致。

对齐网络覆盖 **P0 官方权威**、**P1 学术权威**、**P2 社区权威** 三个层级。

---

## 二、P0 官方权威来源对齐 {#二p0-官方权威来源对齐}

| 权威来源 | 类型 | 对齐文档 | 覆盖主题 | 状态 |
|----------|------|----------|----------|------|
| [The Rust Programming Language](https://doc.rust-lang.org/book/) | 教程 | [10_rust_book_alignment.md](10_rust_book_alignment.md) | 所有权（Ownership）、类型系统（Type System）、并发、错误处理、宏、OOP 等 21 章 | ✅ 已完成 |
| [Rust Reference](https://doc.rust-lang.org/reference/) | 语言规范 | [10_rust_reference_alignment.md](10_rust_reference_alignment.md) / [10_rust_reference_chapters_alignment.md](10_rust_reference_chapters_alignment.md) | 词法、类型、表达式、items、modules、unsafe、attributes | ✅ 已完成 |
| [Rustonomicon](https://doc.rust-lang.org/nomicon/) | 高级/unsafe 指南 | [10_rustonomicon_alignment.md](10_rustonomicon_alignment.md) | 所有权、生命周期、子类型、Send/Sync、FFI、未初始化内存 | ✅ 已完成 |
| [Cargo Book](https://doc.rust-lang.org/cargo/) | 构建工具 | [10_cargo_book_alignment.md](10_cargo_book_alignment.md) | 依赖、workspace、features、crate-type、发布、配置 | ✅ 已完成 |
| [Toolchain Ecosystem](https://www.rust-lang.org/tools) | 工具链 | [10_toolchain_ecosystem_alignment.md](10_toolchain_ecosystem_alignment.md) | rustc、rustup、clippy、rustfmt、rust-analyzer、rustdoc | ✅ 已完成 |
| [Async Ecosystem](https://tokio.rs/) | 异步生态 | [10_async_ecosystem_alignment.md](10_async_ecosystem_alignment.md) | tokio、async-std、smol、futures、axum、tonic | ✅ 已完成 |
| [Version Evolution](https://blog.rust-lang.org/) | 版本演进 | [10_version_evolution_alignment.md](10_version_evolution_alignment.md) | 官方发布说明、Edition、关键特性版本映射 | ✅ 已完成 |
| [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/) | 版本迁移 | [10_edition_guide_alignment.md](10_edition_guide_alignment.md) | 2015/2018/2021/2024 Edition 差异与迁移 | ✅ 已完成 |
| [Async Book](https://rust-lang.github.io/async-book/) | 异步编程 | [10_async_book_alignment.md](10_async_book_alignment.md) | Future、async/await、Pin、执行器、IO | ✅ 已完成 |
| [Rust RFCs](https://rust-lang.github.io/rfcs/) | 设计提案 | [10_rfc_alignment_index.md](10_rfc_alignment_index.md) | 所有权、借用（Borrowing）、生命周期、async、Edition、语法糖 | ✅ 已完成 |
| [Standard Library](https://doc.rust-lang.org/std/) | API 文档 | [10_std_library_alignment.md](10_std_library_alignment.md) | 核心类型、trait、collections、sync、io | ✅ 已完成 |
| [Rust By Example](https://doc.rust-lang.org/rust-by-example/) | 交互式示例 | [10_rust_by_example_alignment.md](10_rust_by_example_alignment.md) | 基础概念、所有权、类型、并发、unsafe | ✅ 已完成 |
| [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) | unsafe 指南 | [10_unsafe_code_guidelines_alignment.md](10_unsafe_code_guidelines_alignment.md) | 内存模型、UB、类型布局、FFI | ✅ 已完成 |
| [Safety & Unsafe](https://doc.rust-lang.org/nomicon/) | 安全/unsafe | [10_safety_and_unsafe_authoritative_alignment.md](10_safety_and_unsafe_authoritative_alignment.md) | P0/P1/P2 安全与 unsafe 权威来源网络 | ✅ 已完成 |
| [Rust Error Codes](https://doc.rust-lang.org/error_codes/error-index.html) | 错误参考 | [10_rustc_errors_alignment.md](10_rustc_errors_alignment.md) | 所有权、类型、模块（Module）、并发错误码 | ✅ 已完成 |
| [Ferrocene Language Specification](https://spec.ferrocene.dev/) | 形式化规范 | [10_ferrocene_fls_alignment.md](10_ferrocene_fls_alignment.md) | 语义规范、安全关键认证 | ✅ 已完成 |
| [rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/) | 编译器开发 | [10_rustc_dev_guide_alignment.md](10_rustc_dev_guide_alignment.md) | HIR/MIR、名称解析、类型推断（Type Inference） | ✅ 已完成 |
| [Verification Tools [已失效]]<!-- 原链接: https://rust-lang.github.io/rust-formal-methods/ --> | 形式化工具 | [10_verification_tools_practical_alignment.md](10_verification_tools_practical_alignment.md) | Aeneas、coq-of-rust、Kani、Prusti、Creusot 实战映射 | ✅ 已完成 |
| [RFC Argumentation](https://rust-lang.github.io/rfcs/) | 设计论证 | [10_rfc_argumentation_chain.md](10_rfc_argumentation_chain.md) | 关键 RFC 的 Motivation→Design→Drawbacks 论证链 | ✅ 已完成 |
| [i18n Sources](https://rust-lang.org/) | 国际化资源 | [10_i18n_source_alignment.md](10_i18n_source_alignment.md) | 中/日/多语言官方翻译与社区资源 | ✅ 已完成 |
| [i18n Translation Gap](https://github.com/rust-lang/book) | 翻译差异检测 | [10_i18n_translation_gap_analysis.md](10_i18n_translation_gap_analysis.md) | 多语言翻译版本差异检测与对齐流程 | ✅ 已完成 |
| [Version Tracking](https://releases.rs/) | 版本跟踪 | [10_authoritative_source_version_tracking.md](10_authoritative_source_version_tracking.md) | 所有权威来源的最后检查日期与版本 | ✅ 已完成 |
| [RFC Tracking](https://rust-lang.github.io/rfcs/) | RFC 实现状态 | [10_rfc_tracking_status.md](10_rfc_tracking_status.md) | 关键 RFC 的 stable/in-progress/deprecated 状态 | ✅ 已完成 |

---

## 三、P1 学术权威来源对齐 {#三p1-学术权威来源对齐}

| 权威来源 | 机构 | 类型 | 对齐文档 | 覆盖主题 |
|----------|------|------|----------|----------|
| [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/) | MPI-SWS | 形式化证明 | [10_rustbelt_alignment.md](10_rustbelt_alignment.md) | 所有权、借用、Unsafe 语义 |
| [Aeneas](https://aeneas-verification.github.io/) | EPFL | 验证工具 | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) | 可验证的 Rust 子集 |
| [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3) | 多机构 | 操作语义 | [10_rustsem_semantics.md](10_rustsem_semantics.md) | Rust 操作语义 |
| [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html) | ETH Zürich | 借用模型 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | 别名模型改进 |
| [Stacked Borrows](https://plv.mpi-sws.org/rustbelt/) | MPI-SWS | 借用模型 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | 原始别名规则 |
| [IEEE/ACM/arXiv/Springer Academic Resources](https://dl.acm.org/) | 多机构 | 学术论文/工具综述 | [10_academic_papers_alignment.md](10_academic_papers_alignment.md) | POPL/PLDI/OOPSLA/ICFP 顶级会议、TOPLAS/JFP/FMSD 期刊、ACM DL/IEEE Xplore/Springer/arXiv 出版商 |

---

## 四、P2 社区权威来源对齐 {#四p2-社区权威来源对齐}

| 权威来源 | 类型 | 对齐文档 | 覆盖主题 | 状态 |
|----------|------|----------|----------|------|
| [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) | 最佳实践 | [10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) | API 设计、命名、SemVer、Future-proofing | ✅ 已完成 |
| [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) | 设计模式 | [10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) / [10_design_patterns_authoritative_alignment.md](10_design_patterns_authoritative_alignment.md) | 惯用法、GoF 模式、反模式 | ✅ 已完成 |
| [Rust Performance Book](https://nnethercote.github.io/perf-book/) | 性能优化 | [10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) / [10_performance_and_testing_alignment.md](10_performance_and_testing_alignment.md) | 基准测试、Profiling、优化技巧 | ✅ 已完成 |
| [This Week in Rust](https://this-week-in-rust.org/) | 社区周报 | — | 新版本特性、博客、RFC 进展 | ✅ 持续追踪 |
| [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/) | 官方博客 | — | 编译器、语言团队进展 | ✅ 持续追踪 |

---

## 五、对齐维度与状态标记 {#五对齐维度与状态标记}

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

## 六、维护与更新 {#六维护与更新}

- 每季度运行一次全量对齐审查。
- Rust 新版本发布后 2 周内更新对应对齐文档。
- 新增研究笔记时，必须在知识图谱索引中补充权威来源链接。

> **权威来源**: [Rust Official Docs](https://doc.rust-lang.org/) | [Rust Reference](https://doc.rust-lang.org/reference/) | [The Rust Programming Language](https://doc.rust-lang.org/book/) | [Rustonomicon](https://doc.rust-lang.org/nomicon/) | [Cargo Book](https://doc.rust-lang.org/cargo/) | [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)

## 相关概念 {#相关概念}

- [权威内容对齐指南](10_authoritative_alignment_guide.md)
- [知识图谱索引](10_knowledge_graph_index.md)
- [Rust Book 对齐](10_rust_book_alignment.md)
- [RustBelt 对齐](10_rustbelt_alignment.md)
- [国际形式化验证索引](10_international_formal_verification_index.md)
