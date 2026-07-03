# 权威来源缺口与反向追溯索引 {#权威来源缺口与反向追溯索引}

> **EN**: Authoritative Source Gap And Backref Index
> **Summary**: 权威来源缺口与反向追溯索引 Authoritative Source Gap And Backref Index.
> **概念族**: 权威来源对齐 / 缺口分析 / 反向追溯
>
> **内容分级**: [核心级]
>
> **分级**: [A]
> **层级**: L0-L7
> **Bloom 层级**: L5-L6
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: ✅ 已完成
>
> **用途**: 建立从权威来源章节到项目文档的反向追溯索引，识别仍未建立对齐的缺口，并给出 P0/P1/P2 优先级补全建议。
>
> **权威来源**:
>
> [Rust Reference](https://doc.rust-lang.org/reference/) |
> [The Rust Programming Language](https://doc.rust-lang.org/book/) |
> [Rustonomicon](https://doc.rust-lang.org/nomicon/) |
> [Rust RFCs](https://rust-lang.github.io/rfcs/) |
> [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) |
> [RustBelt](https://plv.mpi-sws.org/rustbelt/) |
> [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html) |
> [RustSEM](https://rustsem.github.io/)

---

## 📑 目录 {#目录}

- [权威来源缺口与反向追溯索引 {#权威来源缺口与反向追溯索引}](#权威来源缺口与反向追溯索引-权威来源缺口与反向追溯索引)
  - [📑 目录 {#目录}](#-目录-目录)
  - [一、反向追溯机制说明 {#一反向追溯机制说明}](#一反向追溯机制说明-一反向追溯机制说明)
  - [二、已建立反向追溯的权威来源 {#二已建立反向追溯的权威来源}](#二已建立反向追溯的权威来源-二已建立反向追溯的权威来源)
    - [2.1 P0 官方来源 {#21-p0-官方来源}](#21-p0-官方来源-21-p0-官方来源)
    - [2.2 P1 学术/形式化来源 {#22-p1-学术形式化来源}](#22-p1-学术形式化来源-22-p1-学术形式化来源)
    - [2.3 P2 社区/生态来源 {#23-p2-社区生态来源}](#23-p2-社区生态来源-23-p2-社区生态来源)
  - [三、尚未建立对齐的缺口 {#三尚未建立对齐的缺口}](#三尚未建立对齐的缺口-三尚未建立对齐的缺口)
    - [3.1 Rust Reference 缺口 {#31-rust-reference-缺口}](#31-rust-reference-缺口-31-rust-reference-缺口)
    - [3.2 Rust By Example 缺口 {#32-rust-by-example-缺口}](#32-rust-by-example-缺口-32-rust-by-example-缺口)
    - [3.3 学术论文与形式化证明缺口 {#33-学术论文与形式化证明缺口}](#33-学术论文与形式化证明缺口-33-学术论文与形式化证明缺口)
    - [3.4 社区与生态来源缺口 {#34-社区与生态来源缺口}](#34-社区与生态来源缺口-34-社区与生态来源缺口)
  - [四、补全优先级 {#四补全优先级}](#四补全优先级-四补全优先级)
    - [P0：下一季度必须完成 {#p0下一季度必须完成}](#p0下一季度必须完成-p0下一季度必须完成)
    - [P1：半年内完成 {#p1半年内完成}](#p1半年内完成-p1半年内完成)
    - [P2：一年内完成 {#p2一年内完成}](#p2一年内完成-p2一年内完成)
  - [五、项目文档映射 {#五项目文档映射}](#五项目文档映射-五项目文档映射)
  - [六、维护清单 {#六维护清单}](#六维护清单-六维护清单)
  - [相关概念 {#相关概念}](#相关概念-相关概念)

---

## 一、反向追溯机制说明 {#一反向追溯机制说明}

反向追溯（back-reference）是权威来源对齐网络的双向链路：

- **正向链路**：从项目概念/文档出发，引用权威来源的章节、行号或论文，证明项目表述有据可依。
- **反向链路**：从权威来源的某个章节/论文/示例出发，能够反向检索到项目内对应的文档、反例、代码示例或证明。

本索引负责记录和维护反向链路，确保：

1. 每个权威来源的关键章节至少对应一个项目文档。
2. 每个项目文档的关键缺口都能在权威来源侧找到待补章节。
3. 维护者可以按 P0/P1/P2 优先级批量补全缺口。

> **自动化支撑**：`scripts/maintenance/check_authoritative_source_gaps.py` 定期扫描 `docs/research_notes/` 下 Markdown 文件，按概念族统计权威 URL 覆盖比例，并输出缺口报告。

---

## 二、已建立反向追溯的权威来源 {#二已建立反向追溯的权威来源}

### 2.1 P0 官方来源 {#21-p0-官方来源}

| 权威来源 | 关键章节/入口 | 项目文档 |
|----------|--------------|----------|
| [The Rust Programming Language](https://doc.rust-lang.org/book/) | 21 章全章节 | [10_rust_book_alignment.md](10_rust_book_alignment.md) |
| [Rust Reference](https://doc.rust-lang.org/reference/) | 词法、类型、表达式、items、modules、unsafe、attributes | [10_rust_reference_alignment.md](10_rust_reference_alignment.md)、[10_rust_reference_chapters_alignment.md](10_rust_reference_chapters_alignment.md) |
| [Rustonomicon](https://doc.rust-lang.org/nomicon/) | 所有权、类型布局、并发、未初始化内存、FFI | [10_rustonomicon_alignment.md](10_rustonomicon_alignment.md) |
| [Cargo Book](https://doc.rust-lang.org/cargo/) | package、依赖、workspace、features、build、发布 | [10_cargo_book_alignment.md](10_cargo_book_alignment.md) |
| [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/) | 2015/2018/2021/2024 Edition 差异 | [10_edition_guide_alignment.md](10_edition_guide_alignment.md) |
| [Async Book](https://rust-lang.github.io/async-book/) | Future、Pin、执行器、Waker、IO | [10_async_book_alignment.md](10_async_book_alignment.md) |
| [Rust RFCs](https://rust-lang.github.io/rfcs/) | 所有权、借用、生命周期、async、Edition、语法糖 | [10_rfc_alignment_index.md](10_rfc_alignment_index.md)、[10_rfc_argumentation_chain.md](10_rfc_argumentation_chain.md) |
| [Standard Library](https://doc.rust-lang.org/std/) | 核心类型、trait、collections、sync、io | [10_std_library_alignment.md](10_std_library_alignment.md) |
| [Rust By Example](https://doc.rust-lang.org/rust-by-example/) | 基础概念、所有权、类型、并发、unsafe | [10_rust_by_example_alignment.md](10_rust_by_example_alignment.md) |
| [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) | 内存模型、UB、类型布局、FFI、并发 | [10_unsafe_code_guidelines_alignment.md](10_unsafe_code_guidelines_alignment.md) |
| [Rust Error Codes](https://doc.rust-lang.org/error_codes/error-index.html) | 所有权、类型、模块、并发、unsafe 错误码 | [10_rustc_errors_alignment.md](10_rustc_errors_alignment.md) |
| [Ferrocene Language Specification](https://spec.ferrocene.dev/) | 语义规范、安全关键认证 | [10_ferrocene_fls_alignment.md](10_ferrocene_fls_alignment.md) |
| [rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/) | HIR/MIR、名称解析、类型推断、借用检查 | [10_rustc_dev_guide_alignment.md](10_rustc_dev_guide_alignment.md) |

### 2.2 P1 学术/形式化来源 {#22-p1-学术形式化来源}

| 权威来源 | 机构/作者 | 项目文档 |
|----------|----------|----------|
| [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/) | MPI-SWS | [10_rustbelt_alignment.md](10_rustbelt_alignment.md) |
| [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html) | ETH Zürich / Ralf Jung | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md)、[10_rustsem_semantics.md](10_rustsem_semantics.md) |
| [Stacked Borrows](https://plv.mpi-sws.org/rustbos/) | MPI-SWS | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) |
| [Oxide](https://arxiv.org/abs/1903.00982) | Aaron Weiss 等 | [type_theory/10_lifetime_formalization.md](type_theory/10_lifetime_formalization.md)、[type_theory/10_variance_theory.md](type_theory/10_variance_theory.md) |
| [Aeneas](https://arxiv.org/abs/2207.09467) | EPFL | [10_aeneas_integration_plan.md](10_aeneas_integration_plan.md)、[10_international_formal_verification_index.md](10_international_formal_verification_index.md) |
| [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3) | 多机构 | [10_rustsem_semantics.md](10_rustsem_semantics.md) |
| [IEEE/ACM/arXiv/Springer 学术资源](https://dl.acm.org/) | 多机构 | [10_academic_papers_alignment.md](10_academic_papers_alignment.md) |

### 2.3 P2 社区/生态来源 {#23-p2-社区生态来源}

| 权威来源 | 类型 | 项目文档 |
|----------|------|----------|
| [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) | 最佳实践 | [10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) |
| [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) | 设计模式 | [10_design_patterns_authoritative_alignment.md](10_design_patterns_authoritative_alignment.md)、[10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) |
| [Rust Performance Book](https://nnethercote.github.io/perf-book/) | 性能优化 | [10_performance_and_testing_alignment.md](10_performance_and_testing_alignment.md)、[10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) |
| [This Week in Rust](https://this-week-in-rust.org/) | 社区周报 | 持续追踪，尚未建立固定反向索引 |
| [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/) | 官方博客 | 持续追踪，尚未建立固定反向索引 |

---

## 三、尚未建立对齐的缺口 {#三尚未建立对齐的缺口}

### 3.1 Rust Reference 缺口 {#31-rust-reference-缺口}

| Reference 章节 | 当前覆盖 | 缺口说明 | 建议项目文档 |
|----------------|----------|----------|--------------|
| [const 求值](https://doc.rust-lang.org/reference/const_eval.html) | 少量提及 | 缺少 const 求值规则、 promotability、`const fn` 边界到项目反例的反向索引 | [10_const_eval_formalization.md](10_const_eval_formalization.md) |
| [宏 hygiene](https://doc.rust-lang.org/reference/macros-by-example.html#hygiene) | `10_macro_system.md` | 缺少 hygiene 示例与 `$crate` 到项目宏示例的反向索引 | [crates/c11_macro_system_proc/README.md](../../crates/c11_macro_system_proc/README.md) |
| [模式匹配细节](https://doc.rust-lang.org/reference/patterns.html) | 分散 | 缺少 refutability、match ergonomics、bindings 到项目文档的反向索引 | [10_core_features_full_chain.md](10_core_features_full_chain.md) |
| [链接与 crate-type](https://doc.rust-lang.org/reference/linkage.html) | [formal_modules/20_linkage_and_symbols.md](formal_modules/20_linkage_and_symbols.md) | 缺少 `dylib`/`staticlib`/`cdylib` 安全契约的精确反向索引 | [formal_modules/20_linkage_and_symbols.md](formal_modules/20_linkage_and_symbols.md) |

### 3.2 Rust By Example 缺口 {#32-rust-by-example-缺口}

| RBE 章节 | 当前覆盖 | 缺口说明 | 建议项目文档 |
|----------|----------|----------|--------------|
| [Testing](https://doc.rust-lang.org/rust-by-example/testing.html) | 未系统对齐 | 单元测试、集成测试、文档测试与项目测试策略未建立反向索引 | [formal_methods/10_testing_strategy_decision_tree.md](formal_methods/10_testing_strategy_decision_tree.md) |
| [Std Library Types](https://doc.rust-lang.org/rust-by-example/std.html) | 未系统对齐 | `HashMap`、`VecDeque`、`Rc`/`Arc` 示例未映射到项目 std 对齐文档 | [10_std_library_alignment.md](10_std_library_alignment.md) |
| [Crates](https://doc.rust-lang.org/rust-by-example/crates.html) | 未系统对齐 | crate 类型、模块树与项目 crate 架构文档未建立反向索引 | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) |

### 3.3 学术论文与形式化证明缺口 {#33-学术论文与形式化证明缺口}

| 论文/工具 | 当前覆盖 | 缺口说明 | 优先级 |
|-----------|----------|----------|--------|
| RustBelt 具体定理 | [10_rustbelt_alignment.md](10_rustbelt_alignment.md) | 论文定理与项目证明树（`10_proof_tree_ownership.md`、`10_proof_tree_borrow.md`）的逐项映射不完整 | P1 |
| Tree Borrows 精确反例 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | `MaybeUninit`、raw pointer、two-phase borrow 等边界未精确到反例行号 | P1 |
| Aeneas async / trait 支持 | [10_aeneas_integration_plan.md](10_aeneas_integration_plan.md) | async、泛型 trait 证明边界尚未对齐 | P2 |
| coq-of-rust 证明脚本 | [10_coq_of_rust_integration_plan.md](10_coq_of_rust_integration_plan.md) | 缺少具体 Coq 证明脚本与项目定理映射 | P2 |
| Oxide 独立章节 | 引用多处 | 无独立文档，需创建 `type_theory/10_oxide_formalization.md` | P1 |

### 3.4 社区与生态来源缺口 {#34-社区与生态来源缺口}

| 来源 | 当前覆盖 | 缺口说明 | 优先级 |
|------|----------|----------|--------|
| API Guidelines – Ergonomic / Flexibility | [10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) | 部分章节仅列出标题，缺少项目示例反向索引 | P2 |
| Rust Design Patterns – Structural / Concurrency Patterns | [10_design_patterns_authoritative_alignment.md](10_design_patterns_authoritative_alignment.md) | 结构型与并发模式覆盖弱于惯用法和反模式 | P2 |
| Rust Performance Book – SIMD / Cache / Inlining | [10_performance_and_testing_alignment.md](10_performance_and_testing_alignment.md) | 高级性能主题缺少项目实验文档反向索引 | P2 |
| This Week in Rust / Inside Rust Blog | — | 无固定索引，仅作为持续追踪来源 | P2 |

---

## 四、补全优先级 {#四补全优先级}

### P0：下一季度必须完成 {#p0下一季度必须完成}

1. **Rust Reference 核心缺口**：补齐 `const` 求值、宏 hygiene、模式匹配细节到项目文档的反向索引。
2. **unsafe / 借用 / 类型核心安全**：更新 Tree Borrows 默认模型，补充 `MaybeUninit`、raw pointer 边界反例。
3. **RustBelt 核心定理映射**：将 RustBelt 所有权/借用定理映射到 `10_proof_tree_ownership.md`、`10_proof_tree_borrow.md`。
4. **形式化工具 1.96 兼容性**：更新 Kani、Miri、Tree Borrows、RustBelt 对 Rust 1.96 / 2024 Edition 的支持状态。

### P1：半年内完成 {#p1半年内完成}

1. **学术论文精确映射**：补齐 Tree Borrows、Oxide、Aeneas 到项目反例和证明树的逐项映射。
2. **Rust Reference 进阶章节**：链接、crate-type、visibility、name resolution 反向索引。
3. **Rust By Example 系统对齐**：建立 Testing、Std Library Types、Crates 与项目文档的反向索引。
4. **Oxide 独立形式化文档**：创建 `type_theory/10_oxide_formalization.md`，与生命周期/方差文档交叉引用。

### P2：一年内完成 {#p2一年内完成}

1. **社区来源增强**：API Guidelines、Rust Design Patterns 结构型/并发模式、Rust Performance Book SIMD/Cache 章节。
2. **博客与周报固定索引**：为 This Week in Rust、Inside Rust Blog 建立季度归档反向索引。
3. **多语言同步**：为 P0 缺口补充英文摘要，便于国际形式化社区对齐。

---

## 五、项目文档映射 {#五项目文档映射}

| 本文档主题 | 关联项目文档 | 说明 |
|------------|--------------|------|
| 缺口矩阵 | [10_authoritative_alignment_gap_matrix.md](10_authoritative_alignment_gap_matrix.md) | 主题 → 来源 → 缺口 → 优先级 → 建议动作 |
| 缺口分析 | [10_authoritative_alignment_gap_analysis.md](10_authoritative_alignment_gap_analysis.md) | 按来源层级和主题域的系统缺口分析 |
| 对齐网络总索引 | [10_authoritative_source_alignment_network.md](10_authoritative_source_alignment_network.md) | P0/P1/P2 权威来源总览与对齐文档入口 |
| 知识图谱索引 | [10_knowledge_graph_index.md](10_knowledge_graph_index.md) | L0-L7 概念节点、关系边、文档锚点 |
| 行号级锚点 | [10_authoritative_source_line_anchors.md](10_authoritative_source_line_anchors.md) | 核心概念到权威来源 GitHub 行号级链接 |
| RFC 到反例映射 | [10_rfc_to_counterexample_mapping.md](10_rfc_to_counterexample_mapping.md) | 关键 RFC 与项目反例的双向映射 |
| 版本跟踪 | [10_authoritative_source_version_tracking.md](10_authoritative_source_version_tracking.md) | 权威来源最后检查日期与版本 |
| 学术资源索引 | [10_academic_papers_alignment.md](10_academic_papers_alignment.md) | IEEE/ACM/arXiv/Springer 学术资源映射 |
| 形式化验证索引 | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) | RustBelt、Aeneas、coq-of-rust 等工具对标 |

---

## 六、维护清单 {#六维护清单}

- [ ] 每季度运行 `scripts/maintenance/check_authoritative_source_gaps.py`，更新本索引的缺口状态。
- [ ] Rust 新版本发布后 2 周内，检查 P0 来源是否新增或变更章节，并更新反向索引。
- [ ] 新增研究笔记时，确保其概念族元信息与权威来源链接符合 [10_authoritative_alignment_guide.md](10_authoritative_alignment_guide.md) 规范。
- [ ] 每个 P0 缺口必须对应一个 issue 或任务项；P1/P2 缺口纳入季度计划。
- [ ] 保持本文件与 [10_authoritative_alignment_gap_matrix.md](10_authoritative_alignment_gap_matrix.md)、[10_knowledge_graph_index.md](10_knowledge_graph_index.md) 的同步，避免重复或矛盾。

> **权威来源**: [Rust Official Docs](https://doc.rust-lang.org/) | [Rust RFCs](https://rust-lang.github.io/rfcs/) | [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) | [RustBelt](https://plv.mpi-sws.org/rustbelt/) | [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [权威来源对齐缺口矩阵](10_authoritative_alignment_gap_matrix.md)
- [权威来源对齐缺口分析](10_authoritative_alignment_gap_analysis.md)
- [权威来源行号锚点索引](10_authoritative_source_line_anchors.md)
- [权威来源版本跟踪表](10_authoritative_source_version_tracking.md)
- [知识图谱索引](10_knowledge_graph_index.md)
- [RFC 到反例映射](10_rfc_to_counterexample_mapping.md)
- [学术资源对齐索引](10_academic_papers_alignment.md)
- [国际形式化验证对标索引](10_international_formal_verification_index.md)
