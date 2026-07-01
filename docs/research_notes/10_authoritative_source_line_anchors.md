# 权威来源行号锚点索引 {#权威来源行号锚点索引}

> **概念族**: 权威来源对齐 / 行号锚点
> **内容分级**: [核心级]
> **层级**: L0-L7
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29
> **权威来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/) | [Rust Reference](https://doc.rust-lang.org/reference/) | [Rustonomicon](https://doc.rust-lang.org/nomicon/) | [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) | [Rust RFCs](https://rust-lang.github.io/rfcs/)

---

## 目录 {#目录}

- [权威来源行号锚点索引 {#权威来源行号锚点索引}](#权威来源行号锚点索引-权威来源行号锚点索引)
  - [目录 {#目录}](#目录-目录)
  - [一、索引说明 {#一索引说明}](#一索引说明-一索引说明)
  - [二、The Rust Programming Language {#二the-rust-programming-language}](#二the-rust-programming-language-二the-rust-programming-language)
  - [三、Rust Reference {#三rust-reference}](#三rust-reference-三rust-reference)
  - [四、Rustonomicon {#四rustonomicon}](#四rustonomicon-四rustonomicon)
  - [五、Unsafe Code Guidelines {#五unsafe-code-guidelines}](#五unsafe-code-guidelines-五unsafe-code-guidelines)
  - [六、RFCs {#六rfcs}](#六rfcs-六rfcs)
  - [七、未覆盖缺口 {#七未覆盖缺口}](#七未覆盖缺口-七未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、索引说明 {#一索引说明}

本文档为项目核心概念建立到国际化权威来源的**行号级 GitHub 锚点**，每个条目给出：概念名称、权威来源、精确到行号的 `blob/main/...#L` 链接，以及对应的本项目文档。行号基于各权威仓库当前 `main`/`master` 分支的最新源码结构；若后续源码重构导致行号偏移，可结合 [10_authoritative_source_version_tracking.md](10_authoritative_source_version_tracking.md) 进行版本校验。

---

## 二、The Rust Programming Language {#二the-rust-programming-language}

| 概念 | 权威来源 | 行号锚点链接 | 对应项目文档 |
|------|----------|--------------|--------------|
| 所有权（Ownership） | TRPL ch04-01 | [`src/ch04-01-what-is-ownership.md#L1`](https://github.com/rust-lang/book/blob/main/src/ch04-01-what-is-ownership.md#L1) | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) |
| 所有权规则 / 变量作用域示例 | TRPL ch04-01 Listing 4-1 | [`src/ch04-01-what-is-ownership.md#L108`](https://github.com/rust-lang/book/blob/main/src/ch04-01-what-is-ownership.md#L108) | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) |
| 泛型函数与类型参数 | TRPL ch10-01 Listing 10-4 | [`src/ch10-01-syntax.md#L21`](https://github.com/rust-lang/book/blob/main/src/ch10-01-syntax.md#L21) | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) |
| Trait 定义与共享行为 | TRPL ch10-02 Listing 10-12 | [`src/ch10-02-traits.md#L37`](https://github.com/rust-lang/book/blob/main/src/ch10-02-traits.md#L37) | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) |
| 生命周期标注与约束 | TRPL ch10-03 Listing 10-18 | [`src/ch10-03-lifetime-syntax.md#L94`](https://github.com/rust-lang/book/blob/main/src/ch10-03-lifetime-syntax.md#L94) | [type_theory/10_lifetime_formalization.md](type_theory/10_lifetime_formalization.md) |
| `Box<T>` 与堆分配 | TRPL ch15-01 Listing 15-1 | [`src/ch15-01-box.md#L43`](https://github.com/rust-lang/book/blob/main/src/ch15-01-box.md#L43) | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) |
| 线程创建 `thread::spawn` | TRPL ch16-01 Listing 16-1 | [`src/ch16-01-threads.md#L45`](https://github.com/rust-lang/book/blob/main/src/ch16-01-threads.md#L45) | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) |

---

## 三、Rust Reference {#三rust-reference}

| 概念 | 权威来源 | 行号锚点链接 | 对应项目文档 |
|------|----------|--------------|--------------|
| 内存分配与生命周期（所有权语义基础） | Rust Reference | [`src/memory-allocation-and-lifetime.md#L2`](https://github.com/rust-lang/reference/blob/master/src/memory-allocation-and-lifetime.md#L2) | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) |
| 借用检查与生命周期 | Rust Reference – Memory Model | [`src/memory-model.md#L2`](https://github.com/rust-lang/reference/blob/master/src/memory-model.md#L2) | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) |
| Unsafe 操作清单 | Rust Reference – Unsafety | [`src/unsafety.md#L2`](https://github.com/rust-lang/reference/blob/master/src/unsafety.md#L2) | [10_safe_unsafe_comprehensive_analysis.md](10_safe_unsafe_comprehensive_analysis.md) |
| Unsafe 操作列表项 | Rust Reference – Unsafety | [`src/unsafety.md#L7`](https://github.com/rust-lang/reference/blob/master/src/unsafety.md#L7) | [10_safe_unsafe_comprehensive_analysis.md](10_safe_unsafe_comprehensive_analysis.md) |

---

## 四、Rustonomicon {#四rustonomicon}

| 概念 | 权威来源 | 行号锚点链接 | 对应项目文档 |
|------|----------|--------------|--------------|
| `Send` / `Sync` 语义 | Rustonomicon | [`src/send-and-sync.md#L1`](https://github.com/rust-lang/nomicon/blob/master/src/send-and-sync.md#L1) | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) |
| `Send` / `Sync` 示例代码 | Rustonomicon | [`src/send-and-sync.md#L46`](https://github.com/rust-lang/nomicon/blob/master/src/send-and-sync.md#L46) | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) |
| 未定义行为（UB）清单 | Rustonomicon – What Unsafe Rust Can Do | [`src/what-unsafe-does.md#L1`](https://github.com/rust-lang/nomicon/blob/master/src/what-unsafe-does.md#L1) | [10_safe_unsafe_comprehensive_analysis.md](10_safe_unsafe_comprehensive_analysis.md) |
| UB 具体条目 | Rustonomicon – What Unsafe Rust Can Do | [`src/what-unsafe-does.md#L9`](https://github.com/rust-lang/nomicon/blob/master/src/what-unsafe-does.md#L9) | [10_safe_unsafe_comprehensive_analysis.md](10_safe_unsafe_comprehensive_analysis.md) |

---

## 五、Unsafe Code Guidelines {#五unsafe-code-guidelines}

| 概念 | 权威来源 | 行号锚点链接 | 对应项目文档 |
|------|----------|--------------|--------------|
| Tree Borrows 模型 | UCG WIP | [`wip/tree-borrows.md#L1`](https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/tree-borrows.md#L1) | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) |
| Tree Borrows 与 Stacked Borrows 差异 | UCG WIP | [`wip/tree-borrows.md#L20`](https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/tree-borrows.md#L20) | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) |
| 数据类型有效性要求（Validity Invariants） | UCG Active Discussion | [`active_discussion/validity.md#L1`](https://github.com/rust-lang/unsafe-code-guidelines/blob/master/active_discussion/validity.md#L1) | [10_safe_unsafe_comprehensive_analysis.md](10_safe_unsafe_comprehensive_analysis.md) |
| 有效性与位模式约束 | UCG Active Discussion | [`active_discussion/validity.md#L10`](https://github.com/rust-lang/unsafe-code-guidelines/blob/master/active_discussion/validity.md#L10) | [10_safe_unsafe_comprehensive_analysis.md](10_safe_unsafe_comprehensive_analysis.md) |

---

## 六、RFCs {#六rfcs}

> 注：Rust RFC 仓库中不存在编号 `1858` 的已接受 RFC，因此以下索引使用相邻关键 RFC `1857`（stabilize-drop-order）作为替代，并保留 `2094`、`2394`、`2580`、`3516`。

| 概念 | 权威来源 | 行号锚点链接 | 对应项目文档 |
|------|----------|--------------|--------------|
| Drop 顺序稳定化 | RFC 1857 | [`text/1857-stabilize-drop-order.md#L6`](https://github.com/rust-lang/rfcs/blob/master/text/1857-stabilize-drop-order.md#L6) | [10_version_evolution_alignment.md](10_version_evolution_alignment.md) |
| Drop 顺序详细设计 | RFC 1857 | [`text/1857-stabilize-drop-order.md#L53`](https://github.com/rust-lang/rfcs/blob/master/text/1857-stabilize-drop-order.md#L53) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) |
| 非词法生命周期（NLL） | RFC 2094 | [`text/2094-nll.md#L6`](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md#L6) | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) |
| NLL 动机：生命周期问题案例 | RFC 2094 | [`text/2094-nll.md#L19`](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md#L19) | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) |
| `async`/`await` 语法 | RFC 2394 | [`text/2394-async_await.md#L8`](https://github.com/rust-lang/rfcs/blob/master/text/2394-async_await.md#L8) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) |
| `async` 块与 `await!` 展开 | RFC 2394 | [`text/2394-async_await.md#L60`](https://github.com/rust-lang/rfcs/blob/master/text/2394-async_await.md#L60) | [formal_methods/10_pin_self_referential.md](formal_methods/10_pin_self_referential.md) |
| 指针元数据与 DST | RFC 2580 | [`text/2580-ptr-meta.md#L6`](https://github.com/rust-lang/rfcs/blob/master/text/2580-ptr-meta.md#L6) | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) |
| `Pointee` trait 定义 | RFC 2580 | [`text/2580-ptr-meta.md#L20`](https://github.com/rust-lang/rfcs/blob/master/text/2580-ptr-meta.md#L20) | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) |
| 公共/私有依赖 | RFC 3516 | [`text/3516-public-private-dependencies.md#L8`](https://github.com/rust-lang/rfcs/blob/master/text/3516-public-private-dependencies.md#L8) | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) |
| 依赖可见性与解析器 | RFC 3516 | [`text/3516-public-private-dependencies.md#L168`](https://github.com/rust-lang/rfcs/blob/master/text/3516-public-private-dependencies.md#L168) | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) |

---

## 七、未覆盖缺口 {#七未覆盖缺口}

1. **Book 后续章节**：ch12/ch13/ch17/ch18/ch19/ch20 等章节的代码清单尚未逐行锚定。
2. **Reference 深层章节**：items、types、expressions 子目录下的具体语法条目尚未逐条建立行号锚点。
3. **Rustonomicon 高级主题**：子类型、生命周期、FFI、未初始化内存等章节的行号锚点待补。
4. **RFC 编号 1858**：Rust RFC 仓库中无此编号，已用 RFC 1857 替代；后续若该编号被分配，需更新。
5. **UCG 正式 reference**：`reference/src/` 下正在迁移的正式条目（如 `validity/` 子目录）待跟进。
6. **自动化行号校验**：当前行号为人工基于当前分支抓取，需引入脚本定期校验偏移。

---

## 相关概念 {#相关概念}

- [10_authoritative_source_alignment_network.md](10_authoritative_source_alignment_network.md) — 权威来源对齐网络总入口
- [10_knowledge_graph_index.md](10_knowledge_graph_index.md) — 知识图谱索引（含本文档作为行号锚点依据）
- [10_rust_book_alignment.md](10_rust_book_alignment.md) — Rust Book 逐章对标映射
- [10_rust_reference_alignment.md](10_rust_reference_alignment.md) — Rust Reference 对齐
- [10_rustonomicon_alignment.md](10_rustonomicon_alignment.md) — Rustonomicon 对齐
- [10_unsafe_code_guidelines_alignment.md](10_unsafe_code_guidelines_alignment.md) — Unsafe Code Guidelines 对齐
- [10_rfc_alignment_index.md](10_rfc_alignment_index.md) — RFC 对齐索引
- [10_authoritative_source_version_tracking.md](10_authoritative_source_version_tracking.md) — 权威来源版本跟踪

## 社区权威参考 {#社区权威参考}

- [This Week in Rust](https://this-week-in-rust.org/)
- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [Rust 中文社区](https://rustcc.cn/)

> **来源: [RustBelt: Securing the Foundations of the Rust Programming Language](https://plv.mpi-sws.org/rustbelt/popl18/)**
> **来源: [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)**
