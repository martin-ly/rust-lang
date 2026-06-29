# 安全与 unsafe 权威来源对齐矩阵

> **概念族**: 权威来源对齐 / 安全 / unsafe
> **内容分级**: [核心级]
> **层级**: L0-L6
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录

- [安全与 unsafe 权威来源对齐矩阵](#安全与-unsafe-权威来源对齐矩阵)
  - [目录](#目录)
  - [一、对齐说明](#一对齐说明)
  - [二、P0 官方权威](#二p0-官方权威)
  - [三、P1 学术权威](#三p1-学术权威)
  - [四、P2 社区与行业权威](#四p2-社区与行业权威)
  - [五、安全边界映射](#五安全边界映射)
  - [六、与项目文档的映射](#六与项目文档的映射)
  - [七、未覆盖缺口](#七未覆盖缺口)
  - [相关概念](#相关概念)

---

## 一、对齐说明

本文档将 `docs/research_notes/` 中关于 Rust 安全保证、unsafe 边界、内存安全、并发安全、FFI 安全的内容与 P0/P1/P2 权威来源建立映射，形成跨层级的安全权威来源网络。

---

## 二、P0 官方权威

| 权威来源 | 链接 | 项目文档 | 覆盖主题 |
|----------|------|----------|----------|
| The Rust Programming Language — Unsafe | [Ch 19](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html) | [10_rust_book_alignment.md](10_rust_book_alignment.md) | unsafe 块、裸指针、extern、static mut |
| Rust Reference — Unsafe | [Unsafe Operations](https://doc.rust-lang.org/reference/unsafe-op-in-unsafe-fn.html) | [10_rust_reference_alignment.md](10_rust_reference_alignment.md) | unsafe 操作语义 |
| Rustonomicon | <https://doc.rust-lang.org/nomicon/> | [10_rustonomicon_alignment.md](10_rustonomicon_alignment.md) | 所有权、类型布局、Send/Sync、FFI |
| Unsafe Code Guidelines | <https://rust-lang.github.io/unsafe-code-guidelines/> | [10_unsafe_code_guidelines_alignment.md](10_unsafe_code_guidelines_alignment.md) | UB、内存模型、类型合法值 |
| Rust Error Codes | [Error Index](https://doc.rust-lang.org/error_codes/error-index.html) | [10_rustc_errors_alignment.md](10_rustc_errors_alignment.md) | E0xxx unsafe/借用错误 |

---

## 三、P1 学术权威

| 权威来源 | 机构 | 项目文档 | 覆盖主题 |
|----------|------|----------|----------|
| [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/) | MPI-SWS | [10_rustbelt_alignment.md](10_rustbelt_alignment.md) | 所有权、借用、unsafe 抽象安全 |
| [Stacked Borrows](https://plv.mpi-sws.org/rustbos/) | MPI-SWS | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | 别名模型、UB |
| [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html) | ETH Zürich | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | 改进别名模型 |
| [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3) | 多机构 | [10_rustsem_semantics.md](10_rustsem_semantics.md) | 操作语义、unsafe 行为 |
| [Aeneas](https://aeneas-verification.github.io/) | EPFL | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) | 可验证子集、unsafe 边界 |
| [Kani](https://model-checking.github.io/kani/) | AWS | [10_verification_tools_practical_alignment.md](10_verification_tools_practical_alignment.md) | 模型检查、unsafe 断言 |

---

## 四、P2 社区与行业权威

| 权威来源 | 类型 | 项目文档 | 覆盖主题 |
|----------|------|----------|----------|
| [Rust Secured](https://rust-secure-code.github.io/) | 安全工作组 | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) | 安全编码、供应链 |
| [Cargo Audit](https://docs.rs/cargo-audit/) | 安全工具 | [10_cargo_book_alignment.md](10_cargo_book_alignment.md) | 依赖漏洞扫描 |
| [Rust Fuzzing](https://rust-fuzz.github.io/book/) | 模糊测试 | [experiments/10_concurrency_performance.md](experiments/10_concurrency_performance.md) | fuzz、cargo-fuzz |
| [Miri](https://github.com/rust-lang/miri) | UB 检测器 | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) | 运行时 UB 检测 |

---

## 五、安全边界映射

| 安全边界 | 官方来源 | 学术支撑 | 项目反例 |
|----------|----------|----------|----------|
| 悬垂/越界指针 | [What is UB?](https://rust-lang.github.io/unsafe-code-guidelines/reference/undefined-behavior.html) | Stacked/Tree Borrows | [60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §1-§2 |
| 数据竞争 | [Data Races](https://rust-lang.github.io/unsafe-code-guidelines/reference/undefined-behavior.html#data-races) | RustBelt | [60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §3 |
| 类型双关 | [Type Layout](https://rust-lang.github.io/unsafe-code-guidelines/layout.html) | RustSEM | [60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §4 |
| 虚假 Send/Sync | [Send/Sync](https://rust-lang.github.io/unsafe-code-guidelines/reference/send-and-sync.html) | RustBelt | [60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §5 |
| FFI 协议违规 | [FFI](https://rust-lang.github.io/unsafe-code-guidelines/reference/ffi.html) | — | [60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §6 |
| transmute 误用 | [Validity Invariants](https://rust-lang.github.io/unsafe-code-guidelines/reference/validity-invariants.html) | RustSEM | [60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §7 |

---

## 六、与项目文档的映射

| 项目文档 | 覆盖安全主题 | 权威来源 |
|----------|--------------|----------|
| [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) | unsafe 反例边界 | UCG、Rustonomicon |
| [10_safe_unsafe_comprehensive_analysis.md](10_safe_unsafe_comprehensive_analysis.md) | safe/unsafe 综合 | Rust Book、Rustonomicon |
| [10_unsafe_code_guidelines_alignment.md](10_unsafe_code_guidelines_alignment.md) | UCG 对齐 | UCG |
| [10_rustonomicon_alignment.md](10_rustonomicon_alignment.md) | Rustonomicon 对齐 | Rustonomicon |
| [10_rustbelt_alignment.md](10_rustbelt_alignment.md) | 形式化安全 | RustBelt |
| [10_verification_tools_practical_alignment.md](10_verification_tools_practical_alignment.md) | 验证工具实战 | Kani、Aeneas、Prusti |

---

## 七、未覆盖缺口

1. `unsafe_op_in_unsafe_fn` 默认启用后的反例可细化。
2. Miri 与 Kani 在项目示例中的集成步骤可补充。
3. 供应链安全（cargo-audit、SBOM、Sigstore）可扩展。

> **权威来源**: [Rust Book Ch 19](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html) | [Rustonomicon](https://doc.rust-lang.org/nomicon/) | [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) | [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/) | [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html) | [Miri](https://github.com/rust-lang/miri) | [Kani](https://model-checking.github.io/kani/)

## 相关概念

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [Unsafe Code Guidelines 对齐](10_unsafe_code_guidelines_alignment.md)
- [Rustonomicon 对齐](10_rustonomicon_alignment.md)
- [RustBelt 对齐](10_rustbelt_alignment.md)
- [验证工具实战对齐](10_verification_tools_practical_alignment.md)
- [知识图谱索引](10_knowledge_graph_index.md)
