# Unsafe Code Guidelines 对齐矩阵

> **概念族**: 权威来源对齐 / Unsafe Code Guidelines
> **内容分级**: [核心级]
> **层级**: L0-L6
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录

- [Unsafe Code Guidelines 对齐矩阵](#unsafe-code-guidelines-对齐矩阵)
  - [目录](#目录)
  - [一、对齐说明](#一对齐说明)
  - [二、内存模型](#二内存模型)
  - [三、所有权与借用](#三所有权与借用)
  - [四、类型与布局](#四类型与布局)
  - [五、并发](#五并发)
  - [六、FFI](#六ffi)
  - [七、常见 unsafe 模式](#七常见-unsafe-模式)
  - [八、未覆盖缺口](#八未覆盖缺口)
  - [相关概念](#相关概念)
  - [学术权威参考](#学术权威参考)

---

## 一、对齐说明

[Unsafe Code Guidelines (UCG)](https://rust-lang.github.io/unsafe-code-guidelines/) 是 Rust 社区正在编写的非官方但权威的 unsafe 代码指南。本文档将项目中的 unsafe 反例、边界案例与 UCG 的议题和结论建立映射。

---

## 二、内存模型

| UCG 主题 | 项目文档 | 状态 | 备注 |
|-----------|----------|------|------|
| [Stacked Borrows](https://rust-lang.github.io/unsafe-code-guidelines/stacked_borrows.html) | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | ✅ | 原始别名模型 |
| [Tree Borrows](https://rust-lang.github.io/unsafe-code-guidelines/tree_borrows.html) | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | ✅ | 改进别名模型 |
| [What is UB?](https://rust-lang.github.io/unsafe-code-guidelines/reference/undefined-behavior.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) | ✅ | UB 边界 |

---

## 三、所有权与借用

| UCG 主题 | 项目文档 | 状态 | 备注 |
|-----------|----------|------|------|
| [References](https://rust-lang.github.io/unsafe-code-guidelines/reference/references.html) | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §4 | ✅ | 悬垂引用 |
| [Self-referential structs](https://rust-lang.github.io/unsafe-code-guidelines/reference/types/struct.html#self-referential-structs) | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §5 | ✅ | 自引用类型 |

---

## 四、类型与布局

| UCG 主题 | 项目文档 | 状态 | 备注 |
|-----------|----------|------|------|
| [Type Layout](https://rust-lang.github.io/unsafe-code-guidelines/layout.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §4 | ✅ | 对齐、类型双关 |
| [Uninitialized Memory](https://rust-lang.github.io/unsafe-code-guidelines/reference/what-is-ub.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §1-§2 | ✅ | 未初始化内存 |
| [Transmute](https://rust-lang.github.io/unsafe-code-guidelines/reference/types/union.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §7 | ✅ | 类型转换 |

---

## 五、并发

| UCG 主题 | 项目文档 | 状态 | 备注 |
|-----------|----------|------|------|
| [Send/Sync](https://rust-lang.github.io/unsafe-code-guidelines/reference/send-and-sync.html) | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) | ✅ | 并发安全 |
| [Data Races](https://rust-lang.github.io/unsafe-code-guidelines/reference/undefined-behavior.html#data-races) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §3 | ✅ | 数据竞争 |

---

## 六、FFI

| UCG 主题 | 项目文档 | 状态 | 备注 |
|-----------|----------|------|------|
| [FFI](https://rust-lang.github.io/unsafe-code-guidelines/reference/ffi.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §6 | ✅ | 内存协议 |
| [Validity Invariants](https://rust-lang.github.io/unsafe-code-guidelines/reference/validity-invariants.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §7 | ✅ | 类型合法值 |

---

## 七、常见 unsafe 模式

| 模式 | 项目反例 | UCG 参考 |
|------|----------|----------|
| 悬空裸指针 | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §1 | [References](https://rust-lang.github.io/unsafe-code-guidelines/reference/references.html) |
| 越界访问 | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §2 | [What is UB?](https://rust-lang.github.io/unsafe-code-guidelines/reference/undefined-behavior.html) |
| 数据竞争 | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §3 | [Data Races](https://rust-lang.github.io/unsafe-code-guidelines/reference/undefined-behavior.html#data-races) |
| 类型双关 | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §4 | [Type Layout](https://rust-lang.github.io/unsafe-code-guidelines/layout.html) |
| 虚假 Send/Sync | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §5 | [Send/Sync](https://rust-lang.github.io/unsafe-code-guidelines/reference/send-and-sync.html) |
| FFI use-after-free | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §6 | [FFI](https://rust-lang.github.io/unsafe-code-guidelines/reference/ffi.html) |
| transmute 误用 | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §7 | [Validity Invariants](https://rust-lang.github.io/unsafe-code-guidelines/reference/validity-invariants.html) |

---

## 八、未覆盖缺口

1. UCG 中关于 `repr(C)`、`repr(transparent)` 的详细布局规则可进一步展开。
2. `MaybeUninit` 的具体使用模式与 UCG 结论可补充示例。
3. UCG 仍在演进中，需持续跟踪其结论变化。

> **权威来源**: [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)

## 相关概念

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [Rustonomicon 对齐](10_rustonomicon_alignment.md)
- [Unsafe 与 FFI 反例](formal_methods/60_unsafe_counterexamples.md)
- [知识图谱索引](10_knowledge_graph_index.md)

---

## 学术权威参考

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)
## 社区权威参考

- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [This Week in Rust](https://this-week-in-rust.org/)
