# Rustonomicon 对齐矩阵 {#rustonomicon-对齐矩阵}

> **EN**: Rustonomicon Alignment
> **Summary**: Rustonomicon 对齐矩阵 Rustonomicon Alignment.
> **概念族**: 权威来源对齐 / Rustonomicon
> **内容分级**: [核心级]
> **层级**: L0-L6
> **Bloom 层级**: L5-L6
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [Rustonomicon 对齐矩阵 {#rustonomicon-对齐矩阵}](#rustonomicon-对齐矩阵-rustonomicon-对齐矩阵)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、所有权（Ownership）与借用（Borrowing） {#二所有权与借用}](#二所有权与借用-二所有权与借用)
  - [三、类型系统（Type System）与布局 {#三类型系统与布局}](#三类型系统与布局-三类型系统与布局)
  - [四、并发安全（Concurrency Safety） {#四并发安全}](#四并发安全-四并发安全)
  - [五、未初始化内存 {#五未初始化内存}](#五未初始化内存-五未初始化内存)
  - [六、FFI {#六ffi}](#六ffi-六ffi)
  - [七、实现相关机制 {#七实现相关机制}](#七实现相关机制-七实现相关机制)
  - [八、差异与注意点 {#八差异与注意点}](#八差异与注意点-八差异与注意点)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、对齐说明 {#一对齐说明}

本文档将 `docs/12_research_notes/` 中关于 unsafe、内存布局、生命周期（Lifetimes）、并发安全的内容与 [Rustonomicon](https://doc.rust-lang.org/nomicon/) 建立映射。

---

## 二、所有权与借用 {#二所有权与借用}

| Rustonomicon 章节 | 项目文档 | 状态 | 备注 |
|-------------------|----------|------|------|
| [Ownership](https://doc.rust-lang.org/nomicon/ownership.html) | [../02_formal_methods/09_ownership_model.md](../02_formal_methods/09_ownership_model.md) | ✅ | 所有权三规则 |
| [References](https://doc.rust-lang.org/nomicon/references.html) | [../02_formal_methods/03_borrow_checker_proof.md](../02_formal_methods/03_borrow_checker_proof.md) | ✅ | 引用（Reference）约束 |
| [Lifetimes](https://doc.rust-lang.org/nomicon/lifetimes.html) | [../05_type_theory/03_lifetime_formalization.md](../05_type_theory/03_lifetime_formalization.md) | ✅ | 生命周期子类型 |
| [Lifetime Elision](https://doc.rust-lang.org/nomicon/lifetime-elision.html) | [../05_type_theory/03_lifetime_formalization.md](../05_type_theory/03_lifetime_formalization.md) | ✅ | 省略规则 |

---

## 三、类型系统与布局 {#三类型系统与布局}

| Rustonomicon 章节 | 项目文档 | 状态 | 备注 |
|-------------------|----------|------|------|
| [Type Layout](https://doc.rust-lang.org/nomicon/data.html) | [../02_formal_methods/18_unsafe_counterexamples.md](../02_formal_methods/18_unsafe_counterexamples.md) §4 | ✅ | 类型双关、对齐 |
| [Destructors](https://doc.rust-lang.org/nomicon/destructors.html) | [../05_type_theory/07_type_system_counterexamples.md](../05_type_theory/07_type_system_counterexamples.md) §7 | ✅ | Copy/Drop 互斥 |
| [Transmutes](https://doc.rust-lang.org/nomicon/transmutes.html) | [../02_formal_methods/18_unsafe_counterexamples.md](../02_formal_methods/18_unsafe_counterexamples.md) §7 | ✅ | `transmute` 边界 |

---

## 四、并发安全 {#四并发安全}

| Rustonomicon 章节 | 项目文档 | 状态 | 备注 |
|-------------------|----------|------|------|
| [Send and Sync](https://doc.rust-lang.org/nomicon/send-and-sync.html) | [../02_formal_methods/12_send_sync_formalization.md](../02_formal_methods/12_send_sync_formalization.md) | ✅ | Send/Sync 形式化 |
| [Atomics](https://doc.rust-lang.org/nomicon/atomics.html) | [../02_formal_methods/16_concurrency_async_counterexamples.md](../02_formal_methods/16_concurrency_async_counterexamples.md) §3 | 🔄 | 原子排序待专门展开 |

---

## 五、未初始化内存 {#五未初始化内存}

| Rustonomicon 章节 | 项目文档 | 状态 | 备注 |
|-------------------|----------|------|------|
| [Uninitialized Memory](https://doc.rust-lang.org/nomicon/uninitialized.html) | [../02_formal_methods/18_unsafe_counterexamples.md](../02_formal_methods/18_unsafe_counterexamples.md) §1-§2 | ✅ | 悬空/越界指针 |
| [Unchecked](https://doc.rust-lang.org/nomicon/unchecked-uninit.html) | [../02_formal_methods/18_unsafe_counterexamples.md](../02_formal_methods/18_unsafe_counterexamples.md) §2 | 🔄 | `MaybeUninit` 使用场景 |

---

## 六、FFI {#六ffi}

| Rustonomicon 章节 | 项目文档 | 状态 | 备注 |
|-------------------|----------|------|------|
| [FFI](https://doc.rust-lang.org/nomicon/ffi.html) | [../02_formal_methods/18_unsafe_counterexamples.md](../02_formal_methods/18_unsafe_counterexamples.md) §6 | ✅ | FFI 内存协议 |
| [Exception Safety](https://doc.rust-lang.org/nomicon/exception-safety.html) | [../02_formal_methods/18_unsafe_counterexamples.md](../02_formal_methods/18_unsafe_counterexamples.md) §5 | 🔄 | panic 安全边界 |

---

## 七、实现相关机制 {#七实现相关机制}

| Rustonomicon 章节 | 项目文档 | 状态 | 备注 |
|-------------------|----------|------|------|
| [Subtyping and Variance](https://doc.rust-lang.org/nomicon/subtyping.html) | [../05_type_theory/06_variance_theory.md](../05_type_theory/06_variance_theory.md) | ✅ | 型变理论 |
| [Coercions](https://doc.rust-lang.org/nomicon/coercions.html) | [../05_type_theory/05_type_system_foundations.md](../05_type_theory/05_type_system_foundations.md) | 🔄 | 类型强制转换 |

---

## 八、差异与注意点 {#八差异与注意点}

1. Rustonomicon 强调 **UB 的边界**，项目反例文件已按此组织。
2. 对于 `MaybeUninit`、原子排序等高级主题，可在后续补充专门示例 crate。
3. Rust 1.96+ 中 `unsafe_op_in_unsafe_fn` 默认启用，已反映在 [../03_formal_proofs/33_version_evolution_counterexamples.md](../03_formal_proofs/33_version_evolution_counterexamples.md)。

> **权威来源**: [Rustonomicon](https://doc.rust-lang.org/nomicon/)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [Rust Reference 对齐](34_rust_reference_alignment.md)
- [Unsafe 与 FFI 反例](../02_formal_methods/18_unsafe_counterexamples.md)
- [知识图谱索引](../06_concept_models/13_knowledge_graph_index.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneasverif.github.io/)

## 社区权威参考 {#社区权威参考}

- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [This Week in Rust](https://this-week-in-rust.org/)
