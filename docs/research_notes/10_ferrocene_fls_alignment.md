# Ferrocene Language Specification 对齐矩阵 {#ferrocene-language-specification-对齐矩阵}

> **EN**: Ferrocene Fls Alignment
> **Summary**: Ferrocene Language Specification 对齐矩阵 Ferrocene Fls Alignment.
> **概念族**: 权威来源对齐 / Ferrocene FLS
> **内容分级**: [核心级]
> **层级**: L0-L4
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [Ferrocene Language Specification 对齐矩阵 {#ferrocene-language-specification-对齐矩阵}](#ferrocene-language-specification-对齐矩阵-ferrocene-language-specification-对齐矩阵)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、词法与语法 {#二词法与语法}](#二词法与语法-二词法与语法)
  - [三、类型系统 {#三类型系统}](#三类型系统-三类型系统)
  - [四、所有权与借用 {#四所有权与借用}](#四所有权与借用-四所有权与借用)
  - [五、并发与 unsafe {#五并发与-unsafe}](#五并发与-unsafe-五并发与-unsafe)
  - [六、Items 与 Modules {#六items-与-modules}](#六items-与-modules-六items-与-modules)
  - [七、形式化标注 {#七形式化标注}](#七形式化标注-七形式化标注)
  - [八、未覆盖缺口 {#八未覆盖缺口}](#八未覆盖缺口-八未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、对齐说明 {#一对齐说明}

[Ferrocene Language Specification (FLS)](https://spec.ferrocene.dev/) 是 Rust 的安全关键子集形式化规范，被用于 DO-178C / ISO 26262 等认证场景。本文档将 `docs/research_notes/` 中的概念与 FLS 章节建立映射，突出项目文档在可认证语义层面的覆盖度。

---

## 二、词法与语法 {#二词法与语法}

| FLS 章节 | 项目文档 | 状态 | 备注 |
|----------|----------|------|------|
| [Lexical Elements](https://spec.ferrocene.dev/lexical-elements.html) | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | 🔄 | 基础词法说明 |
| [Syntax](https://spec.ferrocene.dev/syntax.html) | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | 🔄 | 表达式级语法在所有权模型中示例 |

---

## 三、类型系统 {#三类型系统}

| FLS 章节 | 项目文档 | 状态 | 备注 |
|----------|----------|------|------|
| [Types](https://spec.ferrocene.dev/types.html) | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | ✅ | 标量、复合、trait 对象 |
| [Generics](https://spec.ferrocene.dev/generics.html) | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | ✅ | 泛型参数、约束 |
| [Traits](https://spec.ferrocene.dev/traits.html) | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | ✅ | trait 定义、实现、关联类型 |
| [Subtyping](https://spec.ferrocene.dev/subtyping.html) | [type_theory/10_variance_theory.md](type_theory/10_variance_theory.md) | ✅ | 子类型与型变 |

---

## 四、所有权与借用 {#四所有权与借用}

| FLS 章节 | 项目文档 | 状态 | 备注 |
|----------|----------|------|------|
| [Ownership](https://spec.ferrocene.dev/ownership.html) | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | ✅ | 所有权三规则 |
| [Borrowing](https://spec.ferrocene.dev/borrowing.html) | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | ✅ | 借用检查器 |
| [Lifetimes](https://spec.ferrocene.dev/lifetimes.html) | [type_theory/10_lifetime_formalization.md](type_theory/10_lifetime_formalization.md) | ✅ | 生命周期参数与约束 |

---

## 五、并发与 unsafe {#五并发与-unsafe}

| FLS 章节 | 项目文档 | 状态 | 备注 |
|----------|----------|------|------|
| [Concurrency](https://spec.ferrocene.dev/concurrency.html) | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) | ✅ | Send/Sync |
| [Unsafe Rust](https://spec.ferrocene.dev/unsafe-rust.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) | ✅ | unsafe 操作边界 |
| [Foreign Function Interface](https://spec.ferrocene.dev/ffi.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §6 | ✅ | FFI 内存协议 |

---

## 六、Items 与 Modules {#六items-与-modules}

| FLS 章节 | 项目文档 | 状态 | 备注 |
|----------|----------|------|------|
| [Items](https://spec.ferrocene.dev/items.html) | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) | ✅ | module、function、struct、enum 等 |
| [Modules and Crates](https://spec.ferrocene.dev/modules-and-crates.html) | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) | ✅ | crate 结构与可见性 |
| [Linkage](https://spec.ferrocene.dev/linkage.html) | [formal_modules/20_linkage_and_symbols.md](formal_modules/20_linkage_and_symbols.md) | ✅ | crate-type、符号可见性 |

---

## 七、形式化标注 {#七形式化标注}

| FLS 章节 | 项目文档 | 状态 | 备注 |
|----------|----------|------|------|
| [Notation](https://spec.ferrocene.dev/notation.html) | [10_formal_language_and_proofs.md](10_formal_language_and_proofs.md) | ✅ | 形式化符号与推理规则 |
| [Glossary](https://spec.ferrocene.dev/glossary.html) | [10_glossary.md](10_glossary.md) | ✅ | 术语表 |

---

## 八、未覆盖缺口 {#八未覆盖缺口}

1. FLS 对 `const` 求值、模式匹配的细粒度规则可进一步展开。
2. FLS 的「限制子集」与项目 unsafe/FFI 边界可建立更明确的子集映射。
3. 安全关键认证相关的可追溯性矩阵可后续补充。

> **权威来源**: [Ferrocene Language Specification](https://spec.ferrocene.dev/)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [国际形式化验证索引](10_international_formal_verification_index.md)
- [Rust Reference 对齐](10_rust_reference_alignment.md)
- [Rustonomicon 对齐](10_rustonomicon_alignment.md)
- [知识图谱索引](10_knowledge_graph_index.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)

## 社区权威参考 {#社区权威参考}

- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [This Week in Rust](https://this-week-in-rust.org/)
