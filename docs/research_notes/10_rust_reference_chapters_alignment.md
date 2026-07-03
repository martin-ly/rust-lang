# Rust Reference 分章节深度对齐 {#rust-reference-分章节深度对齐}

> **EN**: Rust Reference Chapters Alignment
> **Summary**: Rust Reference 分章节深度对齐 Rust Reference Chapters Alignment.
> **概念族**: 权威来源对齐 / Rust Reference
> **内容分级**: [核心级]
> **层级**: L0-L4
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [Rust Reference 分章节深度对齐 {#rust-reference-分章节深度对齐}](#rust-reference-分章节深度对齐-rust-reference-分章节深度对齐)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、前言与介绍 {#二前言与介绍}](#二前言与介绍-二前言与介绍)
  - [三、词法结构 {#三词法结构}](#三词法结构-三词法结构)
  - [四、类型系统 {#四类型系统}](#四类型系统-四类型系统)
  - [五、表达式 {#五表达式}](#五表达式-五表达式)
  - [六、Items {#六items}](#六items-六items)
  - [七、Attributes {#七attributes}](#七attributes-七attributes)
  - [八、Crates 与 Source Files {#八crates-与-source-files}](#八crates-与-source-files-八crates-与-source-files)
  - [九、Unsafe Rust {#九unsafe-rust}](#九unsafe-rust-九unsafe-rust)
  - [十、链接与 ABI {#十链接与-abi}](#十链接与-abi-十链接与-abi)
  - [十一、未覆盖缺口 {#十一未覆盖缺口}](#十一未覆盖缺口-十一未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、对齐说明 {#一对齐说明}

本文档是 [Rust Reference](https://doc.rust-lang.org/reference/) 的 **分章节深度对齐**，将 Reference 的每个主要部分与 `docs/research_notes/` 中的具体概念、机制、反例一一映射。相比 [10_rust_reference_alignment.md](10_rust_reference_alignment.md) 的概览式矩阵，本文档提供更细的粒度。

---

## 二、前言与介绍 {#二前言与介绍}

| Reference 章节 | 项目文档 | 对齐点 |
|----------------|----------|--------|
| [Introduction](https://doc.rust-lang.org/reference/introduction.html) | [10_knowledge_graph_index.md](10_knowledge_graph_index.md) | 知识体系总览 |
| [Notation](https://doc.rust-lang.org/reference/notation.html) | [10_formal_language_and_proofs.md](10_formal_language_and_proofs.md) | 形式化符号 |

---

## 三、词法结构 {#三词法结构}

| Reference 章节 | 项目文档 | 对齐点 |
|----------------|----------|--------|
| [Input Format](https://doc.rust-lang.org/reference/input-format.html) | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | 源文件编码 |
| [Keywords](https://doc.rust-lang.org/reference/keywords.html) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §3 | `gen` 关键字保留 |
| [Identifiers](https://doc.rust-lang.org/reference/identifiers.html) | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | 标识符规则 |
| [Comments](https://doc.rust-lang.org/reference/comments.html) | [10_code_doc_formal_mapping.md](10_code_doc_formal_mapping.md) | 文档注释 |
| [Tokens](https://doc.rust-lang.org/reference/tokens.html) | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | 字面量、运算符 |

---

## 四、类型系统 {#四类型系统}

| Reference 章节 | 项目文档 | 对齐点 |
|----------------|----------|--------|
| [Types](https://doc.rust-lang.org/reference/types.html) | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | 标量、复合、函数、trait 对象 |
| [Trait Objects](https://doc.rust-lang.org/reference/types/trait-object.html) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §3 | `dyn Trait` 大小不固定 |
| [Generics](https://doc.rust-lang.org/reference/items/generics.html) | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | 泛型参数、where 子句 |
| [Lifetimes](https://doc.rust-lang.org/reference/lifetime-elision.html) | [type_theory/10_lifetime_formalization.md](type_theory/10_lifetime_formalization.md) | 生命周期参数、省略 |
| [Subtyping and Variance](https://doc.rust-lang.org/reference/subtyping-and-variance.html) | [type_theory/10_variance_theory.md](type_theory/10_variance_theory.md) | 型变规则 |
| [Type Coercions](https://doc.rust-lang.org/reference/type-coercions.html) | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | 自动类型转换 |

---

## 五、表达式 {#五表达式}

| Reference 章节 | 项目文档 | 对齐点 |
|----------------|----------|--------|
| [Expressions](https://doc.rust-lang.org/reference/expressions.html) | [crates/c03_control_fn/](../../crates/c03_control_fn/README.md) | 表达式求值 |
| [Literal Expressions](https://doc.rust-lang.org/reference/expressions/literal-expr.html) | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | 字面量 |
| [Block Expressions](https://doc.rust-lang.org/reference/expressions/block-expr.html) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | async 块、tail expr drop order |
| [If / Match](https://doc.rust-lang.org/reference/expressions/if-expr.html) | [crates/c03_control_fn/](../../crates/c03_control_fn/README.md) | 控制流 |
| [Call Expressions](https://doc.rust-lang.org/reference/expressions/call-expr.html) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | async fn 调用 |
| [Closure Expressions](https://doc.rust-lang.org/reference/expressions/closure-expr.html) | [crates/c03_control_fn/](../../crates/c03_control_fn/README.md) | 闭包 |

---

## 六、Items {#六items}

| Reference 章节 | 项目文档 | 对齐点 |
|----------------|----------|--------|
| [Items](https://doc.rust-lang.org/reference/items.html) | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) | Item 种类 |
| [Modules](https://doc.rust-lang.org/reference/items/modules.html) | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) | `mod` 声明 |
| [Use Declarations](https://doc.rust-lang.org/reference/items/use-declarations.html) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §4 | `use` 路径 |
| [Functions](https://doc.rust-lang.org/reference/items/functions.html) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | async fn、unsafe fn |
| [Traits](https://doc.rust-lang.org/reference/items/traits.html) | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | trait 定义 |
| [Implementations](https://doc.rust-lang.org/reference/items/implementations.html) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §5 | Orphan 规则 |
| [External Blocks](https://doc.rust-lang.org/reference/items/external-blocks.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §6 | FFI |

---

## 七、Attributes {#七attributes}

| Reference 章节 | 项目文档 | 对齐点 |
|----------------|----------|--------|
| [Attributes](https://doc.rust-lang.org/reference/attributes.html) | [formal_modules/20_linkage_and_symbols.md](formal_modules/20_linkage_and_symbols.md) | `#[no_mangle]`、`#[repr]` |
| [Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §5 | `cfg` / features |
| [Derive](https://doc.rust-lang.org/reference/attributes/derive.html) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §7 | Copy/Derive |

---

## 八、Crates 与 Source Files {#八crates-与-source-files}

| Reference 章节 | 项目文档 | 对齐点 |
|----------------|----------|--------|
| [Crates and Source Files](https://doc.rust-lang.org/reference/crates-and-source-files.html) | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) | crate 根、模块文件 |
| [Linkage](https://doc.rust-lang.org/reference/linkage.html) | [formal_modules/20_linkage_and_symbols.md](formal_modules/20_linkage_and_symbols.md) | crate-type、符号 |

---

## 九、Unsafe Rust {#九unsafe-rust}

| Reference 章节 | 项目文档 | 对齐点 |
|----------------|----------|--------|
| [Unsafe Blocks](https://doc.rust-lang.org/reference/unsafe-blocks.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) | unsafe 操作边界 |
| [Unsafe Functions](https://doc.rust-lang.org/reference/items/functions.html#unsafe-functions) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §2 | 2024 lint 变化 |
| [Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) | UB 列表 |

---

## 十、链接与 ABI {#十链接与-abi}

| Reference 章节 | 项目文档 | 对齐点 |
|----------------|----------|--------|
| [ABI](https://doc.rust-lang.org/reference/items/external-blocks.html#abi) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §6 | `extern "C"` |
| [No Mangle](https://doc.rust-lang.org/reference/abi.html#the-no_mangle-attribute) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §8 | 符号冲突 |

---

## 十一、未覆盖缺口 {#十一未覆盖缺口}

1. Reference 中 `const` 求值、模式匹配、宏的详细章节可进一步拆分。
2. 每个对齐点可细化到具体文件行号。
3. 可随 Rust 1.97+ 发布持续更新本章节目录。

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [Rust Reference 对齐矩阵](10_rust_reference_alignment.md)
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
